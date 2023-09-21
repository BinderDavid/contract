-- | Practical typed lazy contracts.
--   Author: Olaf Chitil.
--   Version: July 2012.
--
-- Contracts describe properties of expressions (esp. functions) that are
-- checked at run-time.
-- Thus these properties are both documented and enforced.
-- Contracts are more expressive than static types.
-- If a contract is violated, then an informative exception is raised.
--
-- Example uses:
--
-- > head' = $attach head (pNotNil >-> true)
--
-- > nat :: (Integral a, Flat a) => Contract a
-- > nat = prop (>=0)
-- > fibs = $assert (list nat) (0 : 1 : zipWith (+) fibs (tail fibs))
--
-- > conjNF = $(p ’And) conjNF conjNF |> disj
-- > disj   = $(p ’Or)  disj disj |> lit
-- > lit    = $(p ’Not) atom |> atom
-- > atom   = $(p ’Atom) true
-- > clausalNF' = $attach clausalNF (conjNF & right >-> list (list lit))
--
-- See <http://www.cs.kent.ac.uk/~oc/contracts.html>
-- or Olaf Chitil: Practical Typed Lazy Contracts, ICFP 2012, ACM.
--
-- Any user module will need Template Haskell.
-- They will also need DeriveDataTypeable, if they use the deriving 
-- combinators for algebraic data types: 'p', 'pNot' or 'deriveContracts'.

{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}

module Development.Contract (
    Contract -- abstract
  , ContractFailed(..)  -- the exception raised when a contract fails
  , Partner(..)  -- partners of a contract that can be blamed
  , assert   -- $assert :: Contract a -> a -> a
  , attach   -- $attach :: a -> Contract a -> a
  , (&)      -- conjunction of two contracts
  , (|>)     -- disjunction of two contracts, trying first first
  , (>->)    -- build function contract
  , (>>->)   -- build dependent function contract, does not protect laziness
  , true     -- contract that always succeeds
  , false    -- contract that always fails
  , Flat(prop)  -- all flat types can be checked by a predicate
  , p        -- $(p 'cons) is pattern contract for the given constructor
  , pNot     -- $(pNot 'cons) is negative pattern contract 
  , deriveContracts -- $(deriveContracts ''type) 
  , dropContext -- drop context information in a contract to avoid unbound growth
  , pNil, pCons, (=:), pNotNil, pNotCons, list -- contracts for the list type
  , io          -- contract for the IO type
  , pTuple0, pTuple2, pTuple3, pTuple4  -- contracts for tuples
  , pNothing, pJust, pNotNothing, pNotJust, maybe  -- contracts for the Maybe type
  ) where

import Prelude hiding (maybe)
import Data.Char(isLetter)
import Data.Either(either)
import Data.List (intercalate)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import Data.Typeable(Typeable)  -- for the new exception
import Control.Exception(Exception, throw)  -- to add a new exception

-- | The exception raised when a contact fails.
data ContractFailed =
  ContractFailed {culprit :: Partner, loc :: Loc, explanation :: String}
  deriving (Typeable)

instance Show ContractFailed where
  show (ContractFailed culprit loc explanation) = 
    "Contract at " ++ loc_filename loc ++ ":" ++ show line ++ ":" ++ show col ++ 
    " failed at\n" ++ explanation ++ "\n" ++
    "The " ++ show culprit ++ " is to blame."
    where
    (line,col) = loc_start loc

instance Exception ContractFailed

-- | Different contract partners. 
-- For any violated contract a partner is blamed.
data Partner = Server | Client | Contract

instance Show Partner where
  show Server = "server"
  show Client = "client"
  show Contract = "contract"

type Blame = (Partner, Partner)

getCulprit :: Blame -> Partner
getCulprit = fst

contra :: Blame -> Blame
contra (p1,p2) = (p2,p1)

newClient :: Blame -> Partner -> Blame
newClient (p1,_) p2 = (p1,p2)

-- | The contract type.
newtype Contract a = 
  C (Blame -> Loc -> ExplanationB -> a -> Either (Partner,String) a)    

-- | Connect a contract with an expression.
-- The resulting expression is the same except that the contract is
-- monitored for it at runtime.
-- assert splices in code that adds the current location in the module file.
--
-- > $assert :: Contract a -> a -> a
assert :: Q Exp
assert = do 
  loc <- location
  [|monitor (Server,Client) loc id|]

-- | Same as assert with arguments swapped.
-- Useful for attaching contracts in simple variable definitions:
-- fun' = $attach fun contract
--
-- > $attach :: a -> Contract a -> a
attach :: Q Exp
attach = do
  loc <- location
  [|\x c -> monitor (Server,Client) loc id c x|]
  
-- | This instance is missing in Template Haskell; needed for quote above.
instance Lift Loc where
  lift (Loc a1 a2 a3 a4 a5) = [|Loc a1 a2 a3 a4 a5|]

-- | This assert variant does the actual job, taking information about the context.
monitor :: Blame -> Loc -> ExplanationB -> Contract a -> (a -> a)
monitor b l e (C f) x
  = either 
      (\(cul,con) -> throw (ContractFailed cul l (e ("{" ++ con ++ "}")))) 
      id
      (f b l e x)

cFail :: Blame -> String -> Either (Partner,String) a
cFail (p1,p2) err = Left (p1,err)

-- Same associativities and priorities as for the Boolean operators.
infixr 3 &
infixr 2 |>
infixr 1 >->
infixr 1 >>->

-- | Conjunction of two contracts.
(&) :: Contract a -> Contract a -> Contract a
C p1 & C p2 = C (\b l e x -> p1 b l e x >>= p2 b l e)

-- | Disjunction of contracts, given priority to first.
(|>) :: Contract a -> Contract a -> Contract a
-- C p1 |> C p2 = C (\b l e x -> p1 b l e x `mplus` c2 b l e x)
-- Either e is not a monad plus because no good definition of mzero = Left.
C p1 |> C p2 = C (\b l e x -> case p1 b l e x of
                                Left _ -> p2 b l e x
                                Right y -> Right y)

-- | Contract that always succeeds.
true :: Contract a
true = C (\b l e x -> Right x)

-- | Contract that always fails, blaming the client.
false :: Contract a
false = C (\b l e x -> cFail (contra b) "NOT false")

-- | Function contract combinator, taking contracts for pre- and post-condition.
(>->) :: Contract a -> Contract b -> Contract (a -> b)
c1 >-> c2 = 
  C (\b l e f -> Right (f `seq` 
    (monitor b l (e . \s->("(_->"++s++")")) c2 . f . 
     monitor (contra b) l (e . \s->("("++s++"->_)")) c1)))

-- | Dependent function contract combinator.
-- The post-condition also takes the function argument.
-- Warning: This combinator does /not/ protect laziness!
(>>->) :: Contract a -> (a -> Contract b) -> Contract (a -> b)
pre >>-> post = 
  C (\b l e f -> Right (f `seq` 
    \x -> let b' = contra b
              e' = e . \s->("("++s++"->_)")
          in monitor b l (e . \s->("(_->"++s++")"))
               (post (monitor (newClient b' Contract) l e' pre x)) 
               (f (monitor b' l e' pre x))))

-- | Class of all flat types, for which contract prop works.
--
-- A type is flat if its only partial value is bottom / undefined.
-- In other words: an expression of the type is either unevaluted or
-- fully evaluated, never properly partially evaluated.
class Show a => Flat a where
  prop :: (a -> Bool) -> Contract a
  prop p = C (\b l e x -> if p x then Right x else cFail b (show x))

instance Flat Int
instance Flat Integer
instance Flat Float
instance Flat Double
instance Flat Char
instance Flat Bool

-- Functions related to fail message construction

-- | Drop context information in a contract to avoid unbound context growth.
-- Can be wrapped around any context.
dropContext :: Contract a -> Contract a 
dropContext (C f) = C (\b l e x -> f b l (\s->(".."++s++"..")) x)

type ExplanationB = String -> String

-- Name of constructor, arity (>0), position within arguments (start at 1)
context :: String -> Arity -> Int -> ExplanationB
context cons a n s = "("++cons++ concatMap arg [1..a]++")"
  where
  arg :: Int -> String
  arg m = if n==m then ' ':s else " _"

contextI :: String -> Arity -> Int -> ExplanationB
contextI cons _ 1 s = "("++s++cons++"_)"
contextI cons _ 2 s = "(_"++cons++s++")"

showParen :: Bool -> String -> String
showParen True s = "("++s++")"
showParen False s = s

contextVar :: Con -> ExpQ
contextVar (InfixC _ _ _) = varE 'contextI
contextVar _              = varE 'context

-- | For a given algebraic data type 
-- declare pattern contracts for all constructors.
-- The argument must be the name of an algebraic data type.
-- E.g. $(deriveContracts \'\'Either)
deriveContracts :: Name -> Q [Dec]
deriveContracts dataTyName = do
  (TyConI (DataD _ _ _ constructors _)) <- reify dataTyName
  conNameArities <- mapM conNameArity constructors
  let conNames = map fst conNameArities
  conContracts <- mapM deriveConContract conNames
  notContracts <- mapM deriveNotContract conNames
  return (concat conContracts ++ concat notContracts)

-- For a given data constructor declare the pattern contract.
-- The pattern contract takes the same number of arguments as the data
-- constructor.
-- It should also have the same fixity, but Template Haskell cannot splice
-- any fixity declaration; so that is left to the user.
deriveConContract :: Name -> Q [Dec]
deriveConContract conName = do
  (DataConI _ conTy dataTyName _) <- reify conName
  (TyConI (DataD cxt _ _ constructors _)) <- reify dataTyName
  tyDec <- sigD pname (return (conContractType cxt conTy))
  runIO (putStrLn (pprint conTy))
  runIO (putStrLn (pprint cxt))
  runIO (putStrLn (pprint tyDec))
  def <- valD (varP pname) (normalB (p conName)) []
  return [tyDec,def]
  where
  pname = mkName (prefix : name)
  name = nameBase conName
  prefix = if isLetter (head name) then 'p' else '='


-- For a given data constructor declare the negated pattern contract
-- Don't derive it for any operator as there is no standard for naming it.
deriveNotContract :: Name -> Q [Dec]
deriveNotContract conName =
  if isLetter (head name) 
    then do
       (DataConI _ conTy dataTyName _) <- reify conName
       (TyConI (DataD cxt _ tyVars constructors _)) <- reify dataTyName
       tyDec <- sigD pname (return (notContractType cxt dataTyName tyVars))
       def <- valD (varP pname) (normalB (pNot conName)) []
       return [tyDec,def]
    else return []
  where
  name = nameBase conName
  pname = mkName ("pNot" ++ name)

-- Construct the type for a not constructor contract
notContractType :: Cxt -> Name -> [TyVarBndr] -> Type
notContractType cxt tyName tyVars =
  ForallT tyVars cxt 
    (AppT (ConT ''Contract) 
      (if null tyVars
        then (ConT tyName) 
        else AppT (ConT tyName) (foldr1 AppT (map mkTVar tyVars))))
  where
  mkTVar :: TyVarBndr -> Type
  mkTVar (PlainTV name) = VarT name
  mkTVar (KindedTV name _) = VarT name

-- Convert type of a data constructor into type of its pattern contract.
-- Apparently a bug in TH means that the context of the given data constructor
-- type is always empty; hence nasty hack using the context from the 
-- data type declaration. At least the type variables happen to fit.
conContractType :: Cxt -> Type -> Type
conContractType cxt (ForallT tyvars cxt2 ty) = 
  ForallT tyvars cxt (conContractType cxt ty)
conContractType cxt (AppT (AppT ArrowT t1) t2) = 
  AppT (AppT ArrowT (AppT (ConT ''Contract) t1)) (conContractType cxt t2) 
conContractType _ t = AppT (ConT ''Contract) t

type Arity = Int

-- Given the name of a data constructor and a list of constructors containing
-- that constructor, return its arity.
arity :: Name -> [Con] -> Arity
arity conName [] = error "arity: constructor not in list"
arity conName (InfixC _ cName _ : cs) = 
  if conName == cName then 2 else arity conName cs
arity conName (NormalC cName fields : cs) =
  if conName == cName then length fields else arity conName cs
arity conName (RecC cName fields : cs) =
  if conName == cName then length fields else arity conName cs
arity conName (ForallC _ _ _ : cs) = arity conName cs

isConName :: Name -> Con -> Bool
isConName conName (InfixC _ cName _) = conName==cName
isConName conName (NormalC cName _) = conName==cName
isConName conName (RecC cName _) = conName==cName
isConName conName (ForallC _ _ _) = False

name2Con :: Name -> [Con] -> Con
name2Con conName cons = head (filter (isConName conName) cons)

-- | Pattern contract for given constructor.
-- The argument must be the name of a data constructor.
-- E.g. 
-- $(p \'Left)
p :: Name -> ExpQ
p conName = do
  (DataConI _ conTy dataTyName fixity) <- reify conName
  (TyConI (DataD _ _ _ constructors _)) <- reify dataTyName
  let conArity = arity conName constructors
  conArgNames <- mapM (const (newName "c")) [1..conArity]
  projName <- newName "proj"
  mkPatternContract conName conArity conTy conArgNames projName constructors

-- | Negated pattern contract for a given constructor.
-- The argument must be the name of a data constructor.
-- E.g. 
-- $(pNot \'Left)
pNot :: Name -> ExpQ
pNot conName = do
  (DataConI _ conTy dataTyName _) <- reify conName
  (TyConI (DataD _ _ _ constructors _)) <- reify dataTyName
  let conArity = arity conName constructors
  projName <- newName "proj"
  let projDef = 
        funD projName 
          [clauseCon conName conArity (name2Con conName constructors), clauseO]
  letE [projDef] (appE (conE 'C) (varE projName)) 

clauseCon :: Name -> Arity -> Con -> ClauseQ
clauseCon conName arity con = do
  blameName <- newName "b"
  locName <- newName "loc"
  explName <- newName "expl"
  clause [varP blameName, varP locName, varP explName
         ,conP conName (replicate arity wildP)]
         (normalB (appsE [varE 'cFail, varE blameName, 
                          litE (stringL (faultString conName arity con))])) []

clauseO :: ClauseQ
clauseO = do
  blameName <- newName "b"
  locName <- newName "loc"
  explName <- newName "expl"
  argName <- newName "x"
  clause [varP blameName, varP locName, varP explName, varP argName]
         (normalB (appE (conE 'Right) (varE argName))) []



-- Make the code for a pattern contract.
-- Given the name of the constructor, its arity, its type, names for contract
-- arguments, a name for the projection and a list of all data constructors of the 
-- type.
mkPatternContract :: Name -> Int -> Type -> [Name] -> Name -> [Con] -> ExpQ
mkPatternContract conName conArity conTy conArgNames projName constructors =
  conExp -- sigE conExp (return (conContractType conTy))
  where
  clauses = map (mkClause conName conArgNames) constructors
  projDef = funD projName clauses
  contractExp = letE [projDef] (appE (conE 'C) (varE projName))
  conExp = if conArity == 0 then contractExp 
                            else lamE (map varP conArgNames) contractExp

faultString :: Name -> Arity -> Con -> String
faultString cName cArity (InfixC _ _ _) = "_" ++ nameBase cName ++ "_"
faultString cName cArity _ = nameBase cName ++ concat (replicate cArity " _")

conNameArity :: Con -> Q (Name,Arity)
conNameArity (InfixC _ cName _) = return (cName,2)
conNameArity (NormalC cName fields) = return (cName, length fields)
conNameArity (RecC cName vFields) = return (cName, length vFields)
conNameArity (ForallC _ _ _) = do
  report True "Cannot make contract pattern when constructor has existential type."
  return undefined

-- Make one clause of the projection function of the contract.
mkClause :: Name -> [Name] -> Con -> ClauseQ
mkClause conName conArgNames con = do
  blameName <- newName "b"
  locName <- newName "loc"
  explName <- newName "expl"
  (cName,cArity) <- conNameArity con
  cArgNames <- mapM (const (newName "x")) [1..cArity]
  let recExp :: Name -> Name -> Int -> ExpQ
      recExp conArgName cArgName i = 
        appsE [varE 'monitor, varE blameName, varE locName, appsE [varE '(.), varE explName, appsE [contextVar con, litE (stringL (nameBase conName)), litE (integerL (fromIntegral cArity)), litE (integerL (fromIntegral i))]], varE conArgName, varE cArgName]  
  let body :: ExpQ
      body = if cName == conName 
                then appE (conE 'Right) 
                       (appsE ((conE cName) : 
                         zipWith3 recExp conArgNames cArgNames [1..cArity]))
                else appsE [varE 'cFail, varE blameName, 
                            litE (stringL (faultString cName cArity con))] 
  clause [varP blameName, varP locName, varP explName
         ,conP cName (map varP cArgNames)]
         (normalB body) []

-- | Contract for empty list.
pNil :: Contract [a]
pNil = C (\b l e x -> case x of [] -> Right x; _:_ -> cFail b "_:_")
 
-- | Contract combinator for non-empty list.
-- Cf. (:) :: a -> [a] -> [a]
pCons :: Contract a -> Contract [a] -> Contract [a]
pCons cx cxs = 
  C (\b l e x -> case x of 
    (y:ys) -> Right (monitor b l (e . \s->("("++s++":_)")) cx y : 
                     monitor b l (e . \s->("(_:"++s++")")) cxs ys)
    [] -> cFail b "[]")

-- | Alternative name for 'pCons'.
(=:) :: Contract a -> Contract [a] -> Contract [a]
(=:) = pCons
infixr 5 =:

-- | Contract for non-empty list.
pNotNil :: Contract [a]
pNotNil = C (\b l e x -> case x of [] -> cFail b "[]"; _ -> Right x)

-- | Contract for not non-empty list, i.e., empty list.
pNotCons :: Contract [a]
pNotCons = C (\b l e x -> case x of _:_ -> cFail b "_:_"; _ -> Right x)

-- | Contract combinator for list with elements meeting given contract.
list :: Contract a -> Contract [a]
list c = pNil |> pCons c (dropContext (list c))

-- | Contract combinator for IO-monad with return value meeting given contract.
io :: Contract a -> Contract (IO a)
io c = C (\b l e m -> Right (m >>= return . monitor b l (e . \s->("IO "++s)) c))

-- | Contract for empty tuple.
pTuple0 :: Contract ()
pTuple0 = C (\b l e () -> Right ())

-- | Contract combinator for tuple with values meeting given contracts.
pTuple2 :: Contract a -> Contract b -> Contract (a,b)
pTuple2 c1 c2 = 
  C (\b l e (x1,x2) -> Right (monitor b l (e . \s->("("++s++",_)")) c1 x1
                             ,monitor b l (e . \s->("(_,"++s++")")) c2 x2))

-- | Contract combinator for 3-tuple with values meeting given contracts.
pTuple3 :: Contract a -> Contract b -> Contract c -> Contract (a,b,c)
pTuple3 c1 c2 c3 = 
  C (\b l e (x1,x2,x3) -> Right (monitor b l (e . \s->("("++s++",_,_)")) c1 x1
                                ,monitor b l (e . \s->("(_,"++s++",_)")) c2 x2
                                ,monitor b l (e . \s->("(_,_,"++s++")")) c3 x3))

-- | Contract combinator for 4-tuple with values meeting given contracts.
pTuple4 :: 
  Contract a -> Contract b -> Contract c -> Contract d -> Contract (a,b,c,d)
pTuple4 c1 c2 c3 c4 = 
  C (\b l e (x1,x2,x3,x4) -> Right 
    (monitor b l (e . \s->("("++s++",_,_,_)")) c1 x1
    ,monitor b l (e . \s->("(_,"++s++",_,_)")) c2 x2
    ,monitor b l (e . \s->("(_,_,"++s++",_)")) c3 x3
    ,monitor b l (e . \s->("(_,_,_,"++s++")")) c4 x4))

-- | Contract combinator for data constructor 'Just'
-- with value meeting given contract.
pJust :: Contract a -> Contract (Maybe a)
pJust cy = C proj
  where
  -- proj :: Loc -> ExplanationB -> Maybe a -> Either String (Maybe a)
  proj b l e (Just y) = Right (Just (monitor b l (e . context "Just" 1 1) cy y))
  proj b l e Nothing = cFail b "Nothing"

-- | Contract for data constructor 'Nothing'.
pNothing :: Contract (Maybe a)
pNothing = C proj
  where
  proj b l e Nothing = Right Nothing
  proj b l e (Just _) = cFail b "Just _" 

-- | Contract for non-'Nothing' value.
pNotNothing :: Contract (Maybe a)
pNotNothing = 
  C (\b l e x -> case x of Nothing -> cFail b "Nothing"; _ -> Right x)

-- | Contract for non-'Just' value.
pNotJust :: Contract (Maybe a)
pNotJust = 
  C (\b l e x -> case x of Just _ -> cFail b "Just _"; _ -> Right x)

-- | Contract combinator for type 'Maybe' 
-- given contract for possible argument value. 
maybe :: Contract a -> Contract (Maybe a)
maybe c = pNothing |> pJust c 
