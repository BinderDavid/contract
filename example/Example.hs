{-# LANGUAGE TemplateHaskell #-}
module Main where

import Development.Contract

nat :: (Integral a, Flat a) => Contract a
nat = prop (>= 0)

nats :: (Integral a, Flat a) => Contract [a]
nats = list nat

t3 :: [Integer]
t3 = $assert nats [10,9..(-2)]


sqrtC :: Float -> Float
sqrtC = $attach sqrt (prop (>=0) >-> prop (>=0))

t14 = sqrtC 4
t15 = sqrtC (-4)

main :: IO ()
main = do 
    --print t3
    print t14
    print t15
