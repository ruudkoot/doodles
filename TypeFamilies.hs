{-# LANGUAGE GADTs, TypeFamilies #-}

module Main where


data Rep a = K a | Rep a :+: Rep a | Rep a :*: Rep a

type family Derivative
type family Deri
type family Derivative (a :*: b) = a :+: Derivative b :*: Derivative a :+: b

