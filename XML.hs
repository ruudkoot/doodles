{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Main where

infixl 3 <|>
infixl 4 <*>

-- | Data types

type XML  l = [Elem l]
data Elem l = Node l String [Attr l] (XML l)
            | Text l String
data Attr l = Attr l String String

-- | Paring

type Parser s a = [s] -> [(a,[s])]

(p <|> q) input = p input ++ q input

(p <*> q) input = [ (pv qv, rest  )
                  | (pv   , qinput) <- p input
                  , (qv   , rest  ) <- q qinput ]

data Parse = Parse { loc :: Int, uncooked :: String }

parse :: String -> Maybe (XML Parse)
parse = undefined
