module Logic.Propositional.Standard.Data where

data Proposition k a
    = Rec (k a)
    | Not (Proposition k a)
    | Proposition k a :/\: Proposition k a
    | Proposition k a :\/: Proposition k a
    | Proposition k a :=>: Proposition k a
    deriving (Eq, Show)
