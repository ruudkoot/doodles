module Main where

-- related to unfold?

data RotationState a
    = Reversing [a] [a] [a] [a]
    | Appending     [a]     [a]
    | Done                  [a]
    deriving Show
    
startRotation f r = Reversing f [] r []

exec (Reversing (x:f) f' (y:r) r') = Reversing f  (x:f') r (y:r')
exec (Reversing []    f' [y]   r') = Appending       f'    (y:r')
exec (Appending    (x:f')      r') = Appending       f'    (x:r')
exec (Appending []             r') = Done                     r'


