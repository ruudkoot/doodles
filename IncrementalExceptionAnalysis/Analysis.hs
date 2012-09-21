module Analysis where

import qualified Data.Set as S

import Fresh
import Printing

-- | Types 

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)

-- | Free variables

class FreeVars t where
    ftv :: t -> S.Set Ident

-- | Effects

data Eff'
    = EffVar Ident
    | EffCrash
    deriving (Eq, Ord, Show)
    
data Eff
    = EffUnif Ident
    | Eff (S.Set Eff')
    deriving (Eq, Ord, Show)
    
effect = S.fromList . map (\(EffUnif u) -> EffVar u)

instance Fresh Eff where
    fresh = do u <- fresh
               return (EffUnif u)

instance LaTeX Eff' where
    latex (EffVar u) = "\\varphi" ++ u
    latex (EffCrash) = "\\lightning"

instance LaTeX Eff where
    latex (EffUnif u) = "\\dot\\varphi" ++ u
    latex (Eff eff)   = latex eff

-- | Constraints

data Constr'
    = Ident :>: (S.Set Eff')
    deriving (Eq, Ord, Show)
    
type Constr = S.Set Constr'

instance LaTeX Constr' where
    latex (u :>: eff) = "\\dot\\varphi" ++ u ++ "\\supseteq" ++ latex eff
