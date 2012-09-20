{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Printing where

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

class LaTeX a where
    latex :: a -> String

instance LaTeX String where
    latex = id

instance (LaTeX k, LaTeX v) => LaTeX (M.Map k v) where    
    latex m | M.null m  = "\\epsilon"
            | otherwise = ("\\left["++) . (++"\\right]") . L.intercalate ", " . map (\(k, v) -> latex k ++ "\\mapsto" ++ latex v) . M.toList $ m

instance LaTeX a => LaTeX (S.Set a) where
    latex = ("\\left\\{"++) . (++"\\right\\}") . L.intercalate ", " . map latex . S.toList

preamble  =  "\\documentclass{article}\n"
          ++ "\\usepackage{amsmath}\n"
          ++ "\\usepackage[a4paper,landscape]{geometry}\n"
          ++ "\\usepackage[cm]{fullpage}\n"
          ++ "\\usepackage{stmaryrd}\n"
          ++ "\\begin{document}\n"
postamble =  "\\end{document}"

newline = "\\\\"
