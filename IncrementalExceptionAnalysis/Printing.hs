{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Printing where

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Data.Tree as T

class LaTeX a where
    latex :: a -> String
    
instance LaTeX Bool where
    latex b = "\\mathbf{" ++ show b ++ "}"

instance LaTeX String where
    latex = id
    
instance (LaTeX a, LaTeX b) => LaTeX (a, b) where
    latex (x, y) = "\\left(" ++ latex x ++ ", " ++ latex y ++ "\\right)"

instance (LaTeX k, LaTeX v) => LaTeX (M.Map k v) where    
    latex m | M.null m  = "\\epsilon"
            | otherwise = ("\\left["++) . (++"\\right]") . L.intercalate ", " . map (\(k, v) -> latex k ++ "\\mapsto" ++ latex v) . M.toList $ m


instance LaTeX a => LaTeX (S.Set a) where
    latex = ("\\left\\{"++) . (++"\\right\\}") . L.intercalate ", " . map latex . S.toList

{-
instance LaTeX a => LaTeX (S.Set a) where
    latex = L.intercalate " \\cup " . map latex . S.toList
-}

instance LaTeX a => LaTeX (T.Tree a) where
    latex (T.Node x cs) = "\\frac{" ++ concatMap latex cs ++ "}{" ++ latex x ++ "}"

preamble  =  "\\documentclass{article}\n"
          ++ "\\usepackage{amsfonts}\n"
          ++ "\\usepackage{amsmath}\n"
          ++ "\\usepackage{amssymb}\n"
          ++ "\\usepackage[a4paper,landscape]{geometry}\n"
          ++ "\\usepackage[cm]{fullpage}\n"
          ++ "\\usepackage{stmaryrd}\n"
          ++ "\\begin{document}\n"
postamble =  "\\end{document}"

newline = "\\\\"

mapsto l r = L.intercalate ", " 
             . map (\(k, v) -> l ++ latex k ++ "\\mapsto" ++ r ++ latex v)
             . M.toList
