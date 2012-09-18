module Printing where

class LaTeX a where
    latex :: a -> String
    
preamble  = "\\documentclass{article}\n\\usepackage{stmaryrd}\n\\begin{document}\n"
postamble = "\\end{document}"

newline = "\\\\"
