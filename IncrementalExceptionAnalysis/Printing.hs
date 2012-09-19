module Printing where

class LaTeX a where
    latex :: a -> String
    
preamble  =  "\\documentclass{article}\n"
          ++ "\\usepackage{amsmath}\n"
          ++ "\\usepackage[a4paper,landscape]{geometry}\n"
          ++ "\\usepackage[cm]{fullpage}\n"
          ++ "\\usepackage{stmaryrd}\n"
          ++ "\\begin{document}\n"
postamble =  "\\end{document}"

newline = "\\\\"
