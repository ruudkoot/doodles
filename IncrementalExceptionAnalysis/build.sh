#!/bin/bash
ghc -O2 --make Main.hs
./Main > test.tex
pdflatex test.tex && pdflatex test.tex && evince test.pdf
