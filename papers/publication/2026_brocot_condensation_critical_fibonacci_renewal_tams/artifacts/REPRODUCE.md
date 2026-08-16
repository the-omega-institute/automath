# Reproduction

The article's claims are proved analytically in the manuscript. No numerical
script is used as a premise of a theorem.

From the article directory, run:

    latexmk -C main.tex
    latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex

Check main.log for unresolved references, unresolved citations, and duplicate
labels. There are no verify*.py or test_*.py programs in this artifact set.
