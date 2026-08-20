# Build the paper. Requires latexmk + a TeX distribution.
MAIN = main

.PHONY: all watch clean

all:
	latexmk -pdf -synctex=1 -interaction=nonstopmode $(MAIN).tex

# Rebuild automatically on save (nice with the LaTeX Workshop preview pane).
watch:
	latexmk -pdf -synctex=1 -pvc -interaction=nonstopmode $(MAIN).tex

clean:
	latexmk -C
	rm -f *.bbl *.synctex.gz
