pdf: pwrt.md racket.xml
	pandoc --standalone --syntax-definition=racket.xml --highlight-style=kate --from=markdown+latex_macros --metadata title="Programming with Refinement Types in Typed Racket" --output=pwrt.tex -V geometry:margin=1in -V urlcolor=cyan pwrt.md
	pdflatex pwrt.tex
	pdflatex pwrt.tex
	rm pwrt.aux pwrt.log pwrt.tex
