SOURCES=$(wildcard .tex)

main.pdf: $(SOURCES) biblio.bib
	@pdflatex main.tex
	@bibtex main
	@pdflatex main.tex

clean:
	@rm main.pdf
