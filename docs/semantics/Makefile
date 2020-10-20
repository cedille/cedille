arxiv-version.pdf:	arxiv-version.tex Makefile
	rm -f arxiv-version.aux arxiv-version.out
	pdflatex arxiv-version
	pdflatex arxiv-version

paper.pdf:	paper.tex biblio.bib
	rm -f paper.bbl paper.aux paper.out
	pdflatex paper
	bibtex paper
	pdflatex paper
	pdflatex paper


