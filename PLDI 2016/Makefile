PAPER=main

all:
	pdflatex -file-line-error-style -halt-on-error $(PAPER)
	bibtex -min-crossrefs=1000 $(PAPER)
	pdflatex -file-line-error-style -halt-on-error $(PAPER)
	pdflatex -file-line-error-style -halt-on-error $(PAPER)
	grep -InE --color=always "undefined" $(PAPER).log

clean:
	${RM} *~ *.aux *.log *.dvi *.ps *.out $(PAPER).pdf body.tmp head.tmp *.bbl *.blg

over: clean all
