
# Rado Ivanov - 8/20/2013
# Make-file for the CIS400/4001 Project Proposal Specification

	# Filenames to be-used in compilation
MAIN=prop_spec
TEX=prop_spec.tex

	# Core compilation commands
CC=pdflatex
BB=bibtex

all:$(TEX) $(BIB)
	$(CC) $(TEX)
	$(BB) $(MAIN)
	$(CC) $(TEX)
	$(CC) $(TEX)
	
	rm -rf *.log *.aux *.bbl *.blg
	rm -rf *eps-converted-to.pdf
