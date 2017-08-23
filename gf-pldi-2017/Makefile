PAPER=gf-pldi-2017
PKG=gf-pldi-2017
SCRIBBLE_FLAGS=++style texstyle.tex ++extra mathpartir.sty

pdf: compile texstyle.tex
	scribble ${SCRIBBLE_FLAGS} --pdf $(PAPER).scrbl

all: pkg setup pdf

tex: compile texstyle.tex
	scribble ${SCRIBBLE_FLAGS} --latex $(PAPER).scrbl

pkg:
	raco pkg install --skip-installed

setup:
	raco setup ${PKG}

test:
	raco test -c ${PKG}

compile:
	raco make ${PAPER}.scrbl

clean:
	rm -r compiled

