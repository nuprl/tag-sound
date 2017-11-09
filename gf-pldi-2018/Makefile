PAPER=gf-pldi-2018
PKG=gf-pldi-2018
SCRIBBLE_FLAGS=++style texstyle.tex ++extra mathpartir.sty ++extra fig:dyn-lang.tex ++extra fig:sta-lang.tex ++extra fig:mixed-lang.tex ++extra fig:erased-delta.tex ++extra fig:erased-embedding.tex ++extra fig:natural-delta.tex ++extra fig:natural-embedding.tex ++extra fig:delayed-delta.tex ++extra fig:delayed-embedding.tex ++extra fig:forgetful-delta.tex ++extra fig:forgetful-embedding.tex ++extra fig:tagged-delta.tex ++extra fig:tagged-embedding.tex

PLT_FLAGS=PLTSTDERR="error info@gtp-plot"

pdf: compile texstyle.tex
	${PLT_FLAGS} scribble ${SCRIBBLE_FLAGS} --pdf $(PAPER).scrbl

all: pkg setup pdf

tex: compile texstyle.tex
	${PLT_FLAGS} scribble ${SCRIBBLE_FLAGS} --latex $(PAPER).scrbl

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

