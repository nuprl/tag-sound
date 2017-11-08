PAPER=gf-pldi-2018
PKG=gf-pldi-2018
SCRIBBLE_FLAGS=++style texstyle.tex ++extra mathpartir.sty ++extra fig:dyn-lang.tex ++extra fig:sta-lang.tex ++extra fig:mixed-lang.tex ++extra fig:natural-embedding.tex ++extra fig:natural-monitors.tex ++extra fig:natural-cost.tex
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

