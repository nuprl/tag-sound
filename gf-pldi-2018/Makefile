PAPER=gf-pldi-2018
PKG=gf-pldi-2018
SCRIBBLE_FLAGS=++extra style.tex ++extra mathpartir.sty ++extra fig:dyn-lang.tex ++extra fig:sta-lang.tex ++extra fig:mixed-lang.tex ++extra fig:erasure-delta.tex ++extra fig:erasure-embedding.tex ++extra fig:natural-delta.tex ++extra fig:natural-embedding.tex ++extra fig:conatural-delta.tex ++extra fig:conatural-embedding.tex ++extra fig:forgetful-delta.tex ++extra fig:forgetful-embedding.tex ++extra fig:tagged-delta.tex ++extra fig:locally-defensive-embedding.tex ++extra fig:locally-defensive-completion-delta.tex ++extra fig:sta-delta.tex ++extra fig:dyn-delta.tex ++extra fig:mixed-delta.tex ++extra fig:well-tagged.tex ++extra fig:locally-defensive-delta.tex ++extra fig:common-syntax.tex ++extra fig:multi-typing.tex ++extra fig:delta.tex
SUPPLEMENT=gf-pldi-2018-supplement

PLT_FLAGS=PLTSTDERR="error info@gtp-plot info@techreport"

pdf: compile texstyle.tex
	${PLT_FLAGS} scribble ++style texstyle.tex ${SCRIBBLE_FLAGS} --pdf $(PAPER).scrbl

all: pkg setup pdf

tex: compile texstyle.tex
	${PLT_FLAGS} scribble ++style texstyle.tex ${SCRIBBLE_FLAGS} --latex $(PAPER).scrbl

pkg:
	raco pkg install --skip-installed

setup:
	raco setup ${PKG}

supplement: supplement-compile texstyle-appendix.tex
	${PLT_FLAGS} scribble ++style texstyle-appendix.tex ${SCRIBBLE_FLAGS} --pdf ${SUPPLEMENT}.scrbl

supplement-tex: supplement-compile texstyle-appendix.tex
	${PLT_FLAGS} scribble ++style texstyle-appendix.tex ${SCRIBBLE_FLAGS} --latex ${SUPPLEMENT}.scrbl

test:
	raco test -c ${PKG}

compile:
	raco make ${PAPER}.scrbl

supplement-compile:
	raco make ${SUPPLEMENT}.scrbl

clean:
	rm -r compiled

