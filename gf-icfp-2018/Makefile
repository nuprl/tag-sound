PAPER=gf-icfp-2018
PKG=gf-icfp-2018
SCRIBBLE_FLAGS=++extra style.tex ++extra mathpartir.sty ++extra fig:erasure-reduction.tex ++extra fig:erasure-preservation.tex ++extra fig:erasure-embedding.tex ++extra fig:natural-preservation.tex ++extra fig:natural-reduction.tex ++extra fig:natural-embedding.tex ++extra fig:conatural-preservation.tex ++extra fig:conatural-reduction.tex ++extra fig:conatural-embedding.tex ++extra fig:forgetful-preservation.tex ++extra fig:forgetful-reduction.tex ++extra fig:forgetful-embedding.tex ++extra fig:locally-defensive-embedding.tex ++extra fig:locally-defensive-preservation.tex ++extra fig:locally-defensive-reduction.tex ++extra fig:multi-syntax.tex ++extra fig:multi-typing.tex ++extra fig:multi-preservation.tex ++extra fig:multi-reduction.tex ++extra fig:delta.tex ++extra fig:relprime-completion.tex ++extra fig:relprime-typing.tex ++extra fig:relprime-tagging.tex ++extra fig:relprime-reduction.tex ++extra fig:existing-thorn.tex ++extra fig:existing-dart.tex ++extra fig:existing-pyret.tex ++extra fig:existing-strongscript.tex ++extra fig:existing-safets.tex ++extra fig:existing-nom.tex ++extra fig:simulation.tex ++extra artifacts_available.jpg ++extra artifacts_evaluated_functional.jpg
SUPPLEMENT=gf-icfp-2018-supplement
PLT_FLAGS=PLTSTDERR="error info@gtp-plot info@techreport"
RACO=raco

pdf: compile texstyle.tex
	${PLT_FLAGS} ${RACO} scribble ++style texstyle.tex ${SCRIBBLE_FLAGS} --pdf $(PAPER).scrbl

all: pkg setup pdf supplement

tex: compile texstyle.tex
	${PLT_FLAGS} ${RACO} scribble ++style texstyle.tex ${SCRIBBLE_FLAGS} --latex $(PAPER).scrbl

pkg:
	${RACO} pkg install --auto --skip-installed

setup:
	${RACO} setup ${PKG}

supplement: supplement-compile texstyle-appendix.tex
	${PLT_FLAGS} ${RACO} scribble ++style texstyle-appendix.tex ${SCRIBBLE_FLAGS} --pdf ${SUPPLEMENT}.scrbl

supplement-tex: supplement-compile texstyle-appendix.tex
	${PLT_FLAGS} ${RACO} scribble ++style texstyle-appendix.tex ${SCRIBBLE_FLAGS} --latex ${SUPPLEMENT}.scrbl

test:
	${RACO} test -c ${PKG}

compile:
	${RACO} make -v ${PAPER}.scrbl

supplement-compile:
	${RACO} make -v ${SUPPLEMENT}.scrbl

clean:
	rm -r compiled

