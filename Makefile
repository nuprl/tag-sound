RACO=./src/racket/racket/bin/raco
GTP_MEASURE_FLAGS=--output sample-data --warmup 1 -i 8 -c 10 --bin $(shell pwd)/src/racket/racket/bin/
.PHONY: sample-data

all: submodule-init racket-610 paper model

model:
	cd gf-icfp-2018/model-design && ${RACO} make *.rkt && ${RACO} test *.rkt

paper:
	cd gf-icfp-2018 && make all

racket-610:
	cd src/racket && make

submodule-init:
	git submodule update --init src/gtp-measure/ src/racket/ src/require-typed-check/ src/scribble/ src/typed-racket/

sample-data:
	PLTSTDERR="error info@gtp-measure" ${RACO} gtp-measure ${GTP_MEASURE_FLAGS} benchmarks/morsecode/ benchmarks/tag_morsecode/ benchmarks/tag_zombie/ benchmarks/zombie/

new-data:
	PLTSTDERR="error info@gtp-measure" ${RACO} gtp-measure ${GTP_MEASURE_FLAGS} benchmarks/fsm/ benchmarks/jpeg/ benchmarks/kcfa/ benchmarks/morsecode/ benchmarks/sieve/ benchmarks/snake/ benchmarks/suffixtree/ benchmarks/synth/ benchmarks/tag_fsm/ benchmarks/tag_jpeg/ benchmarks/tag_kcfa/ benchmarks/tag_morsecode/ benchmarks/tag_sieve/ benchmarks/tag_snake/ benchmarks/tag_suffixtree/ benchmarks/tag_synth/ benchmarks/tag_tetris/ benchmarks/tag_zombie/ benchmarks/tetris/ benchmarks/zombie/
