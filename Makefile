RACO=./src/racket/racket/bin/raco
RACKET=./src/racket/racket/bin/racket
GTP_MEASURE_FLAGS=--output sample-data --warmup 1 -i 8 -c 10 --bin $(shell pwd)/src/racket/racket/bin/
.PHONY: sample-data

kick-tires: install paper example model

all: kick-tires sample-data sample-pict

install: submodule-init racket

example:
	${RACO} make example.rkt
	${RACO} test example.rkt

model:
	cd gf-icfp-2018/model-design && ../../${RACO} make *.rkt && ../../${RACO} test *.rkt

paper:
	cd gf-icfp-2018 && make all

racket:
	cd src/racket && make
	ln -s $(shell pwd)/src/racket/racket/bin/racket $(shell pwd)/racket
	ln -s $(shell pwd)/src/racket/racket/bin/raco $(shell pwd)/raco
	ln -s $(shell pwd)/src/racket/racket/bin/drracket $(shell pwd)/drracket

submodule-init:
	git submodule update --init src/gtp-util/ src/gtp-plot/ src/gtp-measure/ src/racket/ src/require-typed-check/ src/scribble/ src/typed-racket/

sample-data:
	PLTSTDERR="error info@gtp-measure" ${RACO} gtp-measure ${GTP_MEASURE_FLAGS} benchmarks/morsecode/ benchmarks/tag_morsecode/ benchmarks/tag_zombie/ benchmarks/zombie/

sample-pict:
	${RACKET} src/plot-sample-data.rkt sample-data/1

new-data:
	PLTSTDERR="error info@gtp-measure" ${RACO} gtp-measure ${GTP_MEASURE_FLAGS} benchmarks/fsm/ benchmarks/jpeg/ benchmarks/kcfa/ benchmarks/morsecode/ benchmarks/sieve/ benchmarks/snake/ benchmarks/suffixtree/ benchmarks/synth/ benchmarks/tag_fsm/ benchmarks/tag_jpeg/ benchmarks/tag_kcfa/ benchmarks/tag_morsecode/ benchmarks/tag_sieve/ benchmarks/tag_snake/ benchmarks/tag_suffixtree/ benchmarks/tag_synth/ benchmarks/tag_tetris/ benchmarks/tag_zombie/ benchmarks/tetris/ benchmarks/zombie/
