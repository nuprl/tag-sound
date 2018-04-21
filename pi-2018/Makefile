TALK="pi-2018.rkt"

all: show

compile:
	raco make -v ${TALK}

preview: compile
	raco slideshow --right-half-screen ${TALK}

test: compile
	raco test ${TALK}

show: compile
	raco slideshow ${TALK}

pdf: compile
	raco slideshow --condense --pdf ${TALK}

