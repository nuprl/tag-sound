TALK=simple.ss
RACO=raco

all: preview

compile:
	@${RACO} make -v ${TALK}

preview: compile
	@${RACO} slideshow --right-half-screen ${TALK}

test: compile
	@${RACO} test ${TALK}

show: compile
	@${RACO} slideshow ${TALK}

pdf: compile
	@${RACO} slideshow --condense --pdf ${TALK}

