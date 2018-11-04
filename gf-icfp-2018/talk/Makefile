TALK=simple.ss
GRACE=grace.ss
RACO=raco

all: preview

compile:
	@${RACO} make -v ${TALK}

preview: compile test
	@${RACO} slideshow --right-half-screen ${TALK}

test: compile
	@${RACO} test src/gt-system.rkt

show: compile
	@${RACO} slideshow ${TALK}

pdf: compile
	@${RACO} slideshow --condense --pdf ${TALK}


gcompile:
	@${RACO} make -v ${GRACE}

gpreview: gcompile
	@${RACO} slideshow --right-half-screen ${GRACE}

gpict: gcompile
	@${RACO} pict ${GRACE}

gshow: gcompile
	@${RACO} slideshow ${GRACE}

gpdf: gcompile
	@${RACO} slideshow --condense --pdf ${GRACE}

