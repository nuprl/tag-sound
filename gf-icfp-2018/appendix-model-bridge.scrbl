#lang gf-icfp-2018
@require{techreport.rkt}

@appendix-title++{The Big Picture}

The paragraphs in this section summarize the five embeddings with four slogans.
Each slogan pertains to one aspect of the embedding:
@itemlist[#:style 'ordered
@item{
  What kinds of checks does the embedding perform when a value reaches a type boundary?
}
@item{
  When, if ever, does the embedding wrap a value in a monitor?
}
@item{
  If an ill-typed value reaches a type boundary, when does the embedding signal an error?
}
@item{
  How do types affect behavior?
}
]

These embeddings are ordered on a speculative scale from "most guarantees, worst performance" to "least guarantees, best performance".

@parag{Natural embedding}
@itemlist[#:style 'ordered
@item{
  recursively check read-only values;
}
@item{
  monitor functional and mutable values;
}
@item{
  detect boundary errors as early as possible;
}
@item{
  types globally constrain behavior.
}
]

@parag{Co-Natural embedding}
@itemlist[#:style 'ordered
@item{
  tag-check all values;
}
@item{
  monitor all data structures and functions;
}
@item{
  detect boundary errors as late as possible; *
}
@item{
  types globally constrain behavior
}
]

@parag{Forgetful embedding}
@itemlist[#:style 'ordered
@item{
  tag-check all values;
}
@item{
  apply at most one monitor to each value;
}
@item{
  detect boundary errors as late as possible;
}
@item{
  types locally constrain behavior.
}
]

@parag{Locally-Defensive embedding}
@itemlist[#:style 'ordered
@item{
  tag-check all values;
}
@item{
  never allocate a monitor;
}
@item{
  detect boundary errors as late as possible;
}
@item{
  types locally constrain behavior.
}
]

@parag{Erasure embedding}
@itemlist[#:style 'ordered
@item{
  never check values;
}
@item{
  never allocate a monitor;
}
@item{
  never detect a type boundary error;
}
@item{
  types do not affect behavior
}
]
