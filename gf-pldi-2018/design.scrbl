#lang gf-pldi-2018

@title[#:tag "sec:design"]{Between Soundness and Unsoundness}

@; TODO express as section

Primary design goals:
@itemlist[
@item{
  re-use Typed Racket type checker,
}
@item{
  type-tag soundness,
}
@item{
  separate compilation,
}
@item{
  dynamic type-checks run in @${O(1)} time and space,
}
@item{
  minimize the number of dynamic checks.
}
]

@;Secondary design goals:
@;@itemlist[
@;@item{
@;  no @tt{Dyn} type,
@;}
@;@item{
@;  sound for all of Racket (state, first-class classes),
@;}
@;]

@section{Approaches}

First idea, check tags when values cross from untyped to typed.
On imports.
After calling untyped function.
Before calling typed function
Slogan is, @emph{you can trust the tags}.
That means,
@itemlist[
@item{
  if type is @${\tint}, can do int operations (+, -, *),
}
@item{
  if type is @${\tlist\,\tau} can do list operations (first, rest),
}
@item{
  if type is @${\tarrow\,\tau_0\,\tau_1} can do function operations (apply),
}
@item{
  if type is @${\alpha} can do type var operations (NOTHING).
}
]

@; suppose f : T0 -> T1 called from typed code, but not sure about arguments,
@;  instead of asking T0 about argument,
@;  could ask T0_f about arguments ... meaning are the parts that f accesses already checked
@;  OH NO need to know about f transitive closure

@; Second idea, check tags at the last second.
@; Slogan is, @emph{it's just dynamic typing}.
@; Only check the boundary between typed code and the runtime.
@; Use @${\tau} instead of machine tags to guide checks.
@; The benefit is more undefined primop apps, can use to reason about the program.


@section{Model, Theorems}

TBA

Types (sloppy now, will want to hierarchize later)

@exact|{$$
\begin{array}{l c l}
 \tau & = & \tint
       \mid \tlist\,\tau
       \mid \tarrow\,\tau\,\tau
       \mid \tall \alpha.\,\tau
       \mid \tunion \tau \ldots
\end{array}
$$}|

Value relation (how to tag check)

@exact|{
\fbox{$\vrel{\vstategen}{\tau}$}

\begin{mathpar}
  \inferrule*{
    v \in \integers
  }{
    \vrel{\vstategen}{\tint}
  }

  \inferrule*{
    ???
  }{
    \vrel{\vstategen}{\tlist\,\tau}
  }
\end{mathpar}}|
