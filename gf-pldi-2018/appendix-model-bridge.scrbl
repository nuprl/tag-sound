#lang gf-pldi-2018
@require{techreport.rkt}

@appendix-title++{Bridge Lemmas}

@section{Spectrum of Performance}

@subsection{Notions of Cost}

A reduction rule is a @emph{check rule} if its left-hand-side has the form
 @${\esta{\cdot}{\cdot}} or @${\edyn{\cdot}{\cdot}} or @${\echk{\cdot}{\cdot}}
 or if it invokes the @${\mchk{\cdot}{\cdot}} metafunction.

A reduction rule is an @emph{allocation rule} if its right-hand-side introduces
 a monitor @${\vmon{\cdot}{\cdot}}.

A reduction rule is an @emph{indirection rule} if its left-hand-side expects
 a monitor.

Note that one reduction rule may be, e.g., both an allocation rule and an
 indirection rule.


@subsection{Relative Cost}

N <=alloc  C
N >=check  C
N <=indir  C

C ==alloc  F
C ==check  F
C >=indir  F

F >=alloc  K
F ==check  K
F >=indir  K

K  >check  E

The "intuition" for each comes from the embedding strategy:

- C does not recur
- F does not double-wrap
- K does not monitor
- E erases types

Actual proof I guess will be like:

for all e such that e -->*x A and e -->*y A' then
 [[ (e -->*x A) <= (e -->*y A') ]]

Proved bisimulation.


@section{Spectrum of Soundness}

??? this isn't even the right title

... idea is, weaker soudnness allows some bad programs
