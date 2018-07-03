#lang gf-icfp-2018
@require{techreport.rkt}
@appendix-title{Implementing Tagged Racket}

The high-level architecture of @|TR_N| is to:

@itemlist[#:style 'ordered
@item{
  type-check a module,
}
@item{
  use the type environment to generate contracts, @; for exported functions,
}
@item{
  optimize the contracts for the module,
}
@item{
  output Racket bytecode.
}
]

For @|TR_LD|, we modified step 2 and replaced step 3.

@section{Generating Type-Constructor Contracts}

Typed Racket defines a function @hyperlink["https://github.com/racket/typed-racket/blob/master/typed-racket-lib/typed-racket/private/type-contract.rkt#L283"]{@racket[type->contract]} that
 (1) expects a type,
 (2) compiles the type to a so-called @hyperlink["https://github.com/racket/typed-racket/tree/master/typed-racket-lib/typed-racket/static-contracts"]{@emph{static contract}},
 (3) optimizes the representation of the static contract, and
 (4) compiles the static contract to Racket code that will generate an appropriate contract.

We modified the @racket[type->contract] function to generate type-constructor checks 
 by adding a new method to the internal API for static contracts.
For example, the method converts the contract for a list of elements into
 a contract that checks the @racket[list?] predicate.


@section{Defending Typed Code}

The @|TR_LD| prototype replaces the Typed Racket optimizer with a completion
 function that adds type-constructor checks to typed code.
The function implements a fold over the syntax of a type-annotated program,
 and performs two kinds of rewrites.

First, the completion function rewrites @emph{most} applications @racket[(f x)]
 to @racket[(check K (f x))], where @racket[K] is the static type of the
 application.
If @racket[f] is an identifier, however, there are two exceptional cases:
@itemlist[
@item{
  @racket[f] may be a built-in function that is certain to return a value
   of the correct type constructor
   (e.g., @racket[map] always returns a list); and
}
@item{
  @racket[f] may be statically typed, in which case soundness guarantees that
   @racket[f] returns a value that matches its static type constructor.
  (there is one exception: accessor functions for user-defined
   @hyperlink["http://docs.racket-lang.org/reference/define-struct.html#%28form._%28%28lib._racket%2Fprivate%2Fbase..rkt%29._struct%29%29"]{structs}
   are unsafe like any other accessor, e.g., @racket[car]),
}
]
@exact{\noindent}For these exceptional cases, the completion function
 does not insert a type-constructor check.

Second, the completion function defends typed functions from dynamically-typed arguments
 by translating a function like @racket[(λ (x) e)] to @racket[(λ (x) (check x) e)].
The structure of the check is based on the domain type of the function.


@section{Diff vs. Racket v6.10.1}

The repository for this paper contains the @|TR_LD| prototype and a diff
 between the prototype and Typed Racket v6.10.1.

@exact{\noindent}@hyperlink["https://github.com/nuprl/tag-sound?path=src/locally-defensive.patch"]{github.com/nuprl/tag-sound?path=src/locally-defensive.patch}
