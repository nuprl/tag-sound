#lang gf-pldi-2018

@title{Implementing Tagged Racket}

High-level architecture of Typed Racket:

@itemlist[
@item{
  type-check a module,
}
@item{
  use type environment to generate contracts for exported functions,
}
@item{
  optimize the module
}
@item{
  output Racket bytecode
}
]

To implement @|LD-Racket|, we modified step 2 and replaced step 3.

@section{Generating Type-Tag Contracts}

Typed Racket defines a function @hyperlink["https://github.com/racket/typed-racket/blob/master/typed-racket-lib/typed-racket/private/type-contract.rkt#L283"]{@racket[type->contract]} that
 (1) expects a type, (2) compiles the type to a data structure that describes a contract, (3) optimizes the representation of the data structure, and (4) compiles the data structure to Racket code that will generate an appropriate contract.
This ``data structure that describes a contract'' is called a @hyperlink["https://github.com/racket/typed-racket/tree/master/typed-racket-lib/typed-racket/static-contracts"]{static contract}.

We modified the @racket[type->contract] function to generate type-tag contracts
 by adding a new method to the static contracts API and a new function for static contracts.
The method converts a static contract to a Racket contract that checks it's type tag.
For example, the contract for a list type generates the tag check @racket[list?].
The function expects a static contract and a natural-number amount of fuel.
If the fuel is zero, it returns a tag version of the contract.
Otherwise, it recurs into the static contract and decrements the fuel if the contract
 is for a guarded type (e.g., an intersection type is unguarded).
Note: the initial fuel is always zero for the code we evaluate in this paper.


@section{Defending Typed Code}

We replaced the Typed Racket optimizer with a similarly-structured function that inserts type-tag checks.
The function is a fold over the syntax of a type-annotated program.
The fold performs two kinds of rewrites.

First, the fold rewrites almost every function application @racket[(f x)] to @racket[(check K (f x))], where @racket[K] is the static type of the application.
The exceptions, which do not get a check, are:
@itemlist[
@item{
  built-in functions that we trust to return a well-tagged value (e.g. @racket[map]),
}
@item{
  functions defined in statically-typed code (exception: accessor functions for user-defined @hyperlink["http://docs.racket-lang.org/reference/define-struct.html#%28form._%28%28lib._racket%2Fprivate%2Fbase..rkt%29._struct%29%29"]{structs}),
}
]

Second, the fold defends typed functions from dynamically-typed arguments
 by translating a function like @racket[(λ (x) e)] to @racket[(λ (x) (check x) e)].
The structure of the check is based on the domain type of the function.

