## Denotational hardware design in Agda

This library will be replaced by [Felix](https://github.com/conal/felix), which makes several changes and narrowing the scope.

## Introduction

This Agda project aims to synthesize machine-verified, parallel hardware designs from high-level denotational specifications.
The common algebraic abstraction is categories, as described in the talks [*From Haskell to Hardware via CCCs*](https://github.com/conal/talk-2015-haskell-to-hardware/blob/post-tabula/README.md) and [*Teaching new tricks to old programs*](https://github.com/conal/2017-talk-teaching-new-tricks-to-old-programs#readme), as well as the paper [*Compiling to categories*](http://conal.net/papers/compiling-to-categories/).

The semantics of various representations are given by mappings from operationally motivated representations to their essential denotations.
Those mappings are required to be homomorphic with respect to the shared programming interface.
This requirement yields a collection of homomorphism equations all solutions of which are correct implementations.
As a happy byproduct, the homomorphisms also ensure that all expected laws hold (assuming equivalence is denotational).

## Dependencies

*   [Agda compiler](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs).
    Known to work with Agda 2.6.2
*   The [Agda standard library (agda-stdlib)](https://github.com/agda/agda-stdlib).
    Known to work with version 1.7.
*   Haskell [ieee754 package](https://github.com/agda/agda/issues/3619) (as described under Troubleshooting below)
*   [GraphViz](https://graphviz.org/) for circuit graph rendering

## Building

Makefile targets:

*   `compile`: compiles the `Test` module, but you can compile faster from within the Emacs mode (`∁-c C­x C-c`).
*   `tests`: generates circuit diagrams in the `Figures` subdirectory (dot files and their PDF renderings).
*   `listings`: renders source code to deeply hyper-linked HTML.
    Start perusing at `html/Everything.html`.

## Summary of important modules

*   `Categorical`:
    *   `Object`: Shared interface to categorical products and exponentials as well as booleans.
    *   `Equiv`: Basic interface for morphism equivalences and homomorphisms.
    *   `Raw`: Category classes (including cartesian and cartesian closed).
        "Raw" as in lacking laws (adopting this use of "raw" from agda-stdlib).
    *   `Homomorphism`: Homomorphism classes for categories, cartesian categories, etc.
*   `Ty` (module and directory, as with a few others below): Inductive representation of types/objects with booleans, products, and exponentials, along with mappings to objects in other categories.
*   `Primitive`: "Symbolic" (data type) representation of some common primitives, along with their homomorphic meanings.
    Currently monolithic, but may need some rethinking for modularity.
*   `Routing`: information-rearranging category, indexed by `Ty`.
*   `Linearize`: linearized representation of morphisms as alternating routings and primitives.
    Convenient for generating pictures and code.
*   `Decode`: A category construction and change-of-representation functor.
*   `SSA`: a simple static single-assignment ("SSA") program representation.
    Recursive, in order to support exponentials.
    Conversion from linearized morphisms.
*   `Dot`: generation of GraphViz format from SSA.
*   `Samples`: hardware-friendly algorithms.
*   `Test`: generate pictures from morphisms.
*   `Everything`: import all code as an easy check that everything works.

## Troubleshooting

You might see an error message like this:

```
Calling: ghc -O -o /Users/sseefried/code/agda-machines/Test -Werror -i/Users/sseefried/code/agda-machines -main-is MAlonzo.Code.Test /Users/sseefried/code/agda-machines/MAlonzo/Code/Test.hs --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns
[  1 of 153] Compiling MAlonzo.RTE      ( MAlonzo/RTE.hs, MAlonzo/RTE.o )
Compilation error:

MAlonzo/RTE.hs:9:1: error:
    Could not find module ‘Numeric.IEEE’
    Use -v (or `:set -v` in ghci) to see a list of the files searched for.
  |
9 | import Numeric.IEEE ( IEEE(identicalIEEE, nan) )
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

You can fix this error with:

```
cabal install --lib ieee754
```

You can find out how to more about this issue [here](https://github.com/agda/agda/issues/3619#issuecomment-665232148) and
[here](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs).

## Contributing

I am trying to structure this project in such a way as to leave many clear opportunities to contribute (which I think I did poorly in agda-machines).
For this reason, most functionality is accompanied by semantic functions of type `Homomorphism _⇨₁_ _⇨₂_` for an established morphism type `_⇨₂_` and a new morphism type `_⇨₁_`.
A common first step is to prove specific homomorphism properties of type `CategoryH _⇨₁_ _⇨₂_`, `CartesianH _⇨₁_ _⇨₂_`, etc.

As of 2021-06-01, many of the proofs in [agda-machines](https://github.com/conal/agda-machines) have not been moved over.
You can peek there for hints or start fresh as an exercise.

See the [open issues](https://github.com/conal/agda-hardware/issues).

As another source of tasks, `git grep TODO`.
