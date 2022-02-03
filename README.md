# Interpreters for CMSC 388X

This repository provides some interpreters for material covered in class.

  * [Supplemental](supplemental/)
      * [`bool.ml`](supplemental/src/bool.ml)

        An interpreter for a simple Boolean algebra language. It covers:

         * Defining a grammar.
         * Constructing a type for an AST.
         * Parsing strings to the AST.
         * Small-step operational semantics.
         * Implementing an interpreter for a small-step semantics.
         * Implementing a multistep relation.

      * [`bool2.ml`](supplemental/src/bool2.ml)

        An extension of the language defined in `bool.ml`. It covers:

          * Simplifying a grammar.
          * Defining a helper type.
          * More parsing.
          * Revising operational semantics with a metafunction.
          * Implementing conversion functions.

      * [`arith.ml`](supplemental/src/arith.ml)

        An extension of the language defined in `bool2.ml`, with integers and
        addition. It covers:

          * Using existing notions of values in a grammar definition.
          * A little parsing.
          * A little on operational semantics.
          * A discussion on what it means for a term to get "stuck".


## Interacting With the Code

The code in this repository is implemented in OCaml using the
[Camlrack](https://github.com/pdarragh/camlrack) library for parsing. If you
have all dependencies satisfied, it should be enough to do:

```text
$ dune build
$ dune utop supplemental/src
```

(Assuming you want to interact with the supplemental interpreters.)

From there, you can use the interpreters with qualified names, or you can open
their defining modules:

```text
─( 23:18:03 )─< command 0 >─────────────────────────────────────────────────────
utop # Supplemental.Bool.multistep 5 Supplemental.Bool.T;;
- : Supplemental.Bool.exp = Supplemental.Bool.T
─( 23:18:03 )─< command 1 >─────────────────────────────────────────────────────
utop # open Supplemental.Bool;;
─( 23:28:36 )─< command 2 >─────────────────────────────────────────────────────
utop # multistep 5 T;;
- : exp = T
```
