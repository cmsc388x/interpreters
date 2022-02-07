# Homework 1

You are given a working interpreter. Your job is to choose some of the listed
functionalities and extend the interpreter accordingly.

Each of the listed functionalities has a star rating that approximately
correlates to its expected difficulty. You must complete enough items to secure
at least 5 stars. (You are welcome to complete more!)

  1. ⋆ Add [XOR](https://en.wikipedia.org/wiki/XOR_gate) and
     [NAND](https://en.wikipedia.org/wiki/NAND_gate) forms to the language. (See
     the linked Wikipedia articles for the expected truth tables.) These should
     only accept Boolean values as inputs and return Boolean values as output.
  2. ⋆ [Prerequisite: 1] Implement XOR and NAND in the surface language as
     syntactic sugar (i.e., without adding any corresponding forms to the AST).
  3. ⋆ Add subtraction and multiplication forms to the language. These should
     only accept integer values as inputs and return integer values as output.
  4. ⋆ [Prerequisite: 3] Implement subtraction and addition in the surface
     language as syntactic sugar (i.e., without adding any corresponding forms
     to the AST).
  5. ⋆⋆ Implement semantic short-circuiting for all binary Boolean expressions.
     This will require re-writing the semantic rules for Boolean operator
     reduction.
  6. ⋆ Add floating-point values and floating-point addition. (Hint: use a new
     operator instead of `+`, e.g., OCaml uses `+.`, to make this easier.)
  7. ⋆⋆ [Prerequisite: 6] Add a form to convert integers to floating-point
     numbers.
  8. ⋆⋆⋆ [Prerequisite: 6 and 7] Add implicit coercion from integers to
     floating-point values whenever necessary. For example, you could extend
     your floating-point addition operation so that if either of the arguments
     is an integer, it is converted to a floating-point value. You must also
     update the type-checker so that it will correctly allow integer values as
     the arguments in a floating-point operation.
