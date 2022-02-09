# Homework 1

You are given a working interpreter that has has Boolean values, integer values,
`not`, `and`, `or`, `+`, and `iszero`. Your job is to choose some of the
additional functionalities listed below and extend this interpreter accordingly.

Each of the items in the list has a star rating from ☆ to ☆☆☆ that approximately
correlates to its expected difficulty. You must complete enough items to secure
at least 5 stars. (You are welcome to complete more!)

  1.  ☆: `xor` and `nand`

      Add `xor` and `nand` forms to the language. (See the Wikipedia articles
      for [XOR](https://en.wikipedia.org/wiki/XOR_gate) and
      [NAND](https://en.wikipedia.org/wiki/NAND_gate) for the expected truth
      tables.) These should only accept Boolean values as inputs and return
      Boolean values as output.

  2.  ☆: syntactic sugar for `xor` and `nand` [Prerequisite: 1]

      Implement XOR and NAND in the surface language as syntactic sugar (i.e.,
      without adding any corresponding forms to the AST).

  3.  ☆: `-` and `*`

      Add subtraction (`-`) and multiplication (`*`) binary operator forms to
      the language. These should only accept integer values as inputs and reduce
      to integer values as output.

  4.  ☆: short-circuiting

      Implement semantic short-circuiting for `and` and `or`. (Hint: This will
      require re-writing the semantic rules for Boolean operator reduction.)

  5.  ☆☆: `numequal`

      Add a `numequal` binary operation form to the language. The `numequal`
      form should take two integer expressions as arguments and reduce to a
      Boolean value indicating whether they are the same. Note that
      type-checking should ensure both subterms are integers.

  6.  ☆: syntactic sugar for `numequal` [Prerequisite: 5]

      Implement `numequal` in the surface language as syntactic sugar (i.e.,
      without adding any corresponding form to the AST).

  7.  ☆☆: `if`

      Add an `if` form to the language. The `if` form should take three
      arguments: a Boolean indicating which branch to execute, and any two
      subterms. The type-checker should verify that the two subterms have the
      same type, but it should not care what that type is.

  8.  ☆: real numbers

      Add real number values ℝ and a corresponding addition form to the
      language. The floating-point addition operator should be written `+.`.
      (Hint: Use OCaml's floating-point type to approximate the values of real
      numbers.)

  9.  ☆: integer to real number conversion [Prerequisite: 8]

      Add an `int->real` form to the language to convert integers to real
      numbers.

  10. ☆☆☆: implicit coercion [Prerequisite: 8 and 9]

      Add implicit coercion from integers to real number values whenever
      possible. For example, you could extend your real number addition
      operation so that if either of the arguments is an integer, it is
      converted to a real number value. You must also update the type-checker so
      that it will correctly allow integer values as the arguments in a real
      number operation.


## Submission

Update the `items_complete` list in the code (near the top of the file --- it's
marked with a `TODO` comment) to indicate which of the above problems you want
to be graded on. Only submit the `main.ml` file. Your file must compile without
errors for full credit.
