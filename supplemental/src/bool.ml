(** This module defines (and explains) an interpreter for a simple Boolean
    algebra consisting of the primitive Boolean values, conjunction, negation,
    and conditional expressions. **)

open Camlrack
open Camlrack.ListConvenienceFunctions

(* Let us assume that we wish to implement an interpreter for a small Boolean
   algebra language with true, false, logical conjunctions ("and"), logical
   negations ("not"), and logical conditions ("if").

   The first step will be to define our language's syntax. We do this by giving
   a BNF grammar:

     b ::= T | F

     e ::= b
        |  (e and e)
        |  (not e)
        |  (if e then e else e)

   Here, we're using the metavariable [b] to stand for "Boolean values" and the
   metavariable [e] to stand for "expressions". In this representation, we are
   just using the metavariables inside the definitions directly instead of
   wrapping them in angle brackets as you may sometimes see. We can get away
   with this because there are no cases where this will lead to confusion.

   Now that we have a grammar of expressions, we will need to construct a type
   to represent instances of our language in OCaml. We'll name this type [exp]
   and give it constructors for each of the possible productions of [e]. This
   type corresponds to our language's AST, or Abstract Syntax Tree. *)

(** The type of expressions for our small Boolean algebra. *)
type exp =
  (* Primitive Boolean values representing [true] and [false]. *)
  | T | F
  (* The Boolean conjunction operator, [and]. *)
  | And of exp * exp
  (* The Boolean negation operator, [not]. *)
  | Not of exp
  (* The Boolean condition operator, [if]. *)
  | If of exp * exp * exp

(* Next, we'll write a parser. The parser is a function that takes some kind of
   input from the user and converts it into an AST (our [exp] type from above)
   so we can actually do things with it.

   You will almost never need to write a complete parser from scratch --- there
   are tons of libraries and tools available to make your life easier. For this
   class, we'll be using Camlrack to convert user-input strings into
   S-expressions as an intermediate representation, and then we will convert
   those S-expressions to instances of the [exp] AST type.

   (If you're familiar with parsing at all, you know that usually there is a
   "tokenization" step. That's what we're using the S-expressions for!) *)

(** Parses a [string] to an [exp], if possible. Raises an exception on
    failure. *)
let parse (s : string) : exp =
  let rec parse' (se : sexp) : exp =
    match%spat se with
    (* The [T] and [F] forms can be parsed trivially. *)
    | "T" -> T
    | "F" -> F
    (* Camlrack provides an [ANY] form that matches any valid S-Expression.
       The below is interpreted to mean "match any S-Expression that contains
       three things: an S-Expression, the literal symbol 'and', and another
       S-Expression". *)
    | "(ANY and ANY)" ->
      (* Although not the most efficient, the typical way to use a parser like
         Camlrack is to convert our S-Expression to a list, then select elements
         from it and recursively parse those. For our needs, this is more than
         fast enough! *)
      And (parse' (first (sexp_to_list se)),
           parse' (third (sexp_to_list se)))
    | "(not ANY)" ->
      Not (parse' (second (sexp_to_list se)))
    | "(if ANY then ANY else ANY)" ->
      If (parse' (second (sexp_to_list se)),
          parse' (fourth (sexp_to_list se)),
          parse' (sixth (sexp_to_list se)))
    (* Whenever we find an input we weren't expecting, we just raise an
       exception. A good tip is to write the name of the function that throws
       the error in the exception's message. *)
    | _ -> failwith "parse: invalid input"
  in
  (* Here, we use Camlrack to convert the string to an S-expression ([sexp]).
     Note that this function will raise an exception if the conversion fails,
     which is noted with the [_exn] ending to the function's name. *)
  parse' (Camlrack.sexp_of_string_exn s)

(* Sometimes it might be nice to reconstruct our syntactic language from the
   AST, so we'll define a function for that. This is not necessary, especially
   for our simple Boolean algebra language, but sometimes it makes debugging
   significantly easier so it's good to practice! *)

(** Converts an [exp] into a [string]. *)
let rec string_of_exp (a : exp) : string =
  match a with
  | T -> "T"
  | F -> "F"
  | And (l, r) -> "(" ^ string_of_exp l ^ " and " ^ string_of_exp r ^ ")"
  | Not e -> "(not " ^ string_of_exp e ^ ")"
  | If (cond, thn, els) -> "(if " ^ string_of_exp cond ^
                           " then " ^ string_of_exp thn ^
                           " else " ^ string_of_exp els ^ ")"


(* Now that we can parse our inputs into the [exp] in OCaml, we can write a
   function to interpret that input to reduce it to a Boolean value.

   Our interpreter's operation is defined by the language's semantics, so if we
   want to implement an interpreter, we first must write down the semantics!

   (Recall that semantic rules are defined using a "binary relation". The
   traditional operator we use for indicating the small-step reduction relation
   is written as a right-pointing arrow with a thin tail [->].)

                          e1 -> e1'
                 ---------------------------              E-AndLeft
                 (e1 and e2) -> (e1' and e2)

                           e -> e'
                   -----------------------                E-AndRight
                   (b and e) -> (b and e')

                       --------------                     E-AndTrueTrue
                       (T and T) -> T

                       --------------                     E-AndTrueFalse
                       (T and F) -> F

                       --------------                     E-AndFalseTrue
                       (F and T) -> F

                       --------------                     E-AndFalseFalse
                       (F and F) -> F

                           e -> e'
                     -------------------                  E-NotStep
                     (not e) -> (not e')

                        ------------                      E-NotTrue
                        (not T) -> F

                        ------------                      E-NotFalse
                        (not F) -> T

                          e1 -> e1'
     ---------------------------------------------------  E-IfCond
     (if e1 then e2 else e3) -> (if e1' then e2 else e3)

                          e1 -> e1'
      -------------------------------------------------   E-IfThen
      (if b then e1 else e2) -> (if b then e1' else e2)

                           e -> e'
      -------------------------------------------------   E-IfElse
      (if b1 then b2 else e) -> (if b1 then b2 else e')

               ----------------------------               E-IfTrue
               (if T then b1 else b2) -> b1

               ----------------------------               E-IfFalse
               (if F then b1 else b2) -> b2

   Whew, that's a lot of rules!

   Notice that we do not define any rules for reducing the Boolean values from
   [b]. These are considered "atomic", which means they cannot be reduced any
   further.

   Also, we should note something about the notation: whenever a metavariable is
   used multiple times within a single rule, we attach a number to it. (In a
   paper, these numbers are typically written as subscripts.) The number is
   determined only by the order of appearance of the metavariable. This is why
   the [e] corresponding to the [else] part of the [if]-expression is written as
   [e3] in the E-IfCond rule, [e2] in the E-IfThen rule, and just [e] in the
   E-IfElse rule.

   Now look at the E-AndLeft rule. This rule is meant to be used when the two
   arguments to the [and] operator have not yet been reduced. It forces the
   first argument, [e1], to take a single step forward, then constructs a new
   [and] operation with that stepped-forward result. This rule will be used
   multiple times until the [e1] expression is a Boolean value from [b], at
   which point we can use E-AndRight in the same way.contents

   Once we have reduced the two sub-terms of the [and] expression, we can apply
   one of the four other semantic rules to step to a result. Because we're doing
   everything syntactically, we need one rule for each of the possible
   combinations of Boolean values!

   You may be wondering: Boolean values [b] are part of the definition of
   expressions [e], so couldn't an expression like [(and F T)] be reduced using
   E-AndLeft instead of E-AndFalse? Because we have not provided any rules for
   reducing Boolean values themselves, there is no rule we can plug in for the
   [e1 -> e1'] step if [e1] is a Boolean value (i.e., [T] or [F]). E-AndLeft can
   only be used when the first argument to [and] is an un-reduced expression.

   By repeatedly using the above rules, we can evaluate any syntactically valid
   expression in our Boolean algebra.

   Before we implement a [step] function to turn these rules into code, we will
   want a helper function to easily distinguish between Boolean values and other
   expressions in our language. *)

(** Determines whether an expression [a] is actually a Boolean value. *)
let is_value (a : exp) : bool =
  match a with
  | T | F -> true
  | _ -> false


(** Takes a single step according to the small-step operational semantics. *)
let rec step (a : exp) : exp =
  (* Although the order we write down the semantic rules doesn't matter, we do
     have to be careful when we use a pattern-match in OCaml because the various
     cases are considered in-order! So we'll have to be careful to put the more
     general matches at the end. *)
  match a with
  (* Reducing [and]. *)
  | And (T, T) -> T             (* E-AndTrueTrue *)
  | And (T, F) -> F             (* E-AndTrueFalse *)
  | And (F, T) -> T             (* E-AndFalseTrue *)
  | And (F, F) -> F             (* E-AndFalseFalse *)
  | And (b, e)                  (* E-AndRight *)
    when is_value b ->
    let e' = step e in
    And (b, e')
  | And (e1, e2) ->             (* E-AndLeft *)
    let e1' = step e1 in
    And (e1', e2)
  (* Reducing [not]. *)
  | Not T -> F                  (* E-NotTrue *)
  | Not F -> T                  (* E-NotFalse *)
  | Not e ->                    (* E-NotStep *)
    let e' = step e in
    Not e'
  (* Reducing [if]. *)
  | If (T, b1, b2)              (* E-IfTrue *)
    when is_value b1 && is_value b2 ->
    b1
  | If (F, b1, b2)              (* E-IfFalse *)
    when is_value b1 && is_value b2 ->
    b2
  | If (b1, b2, e)              (* E-IfElse *)
    when is_value b1 && is_value b2 ->
    let e' = step e in
    If (b1, b2, e')
  | If (b, e1, e2)              (* E-IfThen *)
    when is_value b ->
    let e1' = step e1 in
    If (b, e1', e2)
  | If (e1, e2, e3) ->          (* E-IfCond *)
    let e1' = step e1 in
    If (e1', e2, e3)
  (* In any other case, we just don't take a step. *)
  | _ -> a

(* We've implemented our small-step reduction in OCaml, but it only takes a
   single step at a time! This corresponds directly to our semantics, but
   sometimes we may want to take multiple steps at a time, or run an input until
   it is fully reduced. To do this, we will define a modified version of our
   small-step reduction relation, [->], that takes multiple steps at a time.
   This is the small-step multi-step reduction relation, and the operator it is
   traditionally given is the same arrow but with a star afterwards: [->*].

   To implement this relation, we will write a [multistep] function. This
   [multistep] function will take two arguments: the [exp] to be evaluated, and
   a number of steps to take before quitting (assuming the expression is not
   fully reduced to a Boolean value before taking that many steps). *)

(** Takes [k] steps over the given expression [a]. The function will return
    early if the argument it receives is a value according to [is_value], or if
    it attempts to take a step and the output of that step is the same as the
    input.

    NOTE: If [k] is negative, this function will continue to recurse until the
    reduction is complete. *)
let rec multistep (k : int) (a : exp) : exp =
  if k = 0 || is_value a
  then a
  else
    let a' = step a in
    if a' = a
    then a
    else multistep (k - 1) a'

(* That's the end of our interpreter for this small Boolean algebra. Some tests
   are provided below. *)

(** This module provides some test functions for the above interpreter. If you
    have the parent module open in utop, you can do [Tests.run_tests ();;] to
    execute all the tests. If all tests are successful, you will get back the
    unit value. If any test fails, an assertion error will be raised. *)
module Tests = struct
  type test = (string * exp)

  let tests : test list =
    [ ("T", T)
    ; ("F", F)
    ; ("(T and F)", F)
    ; ("((not (if T then F else (T and T))) and (not F))", T)
    ]

  let max_steps = 5

  let run_test ((input, result) : test) : unit =
    assert ((multistep max_steps (parse input)) = result)

  let run_tests () = List.iter run_test tests
end
