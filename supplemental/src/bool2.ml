(** This module defines and explains an interpreter for an extended Boolean
    algebra consisting of primitive Boolean values, conjunctions, and
    disjunctions. **)

open Camlrack
open Camlrack.ListConvenienceFunctions

(* Let's take the same Boolean algebra language from [bool.ml] and add one new
   functionality: the Boolean disjunction operator, [or]. Our BNF grammar for
   this extended language looks like this:

     b ::= T | F

     e ::= b
        |  (e and e)
        |  (e or e)
        |  (not e)
        |  (if e then e else e)

   Almost identical to what we had previously, except we've added the [or] form!
   However, we could imagine going on to later add other binary Boolean
   operators (such as [nand], [xor], etc.). Things could get a bit tedious that
   way, so let's instead define our language's syntax a bit differently:

     b ::= T | F

     binop ::= and | or

     e ::= b
        |  (not e)
        |  (if e then e else e)
        |  (e binop e)

   Now we've defined a [binop] metavariable. Using this, we can express all
   possible binary Boolean operators with a single [e] form. This will come in
   handy later!

   (There are tricks like this that show up the more you work with operational
   semantics. They're not always easy to arrive at by yourself; some of them you
   may just see other people do and eventually come to appreciate. We'll try to
   guide you in this regard based on our experiences, so don't feel bad if this
   seems unintuitive or strange at first!)

   Now we have to implement our expressions in OCaml. We will imitate the above
   construction of the language (i.e., separation the binary operators from the
   other forms) in our type. *)

(** The type of expressions for our extended Boolean algebra. *)
type exp =
  (* These are the same constructors we had previously, minus [and]. *)
  | T | F | Not of exp | If of exp * exp * exp
  (* Now we add a constructor for binary operators, which relies on a new
     [binop] type. *)
  | BinOp of binop * exp * exp

(** The type of binary operators. *)
and binop =
  (* We provide one argument-less constructor for each operator. *)
  | And | Or
  (* You can imagine if we wanted to define additional binary Boolean operators,
     we would only need to extend this part of the type! *)

(* Next, we'll extend our parser. Even though we've changed things around a bit,
   the parsing step remains pretty straightforward! *)

(** Parses a [string] to an [exp], if possible. Raises an exception on
    failure. *)
let parse (s : string) : exp =
  let rec parse' (se : sexp) : exp =
    match%spat se with
    | "T" -> T
    | "F" -> F
    | "(not ANY)" ->
      Not (parse' (second (sexp_to_list se)))
    | "(if ANY then ANY else ANY)" ->
      If (parse' (second (sexp_to_list se)),
          parse' (fourth (sexp_to_list se)),
          parse' (sixth (sexp_to_list se)))
    | "(ANY SYMBOL ANY)" ->
      (* We've revised our handling of binary expressions. Instead of writing
         out a match case for each operator, we're using Camlrack's [SYMBOL]
         form to match any atomic thing. Then, we check that that symbol
         actually corresponds to one of our defined operators. *)
      let op = match (sexp_to_symbol (second (sexp_to_list se))) with
        | "and" -> And
        | "or" -> Or
        (* For this interpreter, we'll raise an exception at this point.
           However, for more complex languages you may need to be more careful
           about when this exception gets raised. *)
        | _ -> failwith "parse: invalid operator in input" in
      BinOp (op,
             parse' (first (sexp_to_list se)),
             parse' (third (sexp_to_list se)))
    | _ -> failwith "parse: invalid input"
  in
  parse' (Camlrack.sexp_of_string_exn s)

(* We will also write a new [exp]-to-[string] function. *)

(** Converts an [exp] into a [string]. *)
let rec string_of_exp (a : exp) : string =
  let string_of_op (op : binop) : string =
    match op with
    | And -> "and"
    | Or -> "or"
  in
  match a with
  | T -> "T"
  | F -> "F"
  | Not e -> "(not " ^ string_of_exp e ^ ")"
  | If (cond, thn, els) -> "(if " ^ string_of_exp cond ^
                           " then " ^ string_of_exp thn ^
                           " else " ^ string_of_exp els ^ ")"
  | BinOp (o, l, r) -> "(" ^ string_of_op o ^
                       " " ^ string_of_exp l ^
                       " " ^ string_of_exp r ^ ")"

(* Now we come to the interesting part: defining an operational semantics for
   our language.

   In our previous iteration, we defined the Boolean conjunction operator [and]
   manually. This required six separate semantic rules to handle correctly. If
   we used the same strategy to implement our disjunction operator [or], it
   would require another six rules! I don't think we want to go through all that
   effort if there is an easier way.

   In cases like this, we can refer to a [metalanguage]. A metalanguage is
   another language that we assume to exist that can help us with some of the
   details of our semantics. For this example, what we want a metalanguage for
   is to interpret the results of Boolean conjunction and disjunction. This is a
   well-known relation that has been defined plenty of other places, so it
   should not be problematic to assume that other computer scientists will
   understand what we mean!

   We will use a special bracket notation, ⟪ and ⟫, to indicate when a syntactic
   term from our language should be converted into the metalanguage. (It is more
   common to use blackboard-bold square brackets, ⟦⟧, but when using a monospace
   font I find the ⟪⟫ to be easier to distinguish.) To do this, we need to
   define precisely what the conversion does:

     ⟪ T ⟫ = true
     ⟪ F ⟫ = false

   In actuality, the ⟪ • ⟫ forms make what is called a [metafunction]. The
   special bracket notation represents a function that relates things from our
   syntax to things in the mathematical world where Boolean values exist.

   We will assume to keep all of the rules from the semantics written in
   [bool.ml], except to remove all of the [and]-related rules. Instead, we will
   define just four new rules to replace them AND handle [or] at the same time:

             e1 -> e1'
     -------------------------   E-OpLeft
     (e1 op e2) -> (e1' op e2)

              e -> e'
       ---------------------     E-OpRight
       (b op e) -> (b op e')

     ⟪ b3 ⟫ = ⟪ b1 ⟫ && ⟪ b2 ⟫
     --------------------------  E-And
         (b1 and b2) -> b3

     ⟪ b3 ⟫ = ⟪ b1 ⟫ || ⟪ b2 ⟫
     --------------------------  E-Or
          (b1 or b2) -> b3

   In this operational semantics, we "inject" our syntactic terms into the
   metalangauge using the ⟪ ⟫ notation. For Boolean values, this means we
   convert our syntactic [T] and [F] into mathematical [true] and [false], then
   rely on the existence of conjunction [&&] and disjunction [||] operators that
   work on those [true] and [false] values. Since these relations are
   well-known, it is reasonable to assume that we do not need to explicitly
   re-implement them in pure operational semantics rules as we did in [bool.ml].

   To use this technique in our interpreter implementation, we're going to need
   a function to convert from syntactic Boolean values to OCaml, then a function
   to convert back from OCaml to our syntactic Boolean values. Note that we will
   only permit the conversion of Boolean values from [b]; we will not convert
   all expressions from [e]. *)

(** Converts an [exp] to an OCaml [bool]. *)
let ocaml_bool_of_exp (a : exp) : bool =
  match a with
  | T -> true
  | F -> false
  | _ -> failwith "ocaml_bool_of_exp: invalid term"

(** Converts an OCaml [bool] to an [exp]. *)
let exp_of_ocaml_bool (b : bool) : exp =
  match b with
  | true -> T
  | false -> F

(* Next, we will copy our [is_value] function from [bool.ml]. *)

(** Determines whether an expression [a] is actually a Boolean value. *)
let is_value (a : exp) : bool =
  match a with
  | T | F -> true
  | _ -> false

(* And now, we can implement the revised [step] function. (There is a nested
   helper function at the top of the [step] definition, then all our new rules
   are implemented at the bottom.) *)

(** Takes a single step according to the small-step operational semantics. *)
let rec step (a : exp) : exp =
  (** Converts a syntactic binary operator into an OCaml function. *)
  let get_op (op : binop) : (bool -> bool -> bool) =
    match op with
    | And -> (&&)
    | Or -> (||)
  in
  match a with
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
  (* Reducing binary operations. *)
  | BinOp (op, v1, v2)          (* E-And and E-Or *)
    when is_value v1 && is_value v2 ->
    exp_of_ocaml_bool ((get_op op) (ocaml_bool_of_exp v1) (ocaml_bool_of_exp v2))
  | BinOp (op, v, e)            (* E-OpRight *)
    when is_value v ->
    let e' = step e in
    BinOp (op, v, e')
  | BinOp (op, e1, e2) ->       (* E-OpLeft *)
    let e1' = step e1 in
    BinOp (op, e1', e2)
  (* As before, in any other case we just don't take a step. *)
  | _ -> a

(* And, again, we will define a [multistep] function to help us take multiple
   steps in a single function call. This is identical to the previous one! *)

(** Takes [k] steps over the given expression [a].

    NOTE: If [k] is negative, this function will continue to recurse until the
    reduction is complete. Be careful of any adversarial inputs! *)
let rec multistep (k : int) (a : exp) : exp =
  if is_value a
  then a
  else
    match k with
    | 0 -> a
    | _ ->
      let a' = step a in
      multistep (k - 1) a'

(** This module provides some test functions for the above interpreter. If you
    have the parent module open in utop, you can do [Tests.run_tests ();;] to
    execute all the tests. If all tests are successful, you will get back the
    unit value. If any test fails, an assertion error will be raised. *)
module Tests = struct
  type test = (string * exp)

  let tests : test list =
    [ ("(T and F)", F)
    ; ("(T and T)", T)
    ; ("(T or F)", T)
    ; ("(F or F)", F)
    ; ("(T or T)", T)
    ; ("(if (T or F) then (T and T) else (not (F or T)))", T)
    ]

  let max_steps = 5

  let run_test ((input, result) : test) : unit =
    assert ((multistep max_steps (parse input)) = result)

  let run_tests () = List.iter run_test tests
end
