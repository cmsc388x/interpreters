(** This module defines and explains an interpreter for a language with Boolean
    operations from [bool2.ml] extended with integers and some operations on
    them. **)

open Camlrack
open Camlrack.ListConvenienceFunctions

(* We've got a pretty good handle on Boolean interpreters, so let's shake things
   up a bit: let's add integers and addition [+].

   So far, we have defined our languages completely syntactically. So how would
   we do this when the set of values we want to describe is infinite?

   One option is to limit our discussion to just a subset of available numbers:

     z ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9

   But then our language technically cannot handle anything bigger than 9 or
   less than 0, which isn't very interesting. We could get a bit clever and do
   something like:

     z ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
        |  z z
        |  - z

   Here, we do technically allow for all integers. But then if we were to peek
   ahead at our operational semantics, it would be awful! We would either need
   separate rules for every possible use of integers (impossible) or else we'd
   need to define a metafunction to convert every one of our syntactic integers
   to actual integers and then use math for our operators (also impossible).

   Since we'd rather implement our interpreter in the real world and not in some
   fantasy-land where we could write all of our numbers infinitely, we will
   instead use a trick and define this grammar in IMpure syntax. Where
   previously we had defined our grammars using only literal syntax and
   metavariables, we will now admit some mathematical description to explain
   what something means.

   The new BNF grammar looks like this:

     b ::= T | F

     z ::= m, where m ∈ ℤ

     v ::= b | n

     binop ::= and | or | +

     e ::= v
        |  (not e)
        |  (if e then e else e)
        |  (e binop e)

   We added two new metavariables: [z] to describe all the integers, and [v] to
   describe all "values". A value is any syntactic form that cannot be reduced
   any further. The Boolean values [b] and integers [z] are all values.

   So now we are relying on the existence of the set of integers, ℤ, to
   define the members of our metavariable [z]. This should be fine --- it seems
   reasonable to assume that any computer scientist with whom we'd like to
   discuss this language will already be familiar with integers!

   We proceed to define a revised implementation of our abstract syntax tree in
   OCaml for our interpreter. *)

(** The type of expressions for our language. *)
type exp =
  (* All these constructors were defined in [bool2.ml]. *)
  | T | F | Not of exp | If of exp * exp * exp | BinOp of binop * exp * exp
  (* For our implementation, we use OCaml's notion of integers. Although this is
     technically only an approximation of the actual set of integers ℤ, it will
     suffice for our needs. *)
  | Int of int

(** The type of binary operators. *)
and binop =
  (* These are the Boolean operators from [bool2.ml]. *)
  | And | Or
  (* We add an [Add] constructor to our type of binary operators. *)
  | Add

(* Now, as usual, we will extend our parser. *)

(** Parses a [string] to an [exp], if possible. Raises an exception on
    failure. *)
let parse (s : string) : exp =
  let rec parse' (se : sexp) : exp =
    match%spat se with
    | "T" -> T
    | "F" -> F
    (* We add a case for parsing integers. Fortunately for us, Camlrack already
       knows how to distinguish integers from other values! *)
    | "INTEGER" -> Int (sexp_to_int se)
    | "(not ANY)" ->
      Not (parse' (second (sexp_to_list se)))
    | "(if ANY then ANY else ANY)" ->
      If (parse' (second (sexp_to_list se)),
          parse' (fourth (sexp_to_list se)),
          parse' (sixth (sexp_to_list se)))
    | "(ANY SYMBOL ANY)" ->
      let op = match (sexp_to_symbol (second (sexp_to_list se))) with
        | "and" -> And
        | "or" -> Or
        | "+" -> Add
        | _ -> failwith "parse: invalid operator in input" in
      BinOp (op,
             parse' (first (sexp_to_list se)),
             parse' (third (sexp_to_list se)))
    | _ -> failwith "parse: invalid input"
  in
  parse' (Camlrack.sexp_of_string_exn s)

(* And, also as usual, we will define a new [exp]-to-[string] function. *)

(** Converts an [exp] into a [string]. *)
let rec string_of_exp (a : exp) : string =
  let string_of_op (op : binop) : string =
    match op with
    | And -> "and"
    | Or -> "or"
    | Add -> "+"
  in
  match a with
  | T -> "T"
  | F -> "F"
  | Int z -> string_of_int z
  | Not e -> "(not " ^ string_of_exp e ^ ")"
  | If (cond, thn, els) -> "(if " ^ string_of_exp cond ^
                           " then " ^ string_of_exp thn ^
                           " else " ^ string_of_exp els ^ ")"
  | BinOp (o, l, r) -> "(" ^ string_of_op o ^
                       " " ^ string_of_exp l ^
                       " " ^ string_of_exp r ^ ")"

(* For our operational semantics, we need only extend the semantics of
   [bool2.ml] with the [+] operator and revise the definition of E-OpRight to
   reduce its left subterms to any value (rather than only Boolean values) and
   we'll be done:

     ⟪ z3 ⟫ = ⟪ z1 ⟫ + ⟪ z2 ⟫
     -------------------------  E-Add
          (z1 + z2) -> z3

              e -> e'
       ---------------------    E-OpRight
       (v op e) -> (v op e')

   (Note that in the E-Add rule, the [+] on the bottom is actually a distinct
   thing from the [+] on the top. The one on top is mathematical, while the one
   on the bottom is purely syntactic. We could have avoided this awkwardness by
   instead defining our addition operator as, say, [add] and constructed forms
   like [(1 add 3)], but that seems even more awkward than just using [+]
   twice.)

   With that, we're all set! Let's implement the interpreter. First, we'll need
   our conversion functions to get us to and from OCaml. *)

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

(** Converts an [exp] to an OCaml [int]. *)
let ocaml_int_of_exp (a : exp) : int =
  match a with
  | Int z -> z
  | _ -> failwith "ocaml_int_of_int: invalid term"

(** Converts an OCaml [int] to an [exp]. *)
let exp_of_ocaml_int (z : int) : exp = Int z

(* We will also revise our [is_value] function. To do this, we will define two
   separate functions to check whether an expression is a Boolean or an integer,
   then use those to define our value-checking function. *)

(** Determines whether an expression is actually a Boolean value. *)
let is_bool (a : exp) : bool =
  match a with
  | T | F -> true
  | _ -> false

(** Determines whether an expression is actually an integer value. *)
let is_int (a : exp) : bool =
  match a with
  | Int _ -> true
  | _ -> false

(** Determines whether an expression is a value. *)
let is_value (a : exp) : bool =
  is_bool a || is_int a

(* Now we can implement our [step] function. But pay attention: OCaml is going
   to give us a hint about our next discussion topic. *)

(** Takes a single step according to the small-step operational semantics. *)
let rec step (a : exp) : exp =
  (** Converts a syntactic binary operator on Booleans into an OCaml
      function. *)
  let get_bool_op (op : binop) : (bool -> bool -> bool) option =
    match op with
    | And -> Some (&&)
    | Or -> Some (||)
    | _ -> None in
  (** Converts a syntactic binary operator on integers into an OCaml
      function. *)
  let get_int_op (op : binop) : (int -> int -> int) option =
    match op with
    | Add -> Some (+)
    | _ -> None
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
  (* Reducing Boolean binary operations. *)
  | BinOp (op, b1, b2)          (* E-And and E-Or *)
    when is_bool b1 && is_bool b2 ->
    (match get_bool_op op with
     | Some op -> exp_of_ocaml_bool (op (ocaml_bool_of_exp b1) (ocaml_bool_of_exp b2))
     | None -> a)
  (* Reducing integer binary operations. *)
  | BinOp (op, z1, z2)          (* E-Add *)
    when is_int z1 && is_int z2 ->
    (match get_int_op op with
     | Some op -> exp_of_ocaml_int (op (ocaml_int_of_exp z1) (ocaml_int_of_exp z2))
     | None -> a)
  (* Reducing binary operations when there are un-reduced subterms. *)
  | BinOp (op, v, e)            (* E-OpRight *)
    when is_value v ->
    let e' = step e in
    BinOp (op, v, e')
  | BinOp (op, e1, e2) ->       (* E-OpLeft *)
    let e1' = step e1 in
    BinOp (op, e1', e2)
  (* No step! *)
  | _ -> a

(* We will quickly define our [multistep] function and some tests before coming
   back to the interesting thing that has happened here. *)

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
    [ ("3", Int 3)
    ; ("-42", Int (-42))
    ; ("(1 + 3)", Int 4)
    ; ("(1 + T)", BinOp (Add, Int 1, T))
    ; ("(4 or 5)", BinOp (Or, Int 4, Int 5))
    ]

  let max_steps = 5

  let run_test ((input, result) : test) : unit =
    assert ((multistep max_steps (parse input)) = result)

  let run_tests () = List.iter run_test tests
end

(* What's going on here? How come not all of our tests reduce to values this
   time?

   The answer is straightforward: our inputs become "stuck". When a semantics
   does not provide any rules for how to deal with a certain kind of term, terms
   of that kind become "stuck" and cannot make any more progress.

   One solution to this might be to use extra syntax to ensure we cannot
   construct such terms in the first place. However, this would be tedious and
   error-prone, and in some cases may actually be impossible.

   Instead, we will seek to use another tool to rule out programs that are
   syntactically correct but semantically invalid: types.

   The astute observer may have noticed that OCaml didn't let us get around this
   problem easily in the implementation of our [step] function. Previously, we
   had implemented a nested [get_op] helper function to convert our syntactic
   operators into OCaml functions. However, since OCaml is statically typed and
   distinguishes the type of Boolean values [bool] from the type of integer
   values [int], we could not handle all of our operators with the same
   function. Instead, we had to implement two separate functions: [get_bool_op]
   and [get_int_op]. This also means we had to handle the pattern-match case for
   [BinOp] forms with two Boolean subterms separately from the pattern-match
   case for [BinOp] forms with two integer subterms.

   We will next learn about using types to rule out programs that would
   otherwise get stuck. *)
