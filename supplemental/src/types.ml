(** This module defines and explains an interpreter for a language with Boolean
    operations and integers values, extended to add type-checking. **)

open Camlrack
open Camlrack.ListConvenienceFunctions

(* As of [arith.ml], we have defined and implemented a small language with
   Boolean and integer values, with some operators to work on them. However, as
   we left things, there is a problem: there exist some terms that are
   syntactically well-formed, but for which we do not assign any meaning by way
   of semantics. For example, consider the following term:

     (not (1 + T))

   Based on the semantics we've defined previously, we would first need to
   reduce that [(1 + T)] subterm. Unfortunately, there is no semantic rule for
   the form [(z + b)]. The E-Add rule only works for expressions of the form
   [(z1 + z2)].

   Inputs of this nature are said to be "stuck" because there is no meaningful
   way to continue reducing them. With our current set of tools, we have three
   methods to deal with this:

     1. If our evaluator always tries to take a step when the input is not a
        value and simply returns inputs for which we have no semantic rule, our
        evaluator will never terminate.

     2. We can instead just return the inputs when we attempt to take a step and
        make no progress.

     3. We can raise an error when no semantic rule is found for a given input.

   However, there is a better way to solve this problem than any of this
   options. Instead of dealing with stuck terms as they arise, we can extend our
   language with a [type system]. I like Benjamin Pierce's definition of the
   term, though it may not have sufficient meaning for you just yet:

     A type system is a tractable syntactic method for proving the absence of
     certain program behaviors by classifying phrases according to the kinds of
     values they compute.
     --- Benjamin C. Pierce, "Types and Programming Languages" (2002)

   In other words, a type system is a set of rules that restrict the set of
   valid inputs that we can feed to our interpreter. The type system will let us
   say that terms like [(1 + T)] are simply not valid, and so we do not evaluate
   them. Even better than that, however, is the fact that our type system will
   be able to tell us in advance that [(not (1 + T))] as a whole is invalid,
   meaning we can get guarantees about our program's ability to reduce before we
   ever run it. This allows us to completely rule out certain programs based on
   undesirable behaviors they may exhibit.

   To get started, we will recreate the language from [arith.ml], except we are
   going to (temporarily) remove the conditional expression form, [if]. The
   reasoning for this will be explained later.

     b ::= T | F

     z ::= m, where m ∈ ℤ

     v ::= b | z

     binop ::= and | or | +

     e ::= v
        |  (not e)
        |  (e binop e)

   Now we will simply copy all the definitions and implementations from
   [arith.ml], leaving out anything involving the [if] expressions. The new
   type-checking portion will appear after that.

   NOTE: There is one additional change to the code below: the [parse] function
   now returns an [exp option] instead of a bare [exp]. This will come in handy
   later on. *)

(** The type of expressions. *)
type exp = | T | F | Int of int | Not of exp | BinOp of binop * exp * exp

(** The type of binary operators. *)
and binop = | And | Or | Add

(** Parses a [string] to an [exp], if possible. Raises an exception on
    failure. *)
let parse (s : string) : exp option =
  let rec parse' (se : sexp) : exp =
    match%spat se with
    | "T" -> T
    | "F" -> F
    | "INTEGER" -> Int (sexp_to_int se)
    | "(not ANY)" ->
      Not (parse' (second (sexp_to_list se)))
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
  try Some (parse' (Camlrack.sexp_of_string_exn s))
  with Failure _ -> None

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
  | BinOp (o, l, r) -> "(" ^ string_of_op o ^
                       " " ^ string_of_exp l ^
                       " " ^ string_of_exp r ^ ")"

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

(* At last, we come to type-checking. Type-checking is a form of [static
   analysis], so let's first talk about what that means.

     analysis: a function that takes a program (or expression) as input and
         answers a question about that program.

     static analysis: an analysis that takes place without evaluating the
         program it is given as input.

   So our type-checking function will need to take a program as input, and it
   will return a Boolean result where [true] means the program "type-checks"/"is
   type-correct" and [false] means the opposite.

   Our first step is to define a syntactic language for types. Typically, you
   need a type for each variety of primitive value your language supports, and
   then you add extra types on top of those as needed. We don't have any need
   for complex types yet, so we can define our types very simply:

     T ::= B
        |  I

   Let's go ahead an implement that in code before we proceed. *)

(** The type of types for our language. *)
(* NOTE: we've named this OCaml type [ty]. OCaml will not allow us to use the
   full name [type] because that is a keyword in OCaml. Other options might be
   [_type], [typ], or [t], but I like [ty] the best. *)
type ty =
  | B
  | I

(* Previously, we established that type-checking is a static analysis, and that
   a static analysis is a function that takes a program (or expression) as input
   and answers a question about that program without evaluating it. We will
   implement this functionality as a function in OCaml named [typecheck], which
   will take an expression [e] as an argument and will return the type of that
   expression.

   So, how do we go about specifying the rules for a type-checking function? If
   you were guessing "kind of like operational semantics", you'd be absolutely
   right!

   Up until now, we have discussed two forms of binary reduction relation: the
   small-step reduction relation [->] and the multiple-small-step reduction
   relation [->*]. For type-checking, we will introduce the typing relation,
   [:].

   First, we'll write a couple axioms, as those are the most straightforward
   rules:

     -----  T-B
     b : B

     -----  T-I
     z : I

   These rules say: "any Boolean value [b] has type [B]" and "any integer value
   [z] has type [I]". This may seem obvious, but it is important that we always
   write down explicit rules for everything when we are trying to provide a
   formal definition of a language.

   Now that we have these basic rules, we can add rules for our other forms of
   expressions:

          e : B
       -----------     T-Not
       (not e) : B

     e1 : B    e2 : B
     ----------------  T-And
      (e1 and e2) : B

     e1 : B    e2 : B
     ----------------  T-Or
      (e1 or e2) : B

     e1 : I    e2 : I
     ----------------  T-Add
       (e1 + e2) : I

   We can read these rules the same way we read the rules in an operational
   semantics. For example, T-Add says "an addition expression [(e1 + e2)] has
   the type [I] if the first subterm [e1] has type [I] and the second subterm
   [e2] has type [I]".

   Now, we can implement our [typecheck] function using these rules in much the
   same way we implement our [step] function based on the operational semantics.
   We'll have [typecheck] return a [ty option] as a result: a [Some] indicates
   that the expression has a type and the type is the contained valued, while a
   [None] means the expression does not have a valid type. (This lets us avoid
   raising errors, which is a nice property sometimes.) *)

(** Determines the type of an expression, if it has one. *)
let rec typecheck (a : exp) : ty option =
  match a with
  (* Type-checking primitive values. *)
  | T | F -> Some B
  | Int _ -> Some I
  (* Type-checking Boolean negation. *)
  | Not e ->
    (match typecheck e with
     | Some B -> Some B
     | _ -> None)
  (* Type-checking binary Boolean operations. *)
  | BinOp (And, e1, e2) | BinOp (Or, e1, e2) ->
    (match typecheck e1, typecheck e2 with
     | (Some B, Some B) -> Some B
     | _ -> None)
  (* Type-checking binary integer operations. *)
  | BinOp (Add, e1, e2) ->
    (match typecheck e1, typecheck e2 with
     | (Some I, Some I) -> Some I
     | _ -> None)

(* And that's it --- that's the whole type-checking function!

   Of course, this language is incredibly simple, so its type-checker is also
   very simple. However, the complexity of type-checking can increase rapidly
   when your language becomes more complex. We'll see that soon enough!

   For the moment, I suggest you consider the human factors of this language
   implementation. Namely, a user must [parse] a term, [typecheck] it, and only
   then can they [multistep]-evaluate it. What a pain!

   Let's add a nice wrapper function, named [eval]. Our [eval] function will
   take a string as an argument, attempt to parse the string to an expression,
   attempt to type-check that expression, and then evaluate the expression.
   We'll keep our error-handling to a minimum, simply returning [None] if
   anything at all goes wrong in that pipeline. *)

(** The number of steps taken by the [eval] function when it is able to evaluate
    its input. *)
let number_of_steps = 5

(** Parses a given string, type-checks the resulting expression, and evaluates
    the expression if type-checking is successful. Returns the evaluated form of
    the expression if there are no errors. *)
let eval (s : string) : exp option =
  let e = parse s in
  let t = Option.map typecheck e in
  Option.map (fun _ -> multistep number_of_steps (Option.get e)) t

(** This module provides some test functions for the above interpreter. If you
    have the parent module open in utop, you can do [Tests.run_tests ();;] to
    execute all the tests. If all tests are successful, you will get back the
    unit value. If any test fails, an assertion error will be raised. *)
module Tests = struct
  type test = (string * (ty * exp) option)

  let tests : test list =
    [ ("3", Some (I, Int 3))
    ; ("T", Some (B, T))
    ; ("(1 + 1)", Some (I, Int 2))
    ; ("(T and F)", Some (B, F))
    ; ("(1 + T)", None)
    ; ("(not (1 + T))", None)
    ]

  let max_steps = 5

  let run_test ((input, result) : test) : unit =
    match parse input with
    | None -> failwith ("run_test: could not parse input '" ^ input ^ "'")
    | Some e ->
      (match result with
       | None -> assert (typecheck e = None)
       | Some (expected_type, expected_result) ->
         assert (typecheck e = Some expected_type &&
                 multistep max_steps e = expected_result &&
                 let eres = eval input in
                 Option.is_some eres && Option.get eres = expected_result))

  let run_tests () = List.iter run_test tests
end
