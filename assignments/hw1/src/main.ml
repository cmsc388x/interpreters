open Camlrack
open Camlrack.ListConvenienceFunctions

(** The type of expressions. *)
type exp =
  | T | F
  | Integer of int
  | Not of exp
  | IsZero of exp
  | BinOp of binop * exp * exp

(** The type of binary operators. *)
and binop =
  | And | Or
  | Add

(** Parses a [string] to an [exp], if possible. Raises an exception on
    failure. *)
let parse (s : string) : exp option =
  let rec parse' (se : sexp) : exp =
    match%spat se with
    | "T" -> T
    | "F" -> F
    | "INTEGER" -> Integer (sexp_to_int se)
    | "(not ANY)" ->
      Not (parse' (second (sexp_to_list se)))
    | "(iszero ANY)" ->
      IsZero (parse' (second (sexp_to_list se)))
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
  | Integer z -> string_of_int z
  | Not e -> "(not " ^ string_of_exp e ^ ")"
  | IsZero e -> "(iszero " ^ string_of_exp e ^ ")"
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
  | Integer z -> z
  | _ -> failwith "ocaml_int_of_int: invalid term"

(** Converts an OCaml [int] to an [exp]. *)
let exp_of_ocaml_int (z : int) : exp = Integer z

(** Determines whether an expression is actually a Boolean value. *)
let is_bool (a : exp) : bool =
  match a with
  | T | F -> true
  | _ -> false

(** Determines whether an expression is actually an integer value. *)
let is_int (a : exp) : bool =
  match a with
  | Integer _ -> true
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
  (* Reducing [iszero]. *)
  | IsZero (Integer 0) -> T     (* E-IsZeroTrue *)
  | IsZero (Integer _) -> F     (* E-IsZeroFalse *)
  | IsZero e ->                 (* E-IsZeroStep *)
    let e' = step e in
    IsZero e'
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

(** The type of types for our language. *)
type ty =
  | Bool
  | Int

(** Determines the type of an expression, if it has one. *)
let rec typecheck (a : exp) : ty option =
  match a with
  (* Type-checking primitive values. *)
  | T | F -> Some Bool
  | Integer _ -> Some Int
  (* Type-checking Boolean negation. *)
  | Not e ->
    (match typecheck e with
     | Some Bool -> Some Bool
     | _ -> None)
  (* Type-checking integer-is-zero. *)
  | IsZero e ->
    (match typecheck e with
     | Some Int -> Some Bool
     | _ -> None)
  (* Type-checking binary Boolean operations. *)
  | BinOp (And, e1, e2) | BinOp (Or, e1, e2) ->
    (match typecheck e1, typecheck e2 with
     | (Some Bool, Some Bool) -> Some Bool
     | _ -> None)
  (* Type-checking binary integer operations. *)
  | BinOp (Add, e1, e2) ->
    (match typecheck e1, typecheck e2 with
     | (Some Int, Some Int) -> Some Int
     | _ -> None)

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
    [ ("3", Some (Int, Integer 3))
    ; ("T", Some (Bool, T))
    ; ("(1 + 1)", Some (Int, Integer 2))
    ; ("(T and F)", Some (Bool, F))
    ; ("(iszero 0)", Some (Bool, T))
    ; ("(iszero 42)", Some (Bool, F))
    ; ("(1 + T)", None)
    ; ("(not (1 + T))", None)
    ; ("(iszero T)", None)
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
