(** February 14, 2022 *)
open Camlrack
open Camlrack.ListConvenienceFunctions

(* This code is a direct continuation of the code in [lec01.ml]. *)

type exp =
  | T | F
  | Integer of int
  | UnaryOp of op1 * exp
  | BinaryOp of op2 * exp * exp

and op1 =
  | Not
  | IsZero

and op2 =
  | And
  | Or
  | Plus

let example_exp = BinaryOp (And, T, BinaryOp (Plus, Integer 1, Integer 2))

let parse (s : string) : exp =
  let rec parse' (se : sexp) : exp =
    match%spat se with
    | "T" -> T
    | "F" -> F
    | "INTEGER" -> Integer (sexp_to_int se)
    | "(SYMBOL ANY)" ->
      let op = match (sexp_to_symbol (first (sexp_to_list se))) with
        | "not" -> Not
        | "iszero" -> IsZero
        | _ -> failwith "parse: not a valid unary operator" in
      UnaryOp (op, parse' (second (sexp_to_list se)))
    | "(ANY SYMBOL ANY)" ->
      let op = match (sexp_to_symbol (second (sexp_to_list se))) with
        | "and" -> And
        | "or" -> Or
        | "+" -> Plus
        | _ -> failwith "parse: not a valid binary operator" in
      BinaryOp (op,
                parse' (first (sexp_to_list se)),
                parse' (third (sexp_to_list se)))
    | _ -> failwith "parse: invalid expression"
  in
  parse' (Camlrack.sexp_of_string_exn s)

let is_bool (a : exp) : bool =
  match a with
  | T | F -> true
  | _ -> false

let ocaml_bool_of_bool (a : exp) : bool =
  match a with
  | T -> true
  | F -> false
  | _ -> failwith "ocaml_bool_of_bool: not a Boolean"

let bool_of_ocaml_bool (b : bool) : exp =
  match b with
  | true -> T
  | false -> F

let is_int (a : exp) : bool =
  match a with
  | Integer _ -> true
  | _ -> false

let ocaml_int_of_int (a : exp) : int =
  match a with
  | Integer z -> z
  | _ -> failwith "ocaml_int_of_int: not an integer"

let int_of_ocaml_int (z : int) : exp =
  Integer z

let is_value (a : exp) : bool =
  is_bool a || is_int a

let rec step (a : exp) : exp =
  match a with
  | UnaryOp (Not, e) ->
    (match e with
     | T -> F
     | F -> T
     | _ ->
       let e' = step e in
       UnaryOp (Not, e'))
  | UnaryOp (IsZero, e) ->
    (match e with
     | Integer 0 -> T
     | Integer _ -> F
     | _ ->
       let e' = step e in
       UnaryOp (IsZero, e'))
  | BinaryOp (And, b1, b2)
    when is_bool b1 && is_bool b2 ->
    bool_of_ocaml_bool (ocaml_bool_of_bool b1 && ocaml_bool_of_bool b2)
  | BinaryOp (And, b, e)
    when is_bool b ->
    let e' = step e in
    BinaryOp (And, b, e')
  | BinaryOp (And, e1, e2) ->
    let e1' = step e1 in
    BinaryOp (And, e1', e2)
  | BinaryOp (Or, b1, b2)
    when is_bool b1 && is_bool b2 ->
    bool_of_ocaml_bool (ocaml_bool_of_bool b1 || ocaml_bool_of_bool b2)
  | BinaryOp (Or, b, e)
    when is_bool b ->
    let e' = step e in
    BinaryOp (Or, b, e')
  | BinaryOp (Or, e1, e2) ->
    let e1' = step e1 in
    BinaryOp (Or, e1', e2)
  | BinaryOp (Plus, z1, z2)
    when is_int z1 && is_int z2 ->
    int_of_ocaml_int (ocaml_int_of_int z1 + ocaml_int_of_int z2)
  | BinaryOp (Plus, z, e)
    when is_int z ->
    let e' = step e in
    BinaryOp (Plus, z, e')
  | BinaryOp (Plus, e1, e2) ->
    let e1' = step e1 in
    BinaryOp (Plus, e1', e2)
  | _ -> failwith "no semantic rule for input"

let rec multistep (k : int) (a : exp) : exp =
  if is_value a
  then a
  else
    match k with
    | 0 -> a
    | _ ->
      let a' = step a in
      multistep (k - 1) a'

type ty =
  | Bool
  | Int

let rec typecheck (a : exp) : ty =
  match a with
  (* T-Bool *)
  | T | F -> Bool
  (* T-Int *)
  | Integer _ -> Int
  (* T-Not *)
  | UnaryOp (Not, e) ->
    if typecheck e = Bool
    then Bool
    else failwith "argument to 'not' not a Boolean"
  (* T-IsZero *)
  | UnaryOp (IsZero, e) ->
    if typecheck e = Int
    then Bool
    else failwith "argument to 'iszero' not an integer"
  (* T-And and T-Or *)
  | BinaryOp (And, e1, e2) | BinaryOp (Or, e1, e2) ->
    if typecheck e1 = Bool && typecheck e2 = Bool
    then Bool
    else failwith "one or more arguments not Boolean values"
  (* T-Plus *)
  | BinaryOp (Plus, e1, e2) ->
    if typecheck e1 = Int && typecheck e2 = Int
    then Int
    else failwith "one or more arguments not integer values"

let eval (s : string) : exp =
  let e = parse s in
  let _ = typecheck e in
  multistep 7 e
