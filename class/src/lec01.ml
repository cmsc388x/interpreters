(** February 9, 2022 *)
open Camlrack
open Camlrack.ListConvenienceFunctions

(* To use this file interactively in utop, open your terminal and change
   directory (`cd`) to the top of the `interpreters` repository code. (This is
   the directory with the `dune-project` and `.gitignore` files, a few levels
   above where this file is defined.) Then, do:

     $ dune utop class/src

   This should start utop, at which point you can do:

     # open Class.Lec01;;

   Now, you'll be able to access types and functions defined in this file. *)

type exp =
  | T | F
  | Integer of int
  | UnaryOp of op1 * exp
  | BinaryOp of op2 * exp * exp

and op1 =
  | Not

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

let rec step (a : exp) : exp =
  match a with
  | UnaryOp (Not, e) ->
    (match e with
     | T -> F
     | F -> T
     | _ ->
       let e' = step e in
       UnaryOp (Not, e'))
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
  (* TODO: This is where we left off...! *)
  (* ... *)
  | _ -> a
