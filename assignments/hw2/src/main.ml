(**
                           ╔════════════════════════╗
                           ║                        ║
                           ║  CMSC 388X Homework 2  ║
                           ║                        ║
                           ╚════════════════════════╝

    NOTE: This file makes use of Unicode characters.

    File organization (search through the file to jump around):

        * DEBUG MODE DEFINITIONS
        * TYPE DEFINITIONS
        * SIMPLE MAPPINGS
        * STRING RENDERING FUNCTIONS
        * PARSING
        * TYPE-CHECKING
        * CAPTURE-AVOIDING SUBSTITUTION
        * EVALUATION
        * TESTS

    This assignment is split into four parts.

    PART 1: Complete the base implementation of the typed lambda calculus.

        We have implemented a typed lambda calculus. This lambda calculus is
        multary, meaning lambdas can take multiple arguments at one time. The
        types we support at the beginning are [Bool], [Int], and [Arrow] (where
        [Arrow] is the type of functions).

        Unfortunately, some of the implementation was deleted! Your job is to
        re-implement the missing parts. (Fortunately, though, the trickiest
        parts were kept intact. Whew!)

        You'll find the missing sections by looking for comments beginning with
        [TODO PART 1].

    PART 2: Implement additional primitive functions.

        Some primitive functions are implemented, but we want more! You'll find
        the relevant locations to add your definitions by looking for comments
        beginning with [TODO PART 2].

        The functions you should implement are:

            * [iszero] with constructor [IsZero], which takes an integer and
              reduces to a Boolean value representing whether that integer was
              zero.

            * [or] with constructor [Or], which takes two Booleans and reduces
              to a Boolean value representing their logical disjunction.

            * [-] with constructor [Sub], which takes two integers and reduces
              to an integer representing their difference.

            * [*] with constructor [Mul], which takes two integers and reduces
              to an integer representing their product.

    PART 3: Implement two extensions that do not require modifying types.

        These extensions should not be handled like functions, so they cannot be
        added in the same way as the primitive forms in Part 2. Instead, their
        specific rules need to be handled. Look for comments marked with the
        text [TODO PART 3].

        NOTE: You will need to update [get_bound_variables] and [substitute] for
        both of these extensions. Your changes to these functions should be
        fairly straightforward, since you need only call the functions
        recursively. Since we didn't talk about either of these functions in
        class, we describe the process below.

        If we imagine an arbitrary [exp] constructor [C] that takes [n] [exp]s
        and one [exp list] argument (like [C (exp_1, ..., exp_n, exps)]), we
        would need to do the following:

            * [get_bound_variables] code should create a new list that contains
              the bound variables from each of the sub-expressions in order. You
              may find OCaml's [@] operator useful: it appends two lists to one
              another. So, for our arbitrary [exp] constructor from above, we
              need to add a case that looks like:

                  | C (exp_1, ..., exp_n, exps) ->
                    get_bound_variables exp_1 @ ... @ get_bound_variables exp_n
                    @ (List.concat_map get_bound_variables exps)

            * [substitute] code should re-create the constructor we are given,
              but with the substitution performed in each of the the sub-
              expressions. So for our arbitrary [exp] constructor:

                  | C (exp_1, ..., exp_n, exps) ->
                    C (substitute arg for_name exp_1,
                       ...,
                       substitute arg for_name exp_n,
                       List.map (substitute arg for_name) exps)

        The two extensions you must implement are:

        1. [if] with constructor [If], representing a conditional expression. It
           takes three arguments: a Boolean and two sub-expressions. If the
           Boolean reduces to [Bool true], the [if] should reduce to the second
           sub-expression. Otherwise, it should reduce to the third.

           NOTE: The [if] form should not reduce its second and third
           sub-expressions. Only reduce the first sub-expression, then step to
           the un-reduced second or third sub-expression as needed.

           The typing rule for [if] looks like this:

               Γ ⊢ e_c : Bool    Γ ⊢ e_t : T    Γ ⊢ e_f : T
               --------------------------------------------  T-If
                        Γ ⊢ (if e_c e_t e_f) : T_r

           and the small-step reduction rules look like this:

                            e_c ⟶ e_c'
               --------------------------------------  E-IfStep
               (if e_c e_t e_f) ⟶ (if e_c' e_t e_f)

               -----------------------  E-IfTrue
               (if #t e_t e_f) ⟶ e_t

               -----------------------  E-IfFalse
               (if #f e_t e_f) ⟶ e_f

        2. [fix] with constructor [Fix], a primitive form that takes a lambda as
           argument and performs a special substitution that allows for
           simulating a recursive binding.

           The typing rule for [fix] looks like this:

               Γ ⊢ e : ((T) -> T)
               ------------------  T-Fix
                Γ ⊢ (fix e) : T

           and the small-step reduction relation looks like this:

                     e ⟶ e'
               --------------------  E-FixStep
               (fix e) ⟶ (fix e')

               ----------------------------------------------------  E-Fix
               (fix (λ ((x : T)) e)) ⟶ e[x/(fix (λ ((x : T)) e))]

           Hint: use the [substitute] function to perform substitution.

    PART 4: Extend the language to include indexed records.

        In class we discussed the generalized form of product types, called
        records. Records allow you to combine multiple expressions into a single
        expression. (Tuples are a specific kind of record.) For our records, we
        would like to support construction of arbitrary-length records as well
        as projection to any of those fields.

        NOTE: There is only one [TODO PART 4] comment, which corresponds to task
        4.7. The rest of what you should do is described below, and you must
        find where to modify code.

        1. Add a [Record] constructor to the definitions of [ty], [value], and
           [exp]. (You will need all three, since records can also be values if
           their sub-components are fully reduced.) Give it appropriate fields
           to suit its needs.

        2. Extend the [string_of_type], [string_of_value], and [string_of_exp]
           functions to handle the new forms.

        3. Extend the [parse] function to handle record construction and
           projection using the syntax [(record e ...)] for construction and
           [(proj i e)] for projection, where [i] is a positive integer. Note
           that this integer should not be an [Int] in the language, because we
           need to be able to read it during type-checking. (I.e., you will have
           to check that the integer [i] is valid during parsing!)

        4. Extend the [typecheck] function to handle records and projections
           according to the following rules. (We use the syntax [(T; T ...)] to
           write the type of records in these rules to make it visually distinct
           from record expressions, but this syntax cannot be represented in
           Camlrack. Therefore, you may simply use [(record T ...)] for your
           record type syntax, or some other syntax that you enjoy.)

                  Γ ⊢ e_i : T_i  for all i ∈ [1 ... n]
               ------------------------------------------  T-Rec
               Γ ⊢ (record e_1 ... e_n) : (T_1; ...; T_n)

               Γ ⊢ e : (T_1; ...; T_n)  and i ∈ [1 ... n ]
               -------------------------------------------  T-Proj
                           Γ ⊢ (proj i e) : T_i

        5. Extend the [get_bound_variables] and [substitute] functions. These
           should only require that you add rules for the [exp] forms you've
           added, and you ought to just call the functions recursively in a
           manner similar to the other forms already present. These functions
           should not require significant efforts on your part.

        6. Extend the [step] function to handle records and projections
           according to the following rules.

                                      e_1 ⟶ e_1'
               ----------------------------------------------------------  E-Rec
               (record v ... e_1 e_2 ...) ⟶ (record v ... e_1' e_2 ...)

                        e ⟶ e'
               --------------------------  E-ProjStep
               (proj i e) ⟶ (proj i e')

                        when i ∈ [1 ... n]
               -------------------------------------  E-Proj
               (proj i (record v_1 ... v_n)) ⟶ v_i

        7. Add tests in the [part4_tests] list in the [Tests] submodule! (You
           will need to fix the first test, since the correct result is
           dependent on how you implement your records.)

   If you have any questions about anything you find confusing, misleading, or
   whatever else, please either post about it on the class Discord server or
   contact Pierce or Justin to ask for clarification. *)
open Camlrack
open Camlrack.ListConvenienceFunctions

(*
                          ╔══════════════════════════╗
                          ║                          ║
                          ║  DEBUG MODE DEFINITIONS  ║
                          ║                          ║
                          ╚══════════════════════════╝

   NOTE: You don't need to read this section unless you want to know more about
   the functions defined here. This is just to be helpful when debugging. **)

(** These provide functionality for debugging. To use these, first open the Hw2
    module by doing [open Hw2.Main;;], and then you can enable the [debug] flag
    with either [debug := Errors;;] or [debug := Warnings;;]. Only some
    functions are affected, and it's not very sophisticated, but it could help a
    bit!

    You will also find some special functions in the [Tests] submodule for
    running the tests with debugging automatically enabled for you.

    NOTE: The [dwarn] and [derror] functions each take a thunk as argument, that
    is, a function of zero arguments. This is so you can pass an expression that
    might have a high computational complexity, and it will only be used if
    needed. Otherwise, it will not be evaluated. You can easily make a thunk
    using the [delay] function.

    NOTE: I've already added what I think are basically sufficient uses of
    [dwarn] and [derror] in the code. *)
type debug_level = Off | Errors | Warnings
let debug = ref Off
let dwarn t = if !debug = Warnings then print_endline (t ()) else ()
let derror t = if (!debug = Warnings || !debug = Errors) then print_endline (t ()) else ()
let delay x = fun () -> x

(*
                             ╔════════════════════╗
                             ║                    ║
                             ║  TYPE DEFINITIONS  ║
                             ║                    ║
                             ╚════════════════════╝

   The following section defines all the major types we'll use. *)

(** We give variables a type alias so it's easier to understand our other types.
    This isn't necessary, but it's a nice way to improve code legibility! *)
type variable = string

(** The type of types. We define it earlier than we did before because it's used
    in the lambda values! *)
type ty =
  | Bool
  | Int
  | Arrow of (ty list) * ty

(** The type of values. Previously, we incorporated our values directly into our
    expression type and wrote an [is_value] function to check if an expression
    is a value. This time, we've implemented values as a separate type, and we
    inject values into the expressions using a specialized constructor [Val].
    This makes some parts of the code easier to manage, but also adds a bit of
    complexity. Everything is a trade-off!

    Values and expressions are mutually recursive types, though. This is because
    our lambda values contain un-evaluated expressions as their bodies. Mutually
    recursive types in OCaml are expressed by defining the first type with the
    [type] keyword, and connecting the other types using [and] instead of
    [type]. Mutually recursive types are very powerful, but are also a pathway
    to very complicated code in some cases. For example, you will notice that in
    the rest of this file whenever we want to write a function to handle [exp]s
    we will also need a mutually recursive (or inner) function to handle
    [value]s! *)
type value =
  (* Our lambdas are multary (capable of taking 0+ arguments at once), so we
     encode their parameters as a [list]. They also require explicit type
     annotations to make life easier during type-checking. *)
  | Lam of ((variable * ty) list) * exp
  (* Our primitive values are straightforward. Notice OCaml allows us to use the
     same constructor names for our [value]s as we did in the [ty]pes! This is
     nice in some ways because we may have a good reason to use the same name in
     multiple places, but it can also make reading the code (as a human) a bit
     trickier. *)
  | Bool of bool
  | Int of int
  (* We also have some primitive functions. *)
  | Not | And | Add
  (* TODO PART 2: Add constructors for the needed primitive functions. *)

(** The type of expressions. *)
and exp =
  | Val of value
  | Var of variable
  (* TODO PART 3 *)
  | App of exp * (exp list)

(*
                             ╔═══════════════════╗
                             ║                   ║
                             ║  SIMPLE MAPPINGS  ║
                             ║                   ║
                             ╚═══════════════════╝

   By defining these maps, we can move all of our (type/value)-string pairings
   to a single place. This reduces the likelihood of introducing a typo
   somewhere in our program, but it comes at the cost of code complexity and
   reduced guarantees (since we now will no longer get exhaustiveness checks of
   our datatypes). **)

(** A mapping from the primitive types to strings. *)
let simple_types_to_strings : (ty * string) list =
  [ (Bool, "Bool")
  ; (Int, "Int")
  ]

(** A mapping from strings to the primitive types. *)
let strings_to_simple_types = List.map (fun (a, b) -> (b, a)) simple_types_to_strings

(** A mapping from the trivial primitive values to strings. *)
let simple_values_to_strings : (value * string) list =
  [ (Bool true, "#t")
  ; (Bool false, "#f")
  ; (Not, "not")
  ; (And, "and")
  ; (Add, "+")
    (* TODO PART 2: It's probably easiest if you add similar pairs for the new
       primitive functions here. This will add them to the parser. *)
  ]

(** A mapping from strings to the trivial primitives values. *)
let strings_to_simple_values = List.map (fun (a, b) -> (b, a)) simple_values_to_strings

(** A mapping from simple values to their types. *)
let simple_values_to_types : (value * ty) list =
  [ (Bool true, Bool)
  ; (Bool false, Bool)
  (* TODO PART 1: Add the remaining type definitions for the missing simple
     values. *)
  ; (Not, Arrow ([Bool], Bool))
  (* TODO PART 2: It's probably easiest if you add similar pairs for the new
     primitive functions here. This will add them to the type-checker. *)
  ]

(*
                        ╔══════════════════════════════╗
                        ║                              ║
                        ║  STRING RENDERING FUNCTIONS  ║
                        ║                              ║
                        ╚══════════════════════════════╝

   These are useful in debugging and in formatting outputs. **)

(** Converts a [ty]pe to a [string]. *)
let rec string_of_type (t : ty) : string =
  match t with
  | Arrow (pts, rt) ->
    let ptss = List.map string_of_type pts in
    let rts = string_of_type rt in
    "((" ^ String.concat " " ptss ^ ") -> " ^ rts ^ ")"
  | _ ->
    (match List.assoc_opt t simple_types_to_strings with
     | Some s -> s
     | None -> failwith "string_of_type: not a valid type")

(** Converts a [value] to a [string]. *)
let rec string_of_value (v : value) : string =
  match v with
  | Lam (ps, b) ->
    let pss = List.map (fun (x, t) -> "(" ^ x ^ " : " ^ string_of_type t ^ ")") ps in
    let bs = string_of_exp b in
    "(lambda (" ^ String.concat " " pss ^ ") " ^ bs ^ ")"
  | Int z -> string_of_int z
  | _ ->
    (match List.assoc_opt v simple_values_to_strings with
     | Some s -> s
     | None -> failwith "string_of_value: not a valid value")
(** Converts an [exp] to a [string]. *)
and string_of_exp (e : exp) : string =
  match e with
  | Val v -> string_of_value v
  | Var x -> x
  (* TODO PART 3 *)
  | App (f, args) ->
    let fs = string_of_exp f in
    let argss = String.concat " " (List.map string_of_exp args) in
    "(" ^ fs ^ " " ^ argss ^ ")"

(*
                                 ╔═══════════╗
                                 ║           ║
                                 ║  PARSING  ║
                                 ║           ║
                                 ╚═══════════╝
*)

(** Attempts to convert a [string] to an [exp], if possible. *)
let parse (s : string) : exp option =
  dwarn (delay ("parsing string: '" ^ s ^ "'"));
  (** Parses an S-expression representing a type to a [ty]pe. Throws an error if
      the S-expression does not represent a type. *)
  let rec parse_type (se : sexp) : ty =
    dwarn (delay ("  parsing type: '" ^ render_string_of_sexp se ^ "'"));
    match%spat se with
    | "SYMBOL" ->
      (match List.assoc_opt (sexp_to_symbol se) strings_to_simple_types with
       | Some t -> t
       | None -> failwith ("  parse: failed to parse simple type '" ^ render_string_of_sexp se ^ "'"))
    | "((ANY ...) -> ANY)" ->
      Arrow (List.map parse_type (sexp_to_list (first (sexp_to_list se))),
             parse_type (third (sexp_to_list se)))
    | _ -> failwith ("  parse: not a type: '" ^ render_string_of_sexp se ^ "'") in
  (** Parses an S-expression representing a type annotation in a lambda form to
      a pair of the [variable] and [ty]pe. The shape assumptions are safe
      because this function is only called by [parse'], which has already
      checked the shape of the input S-expression. *)
  let parse_annotation (se : sexp) : variable * ty =
    let name = sexp_to_symbol (first (sexp_to_list se)) in
    let annot = parse_type (third (sexp_to_list se)) in
    (name, annot) in
  (** Parses an S-expression to an [exp]. Throws an error if unsuccessful. *)
  let rec parse' (se : sexp) : exp =
    dwarn (delay ("  parsing sub-string: '" ^ render_string_of_sexp se ^ "'"));
    match%spat se with
    (* Non-trivial primitive values. *)
    | "INTEGER" -> Val (Int (sexp_to_int se))
    (* Trivial primitive values and variables. *)
    | "SYMBOL" ->
      let sym = sexp_to_symbol se in
      (match List.assoc_opt sym strings_to_simple_values with
       | Some v -> Val v
       | None -> Var sym)
    (* Lambda forms. We allow a special-cased single-argument lambda form to
       skip the extra set of parentheses as a convenience. *)
    | "(lambda ((SYMBOL : ANY) ...) ANY)" ->
      let params = List.map parse_annotation (sexp_to_list (second (sexp_to_list se))) in
      (* We do not allow lambda to bind the same variable multiple times in a
         single declaration, and we check for this during parsing.contents

         NOTE: This invariant is assumed by [substitute]. *)
      let rec assert_no_duplicates remaining_params =
        match remaining_params with
        | x::y::ps ->
          if x = y
          then failwith ("parse: duplicate variable binding '" ^ x ^ "' in function definition")
          else assert_no_duplicates (y::ps)
        | _ -> Val (Lam (params,
                         parse' (third (sexp_to_list se)))) in
      assert_no_duplicates (List.sort compare (List.map fst params))
    | "(lambda (SYMBOL : ANY) ANY)" ->
      Val (Lam ([parse_annotation (second (sexp_to_list se))],
                parse' (third (sexp_to_list se))))
    (* TODO PART 3 *)
    (* Application. *)
    | "(ANY ANY ...)" ->
      App (parse' (first (sexp_to_list se)),
           List.map parse' (rest (sexp_to_list se)))
    (* Anything else is undefined! *)
    | _ -> failwith ("parse: invalid input: '" ^ render_string_of_sexp se ^ "'")
  in
  (* In regular operation, this function will simply return [None] if the parse
     is unsuccessful. In [debug] mode, however, it will print a bit more
     information! *)
  try Some (parse' (sexp_of_string_exn s))
  with Failure m -> derror (delay m); None

(*
                              ╔═════════════════╗
                              ║                 ║
                              ║  TYPE-CHECKING  ║
                              ║                 ║
                              ╚═════════════════╝
*)

(** The type environment maps variables to types. This is used during type-
    checking. The type environment is usually named Γ (that is the uppercase
    Greek letter gamma), but we will use "g" instead. *)
type tenv = (variable * ty) list

(** Determines the type of an expression, if it has one. *)
let typecheck (e : exp) : ty option =
  (* The design here is a little different. In [step], we use call-by-value
     substitution, but in [typecheck]'s internal functions we use call-by-name.
     This works out fine because types do not need to be evaluated, so the
     behavior is equivalent, but it's easier (in my opinion) to write this kind
     of variable-handling than substitution. It requires passing around a type
     environment ([tenv]) that maps variables to their types, but this is a
     small overhead. *)
  (** Determines the type of a [value]. *)
  let rec typecheck_value (v : value) (g : tenv) : ty =
    match v with
    | Lam (ps, b) ->
      let g' = List.fold_left (fun g p -> p::g) g ps in
      Arrow (List.map snd ps, typecheck_exp b g')
    | Int _ -> Int
    | _ ->
      (match List.assoc_opt v simple_values_to_types with
       | Some t -> t
       | None -> failwith ("typecheck: no type for value: '" ^ string_of_value v ^ "'"))
  (** Determines the type of an [exp]. *)
  and typecheck_exp (e : exp) (g : tenv) : ty =
    dwarn (delay ("typechecking..." ^
                   "\n  e: " ^ string_of_exp e ^
                   "\n  g: [" ^ String.concat "; "
                     (List.map (fun (x, t) -> "(" ^ x ^ ", " ^ string_of_type t ^ ")") g) ^ "]"));
    match e with
    | Val v -> typecheck_value v g
    | Var x ->
      (match List.assoc_opt x g with
       | Some t -> t
       | None -> failwith ("typecheck: invalid reference to free variable '" ^ x ^ "'"))
    (* TODO PART 3 *)
    | App (f, args) ->
      (* We require applications to have exactly as many arguments as there are
         parameters in the function being applied. *)
      (match (typecheck_exp f g, List.map (fun arg -> typecheck_exp arg g) args) with
       | (Arrow (tparams, tbody)), targs ->
         if List.length tparams > List.length targs
         then failwith "typecheck: too few arguments in application"
         else if List.length tparams < List.length targs
         then failwith "typecheck: too many arguments in application"
         else if tparams <> targs
         then failwith "typecheck: incompatible arguments in application"
         else tbody
       | _ -> failwith ("typecheck: invalid application expression: '" ^ string_of_exp e ^ "'"))
  in
  try Some (typecheck_exp e [])
  with Failure m -> derror (delay m); None

(*
                      ╔═════════════════════════════════╗
                      ║                                 ║
                      ║  CAPTURE-AVOIDING SUBSTITUTION  ║
                      ║                                 ║
                      ╚═════════════════════════════════╝

   NOTE: What follows is a full description of the capture-avoiding substitution
   algorithm for a multary lambda calculus. You don't need to read this to
   complete the assignment; it's just to explain what this function is, since we
   never discussed it in class.

   When performing substitution for application forms, a problem that can happen
   is you accidentally "capture" a variable that was meant to belong to a
   different lambda. For example, consider the following term in the basic
   (unary) lambda calculus:

       ((λ (x) (λ (y) (x y))) y)

   If we perform the substitution naively, we will end up with:

       (λ (y) (y y))

   The outermost [y] has been "captured" by the innermost lambda term. However,
   if we replace that outermost [y] in the original term with a different
   variable, such as [z], we would have:

       ((λ (x) (λ (y) (x y))) z)
       (λ (y) (z y))

   Since it doesn't seem sufficient to ask our users "please don't use the same
   variable name more than once", we need to perform substitution more
   carefully.

   Recall that we write substitutions using the notation:

       e_2[x/e_1]

   This means we are replacing occurrences of variable [x] occurring in
   expression [e_2] with expression [e_1]. For most expressions [e_2],
   substitution is straightforward: we simply replace occurrences of the
   variable [x] with the new expression [e_1]. Where things get tricky is when
   [e2] is a lambda (we're switching back to a multary lambda calculus, but
   we'll leave out the type annotations since we don't need them right now):

       (λ (p ...) e_b)[x/e_a]

   When we come to such a case, we have to follow these steps:

       1. Check if [x] occurs in [p ...], e.g., we have the following:

              (λ (p ... when x ∈ p) e_b)[x/e_a]

          Here, we're attempting to replace occurrences of [x] with [e_a] inside
          the expression [(λ (p ... when x ∈ p) e_b)]. However, since the lambda
          is re-binding the variable we are currently substituting, there is no
          way for our outer [x] to have a collision. All [x]es inside the
          lambda's body must refer to the lambda's own binding.

       1. Identify whether we can even possibly have a collision.

          1.1. Does [x] occur in [p ...]? Meaning we are performing something
               like the following:

                   (λ (p ... when x ∈ p) e_b)[x/e_a]

               Here, we're attempting to replace occurrences of [x] with [e_a]
               inside the expression [(λ (p ... when x ∈ p) e_b)]. However,
               since the lambda is re-binding the variable we are currently
               substituting, there is no way for our outer [x] to have a
               collision. All [x]es inside the lambda's body must refer to the
               lambda's own binding.

          1.2. Does [x] occur in [e_b]? If not, there is no collision.

          1.3. Do any of the variables in [e_a] occur in [e_b]? If not, there is
               no collision.

       2. For all colliding variables:

          2.1. Generate a new name guaranteed not to occur in [e_b] or [e_a].

          2.2. Replace the colliding name with the new name in the parameter
               names [p ...] and the body [e_b]. Note that we do not change the
               argument [e_a].

       3. Perform the substitution.

   The algorithm appears below in the [substitute] function. The functions
   between here and there are helpers for that [substitute] function. *)

(** Identifies all variables used in an expression. *)
let rec get_bound_variables (e : exp) : variable list =
  match e with
  | Val v ->
    (match v with
     | Lam (params, body) -> List.map fst params @ get_bound_variables body
     | _ -> [])
  | Var x -> [x]
  (* TODO PART 3 *)
  | App (ef, args) ->
    get_bound_variables ef @ (List.concat_map get_bound_variables args)

(** Produces an integer that has not been used yet.

    This function works by instantiating a mutable integer box ([ref 0]), then
    returning a zero-argument function (also called a "thunk") that returns the
    value inside the box, and increments the value stored in the box by 1.
    Functions like this are not commonly needed, but in this case it's a good
    idea because it ensures we will not accidentally run into name collisions.

    If we were using a big-step semantics (meaning instead of a [step] function
    we just had an [interp] function that fully reduced the input expression to
    a value), we could encapsulate the [fresh] counter within the scope of the
    [interp] function. But since we have only single steps at a time, we need
    for our counter to be global. We could add an ability to reset the counter
    to zero and use that in [multistep] or [eval], but there's no need. *)
let fresh : (unit -> int) =
  let counter = ref 0 in (fun () -> let prev = !counter in counter := prev + 1; prev)

(** Given a name and a list of undesirable (used) names, produces a new name by
    appending a fresh integer to the original name. This process is repeated
    until a name is generated that is not already bound. *)
let freshname (name : variable) (bound_names : variable list) : variable =
  let next_name () = name ^ string_of_int (fresh ()) in
  let rec freshname' (new_name : variable) : variable =
    if List.mem new_name bound_names
    then freshname' (next_name ())
    else new_name
  in
  freshname' (next_name ())

(** Inserts a list of replacements at specified points in an original list of
    items.

    This is used to update the lists of parameters in lambdas. *)
let replace_items (replacements : (int * 'a) list) (originals : 'a list) : 'a list =
  let rec replace_items' index rs os =
    match (rs, os) with
    | ([], _) -> os
    | (_, []) -> failwith "replace_items: too few elements in original list"
    | ((i, r) :: rs', o :: os') ->
      if i = index
      then r :: (replace_items' (i + 1) rs' os')
      else o :: (replace_items' (i + 1) rs os')
  in
  replace_items' 0 replacements originals

(** Multary capture-avoiding substitution algorithm, based on a unary
    implementation found here:

        https://stackoverflow.com/a/60915847/3377150

    If you are performing [e2[x/e1]] (i.e., replacing all occurrences of the
    variable [x] occurring in [e2] with the expression [e1]), then you would
    call this function as [substitute e1 x e2]. *)
let rec substitute (arg : exp) (for_name : variable) (in_exp : exp) : exp =
  match in_exp with
  | Val v ->
    (match v with
     | Lam (params, body) ->
       if List.mem_assoc for_name params
       (* If the variable is re-bound by this lambda, we don't need to worry
          about anything. *)
       then in_exp
       else
         (* Otherwise, check if the variable is used in the lambda's body. *)
         let used_in_body = get_bound_variables body in
         if not (List.mem for_name used_in_body)
         (* If it isn't, then do nothing. *)
         then in_exp
         else
           (* Otherwise, we need to look through the variables that are used by
              the argument term. *)
           let used_in_arg = get_bound_variables arg in
           let indexed_params = List.mapi (fun i (p, _) -> (i, p)) params in
           let conflicts = List.filter (fun (_, p) -> List.mem p used_in_arg) indexed_params in
           (match conflicts with
            (* If there are no conflicts, we can perform substitution! *)
            | [] -> Val (Lam (params, substitute arg for_name body))
            (* Otherwise, we have to rename our conflicting variables. *)
            | _ ->
              (* First, we find all the names being used everywhere. *)
              let all_used_names = used_in_body @ used_in_arg in
              (* We generate new names for all conflicting parameter names,
                 making sure we don't use any name that's already used. *)
              let renamed_conflicts = List.map (fun (i, p) -> (i, freshname p all_used_names)) conflicts in
              let replacements = List.map2 (fun (_, r) (_, o) -> (r, o)) renamed_conflicts conflicts in
              (* Now we update our list of parameters with the new names. *)
              let updated_params =
                List.map2
                  (fun p (_, t) -> (p, t))
                  (replace_items renamed_conflicts (List.map fst params))
                  params in
              (* And generate a new body expression, performing all the
                 appropriate replacements. *)
              let updated_body =
                substitute
                  arg
                  for_name
                  (List.fold_left
                     (fun b' (r, o) -> substitute (Var r) o b')
                     body
                     replacements) in
              (* Lastly, we put it all together! *)
              Val (Lam (updated_params, updated_body)))
     | _ -> in_exp)
  | Var x ->
    if x = for_name
    (* If we found the variable we're looking for, perform substitution! *)
    then arg
    (* Otherwise, leave it alone. *)
    else in_exp
  (* For all other forms, we need only perform the substitution in the sub-
     expressions of the current expression. *)
  (* TODO PART 3 *)
  | App (ef, args) ->
    App (substitute arg for_name ef,
         List.map (substitute arg for_name) args)

(*
                                ╔══════════════╗
                                ║              ║
                                ║  EVALUATION  ║
                                ║              ║
                                ╚══════════════╝
*)

(** Determines whether an [exp] is a [value].

    Although the [exp] type has a [Val] constructor, it is not trivial to test
    variant tags in OCaml without writing a function like this. In the initial
    implementation of this file, this function is only used by [step] to check
    whether a list of argument expressions in an [App] have all been reduced to
    [value]s. An alternative solution would have been to use a specialized
    encoding of argument lists that distinguishes "a list of fully reduced value
    arguments" from "a list of arguments, some of which are certainly not
    reduced to values", but that was a lot of overhead and this was easier. *)
let is_value (e : exp) : bool = match e with Val _ -> true | _ -> false

(** Completes a step for a primitive unary function. *)
let step_primitive_unary_function
    (* The primitive function we're applying. *)
    (func : value)
    (* The arguments to the function (straight from the lambda expression). *)
    (vargs : exp list)
    (* A function to extract the OCaml value from the [value]. *)
    (arg_extract : value -> 'a option)
    (* A function that converts the OCaml value to a new [value]. *)
    (val_produce : 'a -> value): exp =
  let name = List.assoc func simple_values_to_strings in
  match vargs with
  | [] -> failwith ("step: too few arguments in application of '" ^ name ^ "'")
  | [Val varg] ->
    (match arg_extract varg with
     | Some a -> Val (val_produce a)
     | None -> failwith ("step: invalid argument for '" ^ name ^ "': '" ^ string_of_value varg ^ "'"))
  | _ -> failwith ("step: too many arguments in application of '" ^ name ^ "'")

(** Completes a step for a primitive binary function. *)
let step_primitive_binary_function
    (* The primitive function we're applying. *)
    (func : value)
    (* The arguments to the function (straight from the lambda expression). *)
    (vargs : exp list)
    (* A function to extract the OCaml value from the first argument. *)
    (arg1_extract : (value -> 'a option))
    (* A function to extract the OCaml value from the second argument. *)
    (arg2_extract : (value -> 'b option))
    (* A function that converts the two OCaml values to a new [value]. *)
    (val_combine : ('a -> 'b -> value)) : exp =
  let name = List.assoc func simple_values_to_strings in
  match vargs with
  | [] | [_] -> failwith ("step: too few arguments in application of '" ^ name ^ "'")
  | [Val varg1; Val varg2] ->
    (match (arg1_extract varg1, arg2_extract varg2) with
     | (Some a, Some b) -> Val (val_combine a b)
     | (None, _) -> failwith ("step: invalid first argument for '" ^ name ^ "': '" ^ string_of_value varg1 ^ "'")
     | (_, None) -> failwith ("step: invalid second argument for '" ^ name ^ ";: '" ^ string_of_value varg2 ^ "'"))
  | _ -> failwith ("step: too many arguments in application of '" ^ name ^ "'")

(* Functions for extracting OCaml values from [value]s. *)
let bool_extract = function (Bool b) -> Some b | _ -> None
let int_extract = function Int z -> Some z | _ -> None

(** Takes a single step according to the small-step operational semantics. *)
let step (e : exp) : exp option =
  let rec step' (e : exp) : exp =
    dwarn (delay ("taking a step with expression: '" ^ string_of_exp e ^ "'"));
    let rec step_args (es : exp list) : exp list =
      match es with
      | [] -> []
      | (Val _ as e) :: es' ->
        let es' = step_args es' in
        e :: es'
      | e :: es' ->
        let e' = step' e in
        e' :: es'
    in
    match e with
    (* Values do not reduce. *)
    | Val _ -> e
    (* Variables are not allowed to be free. *)
    | Var x -> failwith ("step: invalid reference to free variable '" ^ x ^ "'")
    (* TODO PART 3 *)
    (* Applications are the tricky part. *)
    | App (Val vf, vargs) when List.for_all is_value vargs ->
      (match vf with
       (* Application of a user-defined lambda expression. *)
       | Lam (ps, b) ->
         if List.length ps > List.length vargs
         then failwith "step: too few arguments in application"
         else if List.length ps < List.length vargs
         then failwith "step: too many arguments in application"
         else
           List.fold_left2
             (fun b' arg (p, _) -> substitute arg p b')
             b
             vargs
             ps
       (* Primitive function application. *)
       (* TODO PART 1: Add rules for the original primitive functions here. *)
       | Add -> step_primitive_binary_function Add vargs int_extract int_extract (fun a b -> Int (a + b))
       (* TODO PART 2: Add rules for the new primitive functions here. *)
       (* TODO PART 3

          NOTE: There is no [step_primitive_ternary_function] function to use
          with your [if] form. You can choose to implement one, but you
          certainly don't have to if you'd rather just implement it here
          directly. *)
       (* Anything else is undefined! *)
       | _ -> failwith ("step: invalid subject of application: '" ^ string_of_value vf ^ "'"))
    | App (Val vf, args) -> App (Val vf, step_args args)
    | App (ef, args) -> App (step' ef, args)
  in
  try Some (step' e)
  with Failure m -> derror (delay m); None

(** Takes [k] steps over the given expression [e]. *)
let rec multistep (k : int) (e : exp) : exp option =
  if is_value e
  then Some e
  else
    match k with
    | 0 -> Some e
    | _ ->
      (match step e with
       | Some e' -> multistep (k - 1) e'
       | None -> None)

(** The number of steps taken by the [eval] function when it is able to evaluate
    its input. *)
let number_of_steps = 42

(** Parses a given string, type-checks the resulting expression, and evaluates
    the expression if type-checking is successful. Returns the evaluated form of
    the expression if there are no errors. *)
let eval (s : string) : exp option =
  match parse s with
  | None -> None
  | Some e ->
    (match (typecheck e, multistep number_of_steps e) with
     | (Some _, Some r) -> Some r
     | _ -> None)

(*
                                  ╔═════════╗
                                  ║         ║
                                  ║  TESTS  ║
                                  ║         ║
                                  ╚═════════╝
*)

(** If you run [dune utop] anywhere in this repository, you can run the tests by
    doing [Hw2.Main.Tests.run_tests ();;] to execute all the tests. If all tests
    are successful, you will get back the unit value. If any test fails, an
    assertion error will be raised.

    You can also run the tests in [debug] mode via [Tests.run_tests_debug ();;].
    This will print out a lot of extra information along the way, which can be
    useful in tracking down bugs!

    We highly recommend adding additional tests to the list [Tests.tests] here,
    and then checking that they run successfully using [Tests.run_tests]. If
    successful, you should get [()] (the unit value) as output!

    Tests are pairs consisting of a string representing the program, and an
    optional pair of a type and expression. If the optional value is [None], it
    means that the program is expected to fail at some point (e.g., by raising
    an error during evaluation or not type-checking or something like that). In
    other cases it should be a [Some] of a pair whose first value is the type
    the final result should have, and whose second value is the expression that
    should be obtained after [Tests.max_steps] steps have been taken. *)
module Tests = struct
  type test = (string * (ty * exp) option)

  (* Here are some helper functions for easily writing some values. *)
  let vb b = Val (Bool b)
  let vt = vb true
  let vf = vb false
  let vi z = Val (Int z)

  (* If you want to write more complicated inputs, it can make sense to write
     them as separate values as we do here with [s1]/[t1]/[v1]. *)

  let s1 = "(lambda ((x : Bool) (y : Int)) y)"
  let t1 = Arrow ([Bool; Int], Int)
  let v1 = Option.get (parse s1)

  let s2 = "(" ^ s1 ^ " #t 42)"
  let t2: ty = Int
  let v2 = vi 42

  let fact = "(fix (lambda ((f : ((Int) -> Int))) (lambda ((n : Int)) (if (iszero n) 1 ( * n (f (- n 1)))))))"
  let s3 = "((lambda ((fact : ((Int) -> Int))) (iszero (- (fact 5) 120))) " ^ fact ^ ")"
  let t3: ty = Bool
  let v3 = vt

  (* These tests should pass after you have completed Part 1. *)
  let part1_tests : test list =
    (* Positive tests. *)
    [ ("#t", Some (Bool, vt))
    ; ("#f", Some (Bool, vf))
    ; ("42", Some (Int, vi 42))
    ; ("(not #t)", Some (Bool, vf))
    ; ("(and #t #f)", Some (Bool, vf))
    ; ("(+ 2 3)", Some (Int, vi 5))
    ; (s1, Some (t1, v1))
    ; (s2, Some (t2, v2))
    (* Negative tests. *)
    ; ("foo", None)
    ; ("(foo)", None)
    ; ("(foo #t)", None)
    ; ("(not 42)", None)
    ; ("(and #t 13)", None)
    ; ("(+ 12 #f)", None)
    ; ("(" ^ s1 ^ " 0 42)", None)
    ]

  (* These tests should pass after you have completed Part 2. *)
  let part2_tests : test list =
    (* Positive tests. *)
    [ ("(iszero 0)", Some (Bool, vt))
    ; ("(iszero (+ 0 3))", Some (Bool, vf))
    ; ("(or #t #f)", Some (Bool, vt))
    ; ("(or (and #f #t) #f)", Some (Bool, vf))
    ; ("(- 10 3)", Some (Int, vi 7))
    ; ("(- 0 (+ 10 9))", Some (Int, vi (-19)))
    ; ("(- (- 5 5) -3)", Some (Int, vi 3))
    ; ("(* 6 9)", Some (Int, vi 54))
    ; ("(* (- 4 2) 7)", Some (Int, vi 14))
    (* Negative tests. *)
    ; ("(iszero #f)", None)
    ; ("(iszero (and #f #t))", None)
    ; ("(or 7 #t)", None)
    ; ("(or #f (- 0 1))", None)
    ; ("(- #t 18)", None)
    ; ("(- 0 (iszero 12))", None)
    ; ("(* 8 #f)", None)
    ]

  (* These tests should pass after you have completed Part 3. *)
  let part3_tests : test list =
    (* Positive tests. *)
    [ ("(if #t 1 2)", Some (Int, vi 1))
    ; ("(if (iszero (* 14 8)) (- 92 18) 0)", Some (Int, vi 0))
    ; (s3, Some (t3, v3))
    (* Negative tests. *)
    ; ("(if 7 #t #f)", None)
    ]

  (* These tests should pass after you have completed Part 4. *)
  let part4_tests : test list =
    (* Positive tests. *)
    [ ("(record #t 0 (+ 1 2))", None) (* TODO PART 4: Replace [None] with the
                                         correct return type and value according
                                         to your definition of records. *)
    ; ("(proj 2 (record 0 -7 #f))", Some (Int, vi (-7)))
    (* Negative tests. *)
    ; ("(proj 3 (record #f))", None)
    ]

  (* TODO: Add some more tests! *)
  let extra_tests : test list =
    [
    ]

  (* Convenience list with all the tests. *)
  let all_tests : test list = part1_tests @ part2_tests @ part4_tests @ extra_tests

  (** The number of steps to evaluate. *)
  let max_steps = number_of_steps

  (** Runs a single test. *)
  let run_test ((input, result) : test) : unit =
    dwarn (delay ("running test: " ^ input));
    match parse input with
    | None -> failwith ("run_test: could not parse input '" ^ input ^ "'")
    | Some e ->
      (match result with
       | None -> assert (typecheck e = None && eval input = None)
       | Some (expected_type, expected_result) ->
         dwarn (delay ("  expected type: '" ^ string_of_type expected_type ^ "'"));
         let actual_type : ty option = typecheck e in
         dwarn (delay ("  actual type: " ^
                       match actual_type with
                       | Some t -> "'" ^ string_of_type t ^ "'"
                       | None -> "<none>"));
         dwarn (delay ("  expected result: '" ^ string_of_exp expected_result ^ "'"));
         let actual_mstep_res : exp option = multistep max_steps e in
         dwarn (delay ("  actual multistep result: " ^
                       match actual_mstep_res with
                       | Some e -> "'" ^ string_of_exp e ^ "'"
                       | None -> "<none>"));
         let actual_eval_res : exp option = eval input in
         dwarn (delay ("  actual eval result: " ^
                       match actual_eval_res with
                       | Some e -> "'" ^ string_of_exp e ^ "'"
                       | None -> "<none>"));
         try (assert (actual_type = Some expected_type &&
                      actual_mstep_res = Some expected_result &&
                      Option.is_some actual_eval_res && Option.get actual_eval_res = expected_result);
              dwarn (delay ("test passed")))
         with Assert_failure _ ->
           print_endline ("Failed test: " ^ input);
           (match result with
            | Some (et, ee) ->
              print_endline ("  Expected result: " ^ string_of_exp ee);
              print_endline ("  With type: " ^ string_of_type et)
            | None ->
              print_endline ("  Expected evaluation to fail."));
           print_endline "";
           (match actual_type with
            | Some ft -> print_endline ("  Found type: " ^ string_of_type ft)
            | None -> print_endline "  Could not compute a type.");
           (match actual_mstep_res with
            | Some mr -> print_endline ("  Result after " ^ string_of_int max_steps ^
                                        " steps: " ^ string_of_exp mr)
            | None -> print_endline ("  Had no result after " ^ string_of_int max_steps ^
                                     " steps."));
           (match actual_eval_res with
            | Some er -> print_endline ("  Result from `eval`: " ^
                                        string_of_exp er)
            | None -> print_endline "  No result from `eval`."))

  (** Runs a list of tests. *)
  let run_tests (tests : test list) = List.iter (fun t -> run_test t; dwarn (delay "")) tests

  (** Runs a list of tests in [debug := Warnings] mode. *)
  let run_tests_debug (tests : test list) =
    let prev_debug = !debug in
    debug := Errors;
    run_tests tests;
    debug := prev_debug

  (* Convenience functions for running different groups of tests. *)
  let run_part1_tests () = run_tests part1_tests
  let run_part2_tests () = run_tests part2_tests
  let run_part3_tests () = run_tests part3_tests
  let run_part4_tests () = run_tests part4_tests
  let run_all_tests () = run_tests all_tests

  (* Convenience functions for running different groups of tests in [debug]
     mode. *)
  let run_part1_tests_debug () = run_tests_debug part1_tests
  let run_part2_tests_debug () = run_tests_debug part2_tests
  let run_part3_tests_debug () = run_tests_debug part3_tests
  let run_part4_tests_debug () = run_tests_debug part4_tests
  let run_all_tests_debug () = run_tests_debug all_tests
end
