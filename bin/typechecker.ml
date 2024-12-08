open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) (err : string) =
  let _, (s, e), _ = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))
;;

(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string", ([ TRef RString ], RetVal (TRef (RArray TInt)))
  ; "string_of_array", ([ TRef (RArray TInt) ], RetVal (TRef RString))
  ; "length_of_string", ([ TRef RString ], RetVal TInt)
  ; "string_of_int", ([ TInt ], RetVal (TRef RString))
  ; "string_cat", ([ TRef RString; TRef RString ], RetVal (TRef RString))
  ; "print_string", ([ TRef RString ], RetVoid)
  ; "print_int", ([ TInt ], RetVoid)
  ; "print_bool", ([ TBool ], RetVoid)
  ]
;;

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> TInt, TInt, TInt
  | Lt | Lte | Gt | Gte -> TInt, TInt, TBool
  | And | Or -> TBool, TBool, TBool
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="
;;

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> TInt, TInt
  | Lognot -> TBool, TBool
;;

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2
   - assumes that H contains the declarations of all the possible struct types

   - you will want to introduce addition (possibly mutually recursive)
     helper functions to implement the different judgments of the subtyping
     relation. We have included a template for subtype_ref to get you started.
     (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (h : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TNullRef ref1, TNullRef ref2 | TRef ref1, TRef ref2 | TRef ref1, TNullRef ref2 ->
    subtype_ref h ref1 ref2
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (h : Tctxt.t) (ref1 : Ast.rty) (ref2 : Ast.rty) : bool =
  match ref1, ref2 with
  | RString, RString -> true
  (* TODO: t1 <: t2 => t1[] <: t2[] ? *)
  | RArray t1, RArray t2 -> if t1 = t2 then true else false
  | RStruct s1, RStruct s2 ->
    let fs1 = lookup_struct_option s1 h
    and fs2 = lookup_struct_option s2 h in
    if fs1 = None || fs2 = None
    then false
    else (
      let fs1 = Option.get fs1
      and fs2 = Option.get fs2 in
      List.for_all (fun f2 -> List.exists (fun f1 -> f1 = f2) fs1) fs2)
  | RFun (ts, rt1), RFun (ts', rt2) ->
    if List.length ts <> List.length ts'
    then false
    else (
      let t_t's = List.combine ts ts' in
      List.for_all (fun (t, t') -> subtype h t' t) t_t's && subtype_ret h rt1 rt2)
  | _ -> false

and subtype_ret (h : Tctxt.t) (rt1 : Ast.ret_ty) (rt2 : Ast.ret_ty) : bool =
  match rt1, rt2 with
  | RetVoid, RetVoid -> true
  | RetVal t1, RetVal t2 -> subtype h t1 t2
  | _ -> false
;;

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

   - the function should succeed by returning () if the type is well-formed
     according to the rules

   - the function should fail using the "type_error" helper function if the
     type is not well formed

   - l is just an ast node that provides source location information for
     generating error messages (it's only needed for the type_error generation)

   - tc contains the structure definition context
*)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  failwith "todo: implement typecheck_ty"
;;

(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false
;;

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)
*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  failwith "todo: implement typecheck_exp"
;;

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement
   This function should implement the statment typechecking rules from oat.pdf.

   Inputs:
   - tc: the type context
   - s: the statement node
   - to_ret: the desired return type (from the function declaration)

   Returns:
   - the new type context (which includes newly declared variables in scope
     after this statement)

   - A boolean indicating the return behavior of a statement:
     false:  might not return
     true: definitely returns

   in the branching statements, the return behavior of the branching
   statement is the conjunction of the return behavior of the two
   branches: both both branches must definitely return in order for
   the whole statement to definitely return.

   Intuitively: if one of the two branches of a conditional does not
   contain a return statement, then the entire conditional statement might
   not return.

   looping constructs never definitely return

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s : Ast.stmt node) (to_ret : ret_ty)
  : Tctxt.t * bool
  =
  failwith "todo: implement typecheck_stmt"
;;

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is
   is needed elswhere in the type system.
*)

(* Helper function to look for duplicate field names *)
let rec check_dups (fs : field list) =
  match fs with
  | [] -> false
  | h :: t -> List.exists (fun x -> x.fieldName = h.fieldName) t || check_dups t
;;

let typecheck_tdecl (tc : Tctxt.t) (id : id) (fs : field list) (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id)
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs
;;

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration
   - ensures formal parameters are distinct
   - extends the local context with the types of the formal parameters to the
     function
   - typechecks the body of the function (passing in the expected return type
   - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  failwith "todo: typecheck_fdecl"
;;

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that their names are distinct)

   H1 |-s prog ==> H2

   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

   H ; G1 |-f prog ==> G2

   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

   H ; G1 |-g prog ==> G2

   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let create_struct_ctxt (h1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec create_struct_ctxt_aux (h1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
    match p with
    | [] -> Tctxt.empty
    | d :: p' ->
      let h2 =
        match d with
        | Gvdecl _ | Gfdecl _ -> h1
        | Gtdecl ({ elt = s, fs } as l) ->
          (match lookup_struct_option s h1 with
           | Some _ -> type_error l ("Duplicate struct type: " ^ s)
           | None -> add_struct h1 s fs)
      in
      create_struct_ctxt_aux h2 p'
  in
  let h2 = create_struct_ctxt_aux Tctxt.empty p in
  h2
;;

let create_function_ctxt (h_g1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec create_function_ctxt_aux (h_g1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
    match p with
    | [] -> Tctxt.empty
    | d :: p' ->
      let h_g2 =
        match d with
        | Gtdecl _ | Gvdecl _ -> h_g1
        | Gfdecl ({ elt = { frtyp; fname = f; args } as fd } as l) ->
          typecheck_fdecl h_g1 fd l;
          let args_typs = List.map (fun (arg_typ, _) -> arg_typ) args in
          let t = TRef (RFun (args_typs, frtyp)) in
          (match lookup_global_option f h_g1 with
           | Some _ -> type_error l ("Duplicate function: " ^ f)
           | None -> add_global h_g1 f t)
      in
      create_function_ctxt_aux h_g2 p'
  in
  let h_g2 = create_function_ctxt_aux h_g1 p in
  h_g2
;;

let create_global_ctxt (h_g1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec create_global_ctxt_aux (h_g1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
    match p with
    | [] -> Tctxt.empty
    | d :: p' ->
      let h_g2 =
        match d with
        | Gtdecl _ | Gfdecl _ -> h_g1
        | Gvdecl ({ elt = { name = x; init = gexp } } as l) ->
          let t = typecheck_exp h_g1 gexp in
          (match lookup_global_option x h_g1 with
           | Some _ -> type_error l ("Duplicate global variable: " ^ x)
           | None -> add_global h_g1 x t)
      in
      create_global_ctxt_aux h_g2 p'
  in
  let h_g2 = create_global_ctxt_aux h_g1 p in
  h_g2
;;

(* This function implements the |- prog and the H ; G |- prog
   rules of the oat.pdf specification.
*)
let typecheck_program (p : Ast.prog) : unit =
  let sc = create_struct_ctxt Tctxt.empty p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter
    (function
      | Gvdecl _ -> ()
      | Gfdecl ({ elt = f } as l) -> typecheck_fdecl tc f l
      | Gtdecl ({ elt = id, fs } as l) -> typecheck_tdecl tc id fs l)
    p
;;
