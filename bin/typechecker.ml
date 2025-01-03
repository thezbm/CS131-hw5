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

let unexpected_type (l : 'a node) (t : Ast.ty) =
  type_error l ("Type error: unexpected type " ^ string_of_ty t)

and assert_type (l : 'a node) (t : Ast.ty) (t' : Ast.ty) =
  if not (t = t')
  then
    type_error
      l
      (Printf.sprintf
         "Type error: expected %s, got %s"
         (string_of_ty t')
         (string_of_ty t))
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

   NOTE:
   - subtype, subtype_ref, and subtype_ret will not raise errors
   - when a struct type cannot be found in the context, subtype and subtype_ref
     return false
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

(* Helper function for subtype assertions. *)
let assert_subtype (l : 'a node) (h : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) =
  if not (subtype h t1 t2)
  then
    type_error
      l
      (Printf.sprintf "Subtyping error: %s </: %s" (string_of_ty t1) (string_of_ty t2))
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
let rec typecheck_ty (l : 'a Ast.node) (h : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TRef ref | TNullRef ref -> typecheck_ref l h ref

and typecheck_ref (l : 'a Ast.node) (h : Tctxt.t) (ref : Ast.rty) : unit =
  match ref with
  | RString -> ()
  | RArray t -> typecheck_ty l h t
  | RStruct s ->
    if lookup_struct_option s h = None then type_error l ("Undefined struct type: " ^ s)
  | RFun (ts, rt) ->
    List.iter (fun t -> typecheck_ty l h t) ts;
    typecheck_ret l h rt

and typecheck_ret (l : 'a Ast.node) (h : Tctxt.t) (rt : Ast.ret_ty) : unit =
  match rt with
  | RetVoid -> ()
  | RetVal t -> typecheck_ty l h t
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
let rec typecheck_exp (h_g_l : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull ref ->
    typecheck_ty e h_g_l (TRef ref);
    TNullRef ref
  | CBool true | CBool false -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | Id id ->
    (match lookup_local_option id h_g_l with
     | None ->
       (match lookup_global_option id h_g_l with
        | None -> type_error e ("Undefined identifier: " ^ id)
        | Some t -> t)
     | Some t -> t)
  | CArr (t, exps) ->
    typecheck_ty e h_g_l t;
    List.iter (fun exp -> assert_subtype exp h_g_l (typecheck_exp h_g_l exp) t) exps;
    TRef (RArray t)
  | NewArr (t, exp1) ->
    typecheck_ty e h_g_l t;
    assert_type exp1 (typecheck_exp h_g_l exp1) TInt;
    (match t with
     | TInt | TBool | TNullRef _ -> ()
     | _ -> unexpected_type exp1 t);
    TRef (RArray t)
  | NewArrInit (t, exp1, x, exp2) ->
    typecheck_ty e h_g_l t;
    assert_type exp1 (typecheck_exp h_g_l exp1) TInt;
    (match lookup_local_option x h_g_l with
     | Some _ -> type_error e ("Identifier already defined in local context: " ^ x)
     | None ->
       let h_g_l' = add_local h_g_l x TInt in
       let t' = typecheck_exp h_g_l' exp2 in
       assert_subtype exp2 h_g_l t' t);
    TRef (RArray t)
  | Index (exp1, exp2) ->
    (match typecheck_exp h_g_l exp1 with
     | TRef (RArray t) ->
       assert_type exp2 (typecheck_exp h_g_l exp2) TInt;
       t
     | t -> unexpected_type exp1 t)
  | Length exp ->
    (match typecheck_exp h_g_l exp with
     | TRef (RArray _) -> TInt
     | t -> unexpected_type exp t)
  | CStruct (s, x_exps) ->
    (match lookup_struct_option s h_g_l with
     | None -> type_error e ("Undefined struct type: " ^ s)
     | Some fs ->
       let x_exps = List.sort (fun (x1, _) (x2, _) -> String.compare x1 x2) x_exps in
       let fs = List.sort (fun f1 f2 -> String.compare f1.fieldName f2.fieldName) fs in
       if List.length x_exps <> List.length fs
       then type_error e "Incorrect number of fields";
       List.iter2
         (fun (x, exp) f ->
           if x <> f.fieldName
           then type_error e ("Missing field: " ^ f.fieldName)
           else (
             let t', t = typecheck_exp h_g_l exp, f.ftyp in
             assert_subtype exp h_g_l t' t))
         x_exps
         fs;
       TRef (RStruct s))
  | Proj (exp, x) ->
    (match typecheck_exp h_g_l exp with
     | TRef (RStruct s) ->
       (match lookup_struct_option s h_g_l with
        | None -> type_error exp ("Undefined struct type: " ^ s)
        | Some _ ->
          (match lookup_field_option s x h_g_l with
           | None -> type_error exp ("Undefined field: " ^ x)
           | Some t -> t))
     | t -> unexpected_type exp t)
  | Call (exp, exps) ->
    (match typecheck_exp h_g_l exp with
     | TRef (RFun (ts, t)) ->
       if List.length ts <> List.length exps
       then type_error e "Incorrect number of arguments"
       else (
         List.iter2
           (fun exp t -> assert_subtype exp h_g_l (typecheck_exp h_g_l exp) t)
           exps
           ts;
         match t with
         | RetVoid -> type_error exp "Unexpected void return"
         | RetVal t -> t)
     | t -> unexpected_type exp t)
  | Bop (binop, exp1, exp2) ->
    (match binop with
     | Eq | Neq ->
       let t1, t2 = typecheck_exp h_g_l exp1, typecheck_exp h_g_l exp2 in
       assert_subtype exp1 h_g_l t1 t2;
       assert_subtype exp2 h_g_l t2 t1;
       TBool
     | _ ->
       let t1, t2, t = typ_of_binop binop in
       assert_subtype exp1 h_g_l (typecheck_exp h_g_l exp1) t1;
       assert_subtype exp2 h_g_l (typecheck_exp h_g_l exp2) t2;
       t)
  | Uop (uop, exp) ->
    let t, rt = typ_of_unop uop in
    assert_type e rt t;
    assert_type exp (typecheck_exp h_g_l exp) t;
    t
;;

(* statements --------------------------------------------------------------- *)

let rec typecheck_vdecl (h_g_l1 : Tctxt.t) (vdecl : Ast.vdecl) (l : 'a Ast.node) : Tctxt.t
  =
  let x, exp = vdecl in
  let t = typecheck_exp h_g_l1 exp in
  match lookup_local_option x h_g_l1 with
  | Some _ -> type_error l ("Identifier already defined in local context: " ^ x)
  | None -> add_local h_g_l1 x t

and typecheck_vdecls (h_g_l0 : Tctxt.t) (vdecls : Ast.vdecl list) (l : 'a Ast.node)
  : Tctxt.t
  =
  List.fold_left (fun h_g_l vdecl -> typecheck_vdecl h_g_l vdecl l) h_g_l0 vdecls
;;

(* Typecheck a statement
   This function should implement the statment typechecking rules from oat.pdf.

   Inputs:
   - h_g_l1: the type context H;G;L1
   - rt: the desired return type (from the function declaration)
   - stmt: the statement node

   Returns:
   - the new type context L2 (which includes newly declared variables in scope
     after this statement)

   - A boolean indicating the return behavior of a statement:
     false:  might not return
     true: definitely returns

   in the branching statements, the return behavior of the branching
   statement is the conjunction of the return behavior of the two
   branches: both branches must definitely return in order for
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
let rec typecheck_stmt (h_g_l1 : Tctxt.t) (rt : ret_ty) (stmt : Ast.stmt node)
  : Tctxt.t * bool
  =
  match stmt.elt with
  | Assn (lhs, exp) ->
    (match lhs.elt with
     | Id id ->
       (match lookup_global_option id h_g_l1 with
        | Some (TRef (RFun _)) ->
          if lookup_local_option id h_g_l1 = None
          then type_error lhs ("Assigning to global function: " ^ id)
        | _ -> ())
     | _ -> ());
    assert_subtype exp h_g_l1 (typecheck_exp h_g_l1 exp) (typecheck_exp h_g_l1 lhs);
    h_g_l1, false
  | Decl vdecl -> typecheck_vdecl h_g_l1 vdecl stmt, false
  | SCall (exp, exps) ->
    (match typecheck_exp h_g_l1 exp with
     | TRef (RFun (ts, RetVoid)) ->
       List.iter2
         (fun exp t -> assert_subtype exp h_g_l1 (typecheck_exp h_g_l1 exp) t)
         exps
         ts;
       h_g_l1, false
     | t -> unexpected_type exp t)
  | If (exp, block1, block2) ->
    assert_type exp (typecheck_exp h_g_l1 exp) TBool;
    let r1, r2 = typecheck_block h_g_l1 rt block1, typecheck_block h_g_l1 rt block2 in
    h_g_l1, r1 && r2
  | Cast (ref, x, exp, block1, block2) ->
    (match typecheck_exp h_g_l1 exp with
     | TNullRef ref' ->
       assert_subtype exp h_g_l1 (TRef ref') (TRef ref);
       let r1 = typecheck_block (add_local h_g_l1 x (TRef ref)) rt block1
       and r2 = typecheck_block h_g_l1 rt block2 in
       h_g_l1, r1 && r2
     | t -> unexpected_type exp t)
  | While (exp, block) ->
    assert_type exp (typecheck_exp h_g_l1 exp) TBool;
    let _r = typecheck_block h_g_l1 rt block |> ignore in
    h_g_l1, false
  | For (vdecls, exp_opt, stmt_opt, block) ->
    let h_g_l2 = typecheck_vdecls h_g_l1 vdecls stmt in
    if exp_opt <> None
    then (
      let exp = Option.get exp_opt in
      assert_type exp (typecheck_exp h_g_l2 exp) TBool);
    if stmt_opt <> None
    then (
      let stmt = Option.get stmt_opt in
      let _h_g_l3, r = typecheck_stmt h_g_l2 rt stmt in
      if r then type_error stmt "Unexpected must-return statement");
    let _r = typecheck_block h_g_l2 rt block in
    h_g_l1, false
  | Ret exp ->
    (match exp with
     | Some exp ->
       (match rt with
        | RetVoid -> type_error exp "Unexpected return value"
        | RetVal t ->
          assert_subtype exp h_g_l1 (typecheck_exp h_g_l1 exp) t;
          h_g_l1, true)
     | None ->
       (match rt with
        | RetVal _ -> type_error stmt "Return type is not void"
        | RetVoid -> h_g_l1, true))

(* typecheck_block returns true if the block definitely returns *)
and typecheck_block (h_g_l : Tctxt.t) (rt : ret_ty) (block : Ast.block) : bool =
  let h_g_l0, stmts = h_g_l, block in
  let _h_g_ln, r = typecheck_stmts h_g_l0 rt stmts in
  r

and typecheck_stmts (h_g_l0 : Tctxt.t) (rt : ret_ty) (stmts : Ast.stmt node list)
  : Tctxt.t * bool
  =
  let ln, r =
    List.fold_left
      (fun (h_g_l, r) stmt ->
        if r then type_error stmt "Unexpected must-return statement";
        typecheck_stmt h_g_l rt stmt)
      (h_g_l0, false)
      stmts
  in
  ln, r
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
   - typechecks the body of the function (passing in the expected return type)
   - checks that the function actually returns
*)
let rec typecheck_fdecl (h_g : Tctxt.t) (fdecl : Ast.fdecl) (l : 'a Ast.node) : unit =
  let { frtyp = rt; fname = f; args = t_xs; body = block } = fdecl in
  let h_g_l =
    List.fold_left
      (fun h_g_l (t, x) ->
        if lookup_local_option x h_g_l <> None
        then type_error l ("Duplicate parameter: " ^ x);
        add_local h_g_l x t)
      h_g
      t_xs
  in
  if not (typecheck_block h_g_l rt block) then type_error l "Function does not return"
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
    | [] -> h1
    | d :: p' ->
      let h2 =
        match d with
        | Gvdecl _ | Gfdecl _ -> h1
        | Gtdecl ({ elt = s, fs } as tdecl) ->
          (match lookup_struct_option s h1 with
           | Some _ -> type_error tdecl ("Duplicate struct type: " ^ s)
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
    | [] -> h_g1
    | d :: p' ->
      let h_g2 =
        match d with
        | Gtdecl _ | Gvdecl _ -> h_g1
        | Gfdecl fdecl ->
          let f, t = typecheck_fsig h_g1 fdecl in
          (match lookup_global_option f h_g1 with
           | Some _ -> type_error fdecl ("Duplicate global function: " ^ f)
           | None -> add_global h_g1 f t)
      in
      create_function_ctxt_aux h_g2 p'
  and typecheck_fsig (h : t) ({ elt = { frtyp = rt; fname = f; args = t_xs } } as fdecl)
    : Ast.id * Ast.ty
    =
    typecheck_ret fdecl h rt;
    let ts =
      List.map
        (fun (t, _x) ->
          typecheck_ty fdecl h t;
          t)
        t_xs
    in
    f, TRef (RFun (ts, rt))
  in
  let h_g2 = create_function_ctxt_aux h_g1 p in
  h_g2
;;

let create_global_ctxt (h_g1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec create_global_ctxt_aux (h_g1 : Tctxt.t) (p : Ast.prog) : Tctxt.t =
    match p with
    | [] -> h_g1
    | d :: p' ->
      let h_g2 =
        match d with
        | Gtdecl _ | Gfdecl _ -> h_g1
        | Gvdecl ({ elt = { name = x; init = gexp } } as gdecl) ->
          let t = typecheck_exp h_g1 gexp in
          (match lookup_global_option x h_g1 with
           | Some _ -> type_error gdecl ("Duplicate global variable: " ^ x)
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
  let h = create_struct_ctxt Tctxt.empty p in
  let h_g0 =
    List.fold_left
      (fun h_g (id, (arg_typs, ret_typ)) ->
        add_global h_g id (TRef (RFun (arg_typs, ret_typ))))
      h
      builtins
  in
  let h_g1 = create_function_ctxt h_g0 p in
  let h_g2 = create_global_ctxt h_g1 p in
  List.iter
    (function
      | Gvdecl _ -> ()
      | Gfdecl ({ elt = f } as l) -> typecheck_fdecl h_g2 f l
      | Gtdecl ({ elt = id, fs } as l) -> typecheck_tdecl h_g2 id fs l)
    p
;;
