open Testlib
open Util.Assert
open X86
open Ll
module Driver = Oat.Driver
module Backend = Oat.Backend
module Typechecker = Oat.Typechecker
module Frontend = Oat.Frontend
module Tctxt = Oat.Tctxt
module Ast = Oat.Ast
open Backend
open Driver
open Ast

(* Use this file to create additional test cases here to help you   *)
(* debug your comiplper                                             *)

let my_unit_tests =
  let empty = Tctxt.empty in
  let mk_f fieldName ftyp = { fieldName; ftyp } in
  let add_struct id fs h = Tctxt.add_struct h id fs in
  (* an H with S1 <: S2 *)
  let h_s1_s2 =
    empty
    |> add_struct "s1" [ mk_f "x" TInt; mk_f "y" TBool ]
    |> add_struct "s2" [ mk_f "x" TInt ]
  and s1 = TRef (RStruct "s1")
  and s2 = TRef (RStruct "s2") in
  let mk_func args_typs ret_typ = TRef (RFun (args_typs, RetVal ret_typ)) in
  [ ( "subtype: string <: string?"
    , fun () ->
        if Typechecker.subtype empty (TRef RString) (TNullRef RString)
        then ()
        else failwith "should not fail" )
  ; ( "no subtype: string? </: string"
    , fun () ->
        if Typechecker.subtype empty (TNullRef RString) (TRef RString)
        then failwith "should not succeed"
        else () )
  ; ( "no subtype: s1 </: s2 where s2 not in H"
    , fun () ->
        let h = add_struct "s1" [ mk_f "x" TInt ] empty in
        if Typechecker.subtype h s1 s2 then failwith "should not succeed" else () )
  ; ( "no subtype: s1 </: s2 where s1 does not have all s2 fields"
    , fun () ->
        let h =
          empty
          |> add_struct "s1" [ mk_f "x" TInt; mk_f "y" TBool ]
          |> add_struct "s2" [ mk_f "x" TInt; mk_f "z" TBool ]
        in
        if Typechecker.subtype h s1 s2 then failwith "should not succeed" else () )
  ; ( "subtype: s1 <: s2 where s1 has more fields"
    , fun () ->
        let h =
          empty
          |> add_struct "s1" [ mk_f "x" TInt; mk_f "y" TBool; mk_f "z" TInt ]
          |> add_struct "s2" [ mk_f "z" TInt; mk_f "y" TBool ]
        in
        if Typechecker.subtype h s1 s2 then () else failwith "should not fail" )
  ; ( "subtype: int -> int <: int -> int"
    , fun () ->
        if Typechecker.subtype empty (mk_func [ TInt ] TInt) (mk_func [ TInt ] TInt)
        then ()
        else failwith "should not fail" )
  ; ( "not subtype: int -> int </: int -> bool"
    , fun () ->
        if Typechecker.subtype empty (mk_func [ TInt ] TInt) (mk_func [ TInt ] TBool)
        then failwith "should not succeed"
        else () )
  ; ( "not subtype: bool -> int </: int -> int"
    , fun () ->
        if Typechecker.subtype empty (mk_func [ TBool ] TInt) (mk_func [ TInt ] TInt)
        then failwith "should not succeed"
        else () )
  ; ( "not subtype: (int, int) -> int </: int -> int"
    , fun () ->
        if Typechecker.subtype empty (mk_func [ TInt; TInt ] TInt) (mk_func [ TInt ] TInt)
        then failwith "should not succeed"
        else () )
  ; ( "subtype: s1 -> s2 </: s2 -> s1 where s1 <: s2"
    , fun () ->
        if Typechecker.subtype h_s1_s2 (mk_func [ s1 ] s2) (mk_func [ s2 ] s1)
        then failwith "should not succeed"
        else () )
  ; ( "subtype: s1 -> s2 <: s1 -> s2 where s1 <: s2"
    , fun () ->
        if Typechecker.subtype h_s1_s2 (mk_func [ s1 ] s2) (mk_func [ s1 ] s2)
        then ()
        else failwith "should not fail" )
  ; ( "subtype: s2 -> s1 <: s1 -> s2 where s1 <: s2"
    , fun () ->
        if Typechecker.subtype h_s1_s2 (mk_func [ s2 ] s1) (mk_func [ s1 ] s2)
        then ()
        else failwith "should not fail" )
  ; ( "subtype: (s1 -> s2) -> (s2 -> s1) <: (s2 -> s1) -> (s1 -> s2)"
    , fun () ->
        if Typechecker.subtype
             h_s1_s2
             (mk_func [ mk_func [ s1 ] s2 ] (mk_func [ s2 ] s1))
             (mk_func [ mk_func [ s2 ] s1 ] (mk_func [ s1 ] s2))
        then ()
        else failwith "should not fail" )
  ]
;;

let my_tests = [ "test/studentprograms/correct_global_struct.oat" ]
let my_error_tests = [ "test/studentprograms/error_global_struct.oat" ]

let student_local_tests : suite =
  [ Test ("my unit tests", my_unit_tests)
  ; Test ("my tests", typecheck_file_correct my_tests)
  ; Test ("my error tests", typecheck_file_error my_error_tests)
  ]
;;
