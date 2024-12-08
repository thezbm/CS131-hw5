open Testlib
open Util.Assert
open X86
open Ll
module Driver = Oat.Driver
module Backend = Oat.Backend
module Typechecker = Oat.Typechecker
module Frontend = Oat.Frontend
module Tctxt = Oat.Tctxt
open Backend
open Driver

(* Use this file to create additional test cases here to help you   *)
(* debug your comiplper                                             *)

let my_unit_tests =
  [ ( "subtype: string <: string?"
    , fun () ->
        if Typechecker.subtype Tctxt.empty (TRef RString) (TNullRef RString)
        then ()
        else failwith "should not fail" )
  ; ( "no subtype: string? </: string"
    , fun () ->
        if Typechecker.subtype Tctxt.empty (TNullRef RString) (TRef RString)
        then failwith "should not succeed"
        else () )
  ]
;;

let my_tests =
  [ "test/studentprograms/correct_global_struct.oat"
  ]
;;

let my_error_tests =
  [ "test/studentprograms/error_global_struct.oat"
  ]
;;

let student_local_tests : suite =
  [ Test ("my unit tests", my_unit_tests)
  ; Test ("my tests", typecheck_file_correct my_tests)
  ; Test ("my error tests", typecheck_file_error my_error_tests)
  ]
;;
