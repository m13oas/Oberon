open Ostap.Pretty
open Common
open List

(* ----------------------------------------- Parser --------------------------------- *)

module Parse = 
  struct 
    open L1.Parse
    ostap (
      statement[ref][cexpr][expr][stmt]: 
        !(SimpleStatement.parse)[ref][expr][stmt]
      | !(ExtendedStatement.parse)[ref][cexpr][expr][stmt];
      stmt   : statement[reference][expression][expression][stmt];
      program: !(Module.parse)[declarations PrimitiveType.parse][stmt]
    )
  end

(* -------------------------------------- Pretty-printer ---------------------------- *)

module Print =
  struct
    open L1.Print
    let statement expr = statement expr ++ ExtendedStatement.print expr
    let program m = Module.print (declarations expression PrimitiveType.print) (statement expression apply) m
  end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked

module Resolve = 
  struct
    open L1.Resolve
    let statement ref cexpr expr = SimpleStatement.resolve ref expr ++ ExtendedStatement.resolve ref cexpr expr 
    let program m =
      let env = new env in
      Module.resolve
        env
        (declarations PrimitiveType.resolve)
        (statement
           (destination env) 
           (constantExpr env)
           (SimpleExpression.resolve (reference lookup env))
           apply 
        )
        m -?-> (fun x -> x, env#namer ())
  end

(* --------------------------------------- Typechecker ------------------------------ *)

module Typecheck =
  struct
    open L1.Typecheck
    let rec statement ts expr = SimpleStatement.typecheck ts expr ++ ExtendedStatement.typecheck ts expr
    let program m = program statement m
  end

(* ------------------------------------------ Toplevel ------------------------------ *)

let top source = L1.toplevel0 (Parse.program, Print.program, Resolve.program, Typecheck.program) source
