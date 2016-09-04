open Ostap.Pretty
open Common
open List

@type ('stmt, 'a, 'expr, 'ref) l2_stmt = [ ('stmt, 'a, 'expr, 'ref) ExtendedStatement.extstmt 
						      | ('stmt, 'ref, 'expr) SimpleStatement.stmt] with gmap, foldl

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
open Ostap.Pretty

(*let rec stat (expr: ('a, 'b, 'c, 'd) ExtendedStatement.extstmt) =
    GT.transform(ExtendedStatement.extstmt) 
      (GT.lift (fun s -> Ostap.Pretty.empty))
      (GT.lift (fun s -> Ostap.Pretty.empty))
      (GT.lift L1.Print.expression) 
      (GT.lift (fun s -> Ostap.Pretty.empty)) 
      (new ExtendedStatement.print) () expr 
*)
module Print =
  struct
    open L1.Print
(*)    class['stmt, 'a, 'expr, 'ref] l2_print = object
      inherit ['stmt,    unit, printer,
               'a,       unit, string,
	             'expr,    unit, printer, 
	             'ref,     unit, printer, 
                         unit, printer] @l2_stmt
     method c_While _ _ expr stmt = invalid_arg""
     method c_If     _ a ifprt elprt = invalid_arg""
     method c_Assign _ _  ref expr   = invalid_arg""
     method c_Case _ a e b elsePart = invalid_arg""
     method c_For _ a i l u s b = invalid_arg""
    end
*)
      let express (e: ('a, string ) L1.l1_expr) = expression e
      let refer e = L1.Print.reference e
      (*let stat e = L1.Print.statement e*)
      let a s = Ostap.Pretty.string s
    
  

    let statement (expr: [ ('a,'b,'c, 'd) l2_stmt]) = invalid_arg""
(*)      GT.transform(l2_stmt) 
      (GT.lift exststmt)
      (GT.lift statement)
      (GT.lift expression) 
      (GT.lift reference) 
      (new l2_print) () expr in
    exststmt expr*)
      (*let atom a = GT.transform(ExtendedStatement.atom) (GT.lift expr) (new ExtendedStatement.print_atom) () a in*)
    
(*      statement expr ++ ExtendedStatement.print expr*)

    let program m = invalid_arg""(*Module.print (declarations expression PrimitiveType.print) (exststmt) m*)
  end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked

module Resolve = 
  struct
    open L1.Resolve
    let statement ref cexpr expr = invalid_arg"" (*SimpleStatement.resolve ref expr ++ ExtendedStatement.resolve ref cexpr expr *)
    let program m = invalid_arg""
      (*let env = new env in
      Module.resolve
        env
        (declarations PrimitiveType.resolve)
        (statement
           (destination env) 
           (constantExpr env)
           (SimpleExpression.resolve (reference lookup env))
           apply 
        )
        m -?-> (fun x -> x, env#namer ())*)
  end

(* --------------------------------------- Typechecker ------------------------------ *)

module Typecheck =
  struct
    open L1.Typecheck
    let rec statement ts expr = invalid_arg"" (*SimpleStatement.typecheck ts expr ++ ExtendedStatement.typecheck ts expr*)
    let program m = invalid_arg""(*program statement m*)
  end

(* ------------------------------------------ Toplevel ------------------------------ *)

let top source = L1.toplevel0 (Parse.program, Print.program, Resolve.program, Typecheck.program) source

