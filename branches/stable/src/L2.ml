open Ostap.Pretty
open Common
open List

(* ----------------------------------------- Parser --------------------------------- *)

module Parse = 
  struct 
    open L1.Parse
    ostap (
      statement[ref][cexpr][expr][ext]: 
        !(SimpleStatement.parse)[ref][cexpr][expr][ext]
      | !(ExtendedStatement.parse)[ref][cexpr][expr][ext];
      stmt: statement[reference][expression][expression][stmt];
      program: !(Module.parse)[declarations PrimitiveType.parse][stmt]
    )
  end

(* -------------------------------------- Pretty-printer ---------------------------- *)

module Print =
  struct
    open L1.Print
    let rec statement ref cexpr expr ext s = 
      let self = statement ref cexpr expr ext in
      match s with
      | `For _ | `Case _ -> ExtendedStatement.print ref cexpr expr (fun _ s -> self s) s
      | `Assign _ | `While _ | `If _ -> SimpleStatement.print ref cexpr expr (fun _ s -> self s) s
      | _ -> ext self s
    let program m =
      let stmt s = statement reference expression expression apply s in
      Module.print (declarations PrimitiveType.print) stmt m
  end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked

module Resolve = 
  struct
    open L1
    let rec statement ref cexpr expr ext s =
      let self = statement ref cexpr expr ext in
      match s with
      | `For _ | `Case _ -> ExtendedStatement.resolve ref cexpr expr (fun _ s -> self s) s
      | `Assign _ | `While _ | `If _ -> SimpleStatement.resolve ref cexpr expr (fun _ s -> self s) s
      | _ -> ext self s

    let program m =
      let env = new Resolve.env in
      Module.resolve
        env
        (Resolve.declarations Resolve.typ)      
        (statement
           (Resolve.destination env) 
           (Resolve.constantExpr env)
           (SimpleExpression.resolve (fun self expr -> Resolve.reference Resolve.lookup env self expr))
           apply 
        )
        m -?-> (fun x -> x, env#namer ())
  end

(* --------------------------------------- Typechecker ------------------------------ *)

module Typecheck =
  struct
    open L1
    let rec statement ts ref cexpr expr ext s = 
      let self = statement ts ref cexpr expr ext in
      match s with
      | `For _ | `Case _ -> ExtendedStatement.typecheck ts ref cexpr expr (fun _ s -> self s) s
      | `Assign _ | `While _ | `If _ -> SimpleStatement.typecheck ts ref cexpr expr (fun _ s -> self s) s    
      | _ -> ext self s
    let program m =
      Module.typecheck
        (Typecheck.declarations PrimitiveType.ts)
        (statement
           PrimitiveType.ts
           (Typecheck.reference (fun x -> fail "not a reference" [||] x)) 
           (SimpleExpression.typecheck PrimitiveType.ts Typecheck.reference)
           (SimpleExpression.typecheck PrimitiveType.ts Typecheck.reference)
           apply
        )
        m
  end

(* ------------------------------------------ Toplevel ------------------------------ *)

open Lazy

let top source =
  let parsed   = lazy_from_fun (fun _ -> check (Parse.program (new Lexer.t source))) in
  let resolved = lazy_from_fun (fun _ -> force parsed -?->> Resolve.program) in  
  let checked  = lazy_from_fun (fun _ -> force resolved -?->> (fun t, _ -> Typecheck.program t)) in
  object
    method parse     () = force parsed   -?-> (fun _ -> ())
    method print     () = force parsed   -?-> (fun t -> Ostap.Pretty.toString (Print.program t))
    method resolve   () = force resolved -?-> (fun _ -> ())
    method typecheck () = force checked  -?-> (fun _ -> ())
    method generate  () = force resolved -?-> (fun _ -> "/*** not supported ***/")
  end