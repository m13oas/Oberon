open Ostap.Pretty
open Common
open List
open Ostap.Util

(* ----------------------------------------- Parser --------------------------------- *)

module Parse =
  struct
    open L2
    ostap (  
      declarations[typ][stmt]: 
        d:!(L1.Parse.declarations)[typ]
        p:!(ProcDecl.parse)[typ][declarations typ stmt][stmt]? {d, listify p};
      statement[ref][cexpr][expr]: 
        !(Parse.statement)[ref][cexpr][expr][statement ref cexpr expr] 
      |  loc[ostap (
           name:ident args:(-"(" list0[expr] -")")? {`Call (name, listify args)}
         )];
      stmt   : statement[L1.Parse.reference][L1.Parse.expression][L1.Parse.expression];
      program: !(Module.parse)[declarations PrimitiveType.parse stmt][stmt]
    )
  end

(* -------------------------------------- Pretty-printer ---------------------------- *)

module Print =
  struct
    let rec statement expression = L2.Print.statement expression ++
      (fun ext -> 
	function `Call (name, args) ->  hov [string name; rboxed (listByCommaBreak (map expression args))]
        | s -> ext (statement expression) s
      )   
    let rec declarations expr typ stmt (d, p) =
        vert (
          [L1.Print.declarations expr typ d] @ 
          (ProcDecl.print typ (declarations expr typ stmt) stmt p)
        )
    let program m =
      let stmt s = statement L1.Print.expression apply s in
      Module.print (declarations L1.Print.expression PrimitiveType.print stmt) stmt m
   end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked
open Ostap.Msg

module Resolve =
  struct

    class ['a, 'b] env =
      object(self)
        inherit ['a] L1.Resolve.env
        initializer 
          ignore (self#update "Write" (`Proc ("Write", [`Val, "x", `Int])));
          ignore (self#update "WriteLn" (`Proc ("WriteLn", [])));
          ignore (self#update "WriteHex" (`Proc ("WriteHex", [`Val, "x", `Int])));
          ignore (self#update "Read" (`Proc ("Read", [`Var, "x", `Int])));
          idents#downGlobal "top"

        method extractInternal (x:'a) =
          match x with
          | `Var (iname, _) | `VParam (iname, _) | `Param (iname, _) | `Type (iname, _) -> iname
          | `Proc (iname, _) -> iname
          | `Const _ -> "_const_"

        method lookupProc name = idents#lookup name

        method lookupVar name =
          self#lookup name -?->> 
          (function 
           (`Var _ | `VParam _ | `Param _) as x -> !! (x:'a) 
           | _ -> wrong "variable" name name
          )

        method compositeType (x : [> `Int | `Bool | `User of string * string * 'b] as 'b) = 
          match x with
          | `Int | `Bool -> false
          | `User (_, _, x) -> self#compositeType x
          | _ -> true

        method up   () = idents#up ()
        method down name = idents#down name
      end

    let lookup env name =
      env#lookup name -?->> (function `Proc _  -> wrong "constant/variable" name name | x -> !! x)

    let expression env expr = SimpleExpression.resolve (L1.Resolve.reference lookup env) expr

    let rec statement env reference cexpr expression =
      L2.Resolve.statement (reference env) (cexpr env) (expression env) ++
      (fun ext -> function 
       | `Call (name, aargs) as call -> 
          let reloc = reloc (locate call) in
          env#lookupProc name -?->> 
	  (function 
           | `Proc (_, fargs) as x -> 
               let args =
                 if List.length fargs <> List.length aargs 
                 then Fail [make "%1 argument(s) expected in procedure \"%0\" call but %2 specified" 
                              [|name; string_of_int (List.length fargs); string_of_int (List.length aargs)|] 
                              (locate call)
                          ]
                 else 
                   list (
                     List.map 
                       (fun ((m, name, typ), arg) ->                                
                         (match m with `Var -> reference | `Val -> expression) env arg
                       )
                       (List.combine fargs aargs)
                    )
               in
               args -?-> (fun args -> reloc (`Call (env#extractInternal x, args, x)))
           | _ -> wrong "procedure" name call
          )
       | x -> ext (statement env reference cexpr expression) x
      )

    let stmt env s = statement env L1.Resolve.destination L1.Resolve.constantExpr expression apply s

    let rec declarations restricted typ stmt env (d, p) =
      let m, d = L1.Resolve.declarations typ env d in
      let p = ProcDecl.resolve restricted env (typ env) (declarations restricted typ stmt) (stmt env) p in
      m, tuple (d, p)

    let program m =
      let env = new env in
      Module.resolve env (declarations true PrimitiveType.resolve stmt) (stmt env) m -?->
      (fun x -> x, env#namer ())

  end

(* ---------------------------------------- Typechecker ----------------------------- *)

module Typecheck =
  struct
    let reference ext expr = 
      L1.Typecheck.reference 
        (function 
           (`Ident (_, `VParam (_, t)) | `Ident (_, `Param (_, t))) as x -> !! (x, t) 
         | x -> ext x
        ) 
        expr
    let rec declarations ts stmt (d, p) =
      tuple (
        L1.Typecheck.declarations ts d,  
        ProcDecl.typecheck (declarations ts stmt) (stmt ts) p
      )
    and stmt ts s = statement ts (fun ts -> SimpleExpression.typecheck ts reference) apply s
    and statement ts expression =
      L2.Typecheck.statement ts (expression ts) ++
      (fun ext -> function
       | `Call (name, aargs, `Proc (_, fargs) as p) -> 
            list (
              List.map 
                (fun ((_, farg, typ), arg) -> 
                   expression ts arg -?->> 
                   (fun ((x, t) as arg) ->
                      if ts#equal typ t
                      then !! arg
                      else Fail [make "procedure argument should have type \"%0\"" 
                             [|ts#string typ|] (locate x)
                           ]
                   )
                ) 
                (List.combine fargs aargs)
            ) -?-> (fun aargs -> `Call (name, aargs, p))
       | s -> ext (statement ts expression) s
      )
        
    let program m = Module.typecheck (declarations PrimitiveType.ts stmt) (stmt PrimitiveType.ts) m
  end

(* ------------------------------------------ Toplevel ------------------------------ *)

let top source = L1.toplevel0 (Parse.program, Print.program, Resolve.program, Typecheck.program) source
