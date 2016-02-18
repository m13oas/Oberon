open Ostap.Pretty
open Common
open List

(* ----------------------------------------- Parser --------------------------------- *)

module Parse =
  struct 
    ostap (
      reference: loc[ostap(name:ident {`Ident name})];
      expression: !(SimpleExpression.parse)[reference];
      declarations[typ]: c:!(ConstDecl.parse)[expression]? 
                         t:!(TypeDecl.parse)[typ]?
                         v:!(VarDecl.parse)[typ]? 
      {
        listify c, listify t, listify v
      };
      statement: !(SimpleStatement.parse)[reference][expression][expression][statement];
      program: !(Module.parse)[declarations PrimitiveType.parse][statement]
    )
  end

(* -------------------------------------- Pretty-printer ---------------------------- *)

module Print =
  struct
    let reference, expression, declarations, program =
      let ref  ext = function `Ident name -> string name, 0 | x -> ext x in
      let expr s = SimpleExpression.print ref s in
      let ref  s = fst (ref expr s) in
      let expr s = fst (expr s)     in
      let decl typ (c, t, v) = 
        vert ((ConstDecl.print expr c) @ (TypeDecl.print typ t) @ (VarDecl.print typ v)) 
      in  
      let stmt s = SimpleStatement.print ref expr expr apply s in
      ref, expr, decl, (fun m -> Module.print (decl PrimitiveType.print) stmt m)
  end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked

module Resolve =
  struct

    class ['a] env =
      object(self)
        val idents = Namespace.make "identifier"
        initializer 
          idents#update "INTEGER" (`Type ("int", `Int));
          idents#update "BOOLEAN" (`Type ("int", `Bool));
          idents#downGlobal "global"
     
        method lookup name = (idents#lookupShallow name : ('a, Ostap.Msg.t) t)
        method lookupVar name = 
          self#lookup name -?->> 
          (function 
           | `Var _ as x -> !! (x:'a) 
           | _ -> wrong "variable" name name
          )
        method lookupConst name = 
          self#lookup name -?->> 
          (function 
           | `Const _ as x -> !! (x:'a) 
           | _ -> wrong "constant" name name
          )
        method getInternal name    = idents#getInternal name
        method update      name  v = idents#update name v
        method updateVars  names t = 
          idents#updateList (List.map (fun name -> name, `Var (self#getInternal name, t)) names)
        method updateConst name  v = idents#update name (`Const v)
        method namer () = idents#namer ()
      end

    let lookup     env name = env#lookup    name
    let lookupDest env name = env#lookupVar name

    let noext x = fail "not a reference" [||] x

    let reference lookup env ext = function
    | `Ident name as ref -> 
        let reloc = reloc (locate ref) in
        lookup env name -?-> 
        (function `Const x -> reloc x | x -> reloc (`Ident (name, x)))
    | x -> ext x
    
    let destination env expr = reference lookupDest env noext expr

    let constantExpr env expr = 
      SimpleExpression.resolve 
        (reference (fun env name -> env#lookupConst name) env) 
        expr
      -?->> 
      (fun expr -> 
         try !! (reloc (locate expr) (SimpleExpression.evaluate expr))
         with Division_by_zero -> 
           Fail[Ostap.Msg.make "division by zero during constant expression evaluation" 
                  [||] 
                  (locate expr)
           ]
      )
    let expression env expr = 
       SimpleExpression.resolve (fun self expr -> reference lookup env self expr) expr 

    let typ env t = PrimitiveType.resolve env t

    let declarations typ env (c, t, v) =
      let mc, c = 
        resolveDecls 
          (fun (name, value) -> 
             constantExpr env value  -?->>
             (fun value -> env#updateConst name value -?-> (fun _ -> name, value))
          ) 
          c 
      in
      let mt, t =
        resolveDecls
          (fun (name, t) -> 
             typ env t -?->>
             (fun t -> 
                let iname = env#getInternal name in
                env#update name (`Type (iname, t)) -?-> 
                (fun _ -> iname, t)
             )
          ) 
          t
      in    
      let mv, v = 
        resolveDecls
          (fun (names, t) -> 
             typ env t -?->>
             (fun t -> 
                env#updateVars names t -?-> 
                (fun _ -> List.map (fun name -> env#getInternal name) names, t)
             )
          ) 
          v
      in
      (tuple (mc, tuple (mt, mv)) -?-> (fun _ -> ())), !!(c, t, v)
   
    let program m =
      let env = new env in
      Module.resolve
        env
        (declarations typ)
        (SimpleStatement.resolve 
           (destination env) 
           (constantExpr env)
           (expression env)
           apply 
        )
        m
      -?-> (fun x -> x, env#namer ())

  end

(* --------------------------------------- Typechecker ------------------------------ *)

module Typecheck =
  struct
 
    let rec typeOfConst = function 
    | (`Ident (_, `Const v)) -> SimpleExpression.typeOf typeOfConst v 
    | _ -> invalid_arg ""

    let reference ext = function
    | `Ident (_, `Const _) as x -> !! (x, typeOfConst x)
    | `Ident (_, `Var (_, t)) as x -> !! (x, t)
    | x -> ext x

    let declarations ts (c, t, v) =
      let mc, c = 
        resolveDecls
          (fun (name, value) -> 
             SimpleExpression.typecheck ts (fun self expr -> reference self expr) value -?->
             (fun _ -> name, value)
          )
          c 
      in
      mc -?-> (fun _ -> (c, t, v))

   let program m =
     Module.typecheck
       (declarations PrimitiveType.ts)
       (SimpleStatement.typecheck
          PrimitiveType.ts
          (reference (fun x -> fail "not a reference" [||] x)) 
          (SimpleExpression.typecheck PrimitiveType.ts reference)
          (SimpleExpression.typecheck PrimitiveType.ts reference)
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