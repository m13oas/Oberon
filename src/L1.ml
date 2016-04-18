open Ostap.Pretty
open Common
open List

@type 'ref l1_ref = [`Ident of 'ref] with gmap, foldl

@type ('expr, 'ref) l1_expr = [ 'ref l1_ref | 'expr SimpleExpression.expr] with gmap, foldl

(* ----------------------------------------- Parser --------------------------------- *)

module Parse =
  struct
    ostap (reference: loc[ostap(name:ident {`Ident name})]) 
    ostap (      
      expression: !(SimpleExpression.parse)[reference];
      declarations[typ]: c:!(ConstDecl.parse)[expression]? 
                         t:!(TypeDecl.parse)[typ]?
                         v:!(VarDecl.parse)[typ]? {
        listify c, listify t, listify v
      };
      statement: !(SimpleStatement.parse)[reference][expression][statement];
      program: !(Module.parse)[declarations PrimitiveType.parse][statement]
    )
  end

(* -------------------------------------- Pretty-printer ---------------------------- *)

module Print =
  struct
    class ['ref] print_ref = object
      inherit ['ref, unit, Ostap.Pretty.printer * int, unit, Ostap.Pretty.printer * int] @l1_ref
      method c_Ident _ _ id = id.GT.fx ()
    end

    class ['expr, 'ref] l1_print ps = object
      inherit ['expr, unit, printer * int, 'ref, unit, printer * int, unit, printer * int] @l1_expr
      inherit ['expr] SimpleExpression.print ps
      inherit ['ref]  print_ref
    end

    let expression, declarations, statement, program =
      let reference r = GT.transform(l1_ref) (GT.lift (fun s -> Ostap.Pretty.string s, 0)) (new print_ref) () r in
      let rec expr e = GT.transform(l1_expr) (GT.lift expr) (GT.lift (fun s -> Ostap.Pretty.string s, 0)) (new l1_print SimpleExpression.ob_ps) () e in
      let expr x = fst (expr x) in
      let reference x = fst (reference x) in
      let decl expr typ (c, t, v) = 
        vert ((ConstDecl.print expr c) @ (TypeDecl.print typ t) @ (VarDecl.print typ v)) 
      in  
      let rec stmt s = 
        GT.transform(SimpleStatement.stmt) 
            (GT.lift stmt) 
            (GT.lift reference)
            (GT.lift expr)
            (new SimpleStatement.print SimpleStatement.ob_ps)
            ()
            s
      in
      expr, decl, stmt, (fun m -> Module.print (decl expr PrimitiveType.print) stmt m)
  end

(* --------------------------------------- Name resolver ---------------------------- *)
open Checked

module Resolve =
  struct
    class ['ref, 'env, 'r] resolve_const_ref = object
      inherit ['ref, 'env, ('r, Ostap.Msg.t) Checked.t, 'env, ('r, Ostap.Msg.t) Checked.t] @l1_ref
      method c_Ident inh a x = x.GT.fx inh
    end
      
    class ['ref, 'env, 'r] resolve_ref = object
      inherit ['ref, 'env, ('r, Ostap.Msg.t) Checked.t, 'env, ('r, Ostap.Msg.t) Checked.t] @l1_ref
      method c_Ident inh a x = x.GT.fx inh
    end

    class ['expr, 'ref, 'env, 'r] l1_resolve_conexpr_old = object
      inherit ['expr, 'env, ('r, Ostap.Msg.t) Checked.t, 'ref, 'env, ('r, Ostap.Msg.t) Checked.t, 'env, ('r, Ostap.Msg.t) Checked.t] @l1_expr
      inherit ['expr, 'env, 'r] SimpleExpression.resolve
      inherit ['ref, 'env, 'r] resolve_const_ref
    end  

    class ['expr, 'ref, 'env, 'r] l1_resolve_expr = object
      inherit ['expr, 'env, ('r, Ostap.Msg.t) Checked.t, 'ref, 'env, ('r, Ostap.Msg.t) Checked.t, 'env, ('r, Ostap.Msg.t) Checked.t] @l1_expr
      inherit ['expr, 'env, 'r] SimpleExpression.resolve
      inherit ['ref, 'env, 'r] resolve_const_ref
    end
    
    class ['a] env =
      object(self)
        val idents = Namespace.make "identifier"
        initializer 
          idents#update "INTEGER" (`Type ("INTEGER", `Int));
          idents#update "BOOLEAN" (`Type ("BOOLEAN", `Bool));
          idents#downGlobal "global"
        method extractInternal (x:'a) = 
          match x with 
          | `Var (iname, _) | `Type (iname, _) -> iname | `Const _ -> "_const_"
          | _ -> invalid_arg "should not happen"             
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
      (function `Const x -> reloc x | x -> reloc (`Ident (env#extractInternal x, x)))
    | x -> invalid_arg ""

    let destination env expr = 
      GT.transform(l1_ref) (fun env expr -> 
	  let reloc = reloc (locate (`Ident expr)) in
          env#lookupVar expr -?-> 
	    (function `Const x -> reloc x | x -> reloc (`Ident (env#extractInternal x, x)))) (new resolve_ref) env expr

    let constantExpr env expr = 
      let rec res env expr =
	GT.transform(l1_expr) (res)
	  (
	    fun env expr -> 
	  let reloc = reloc (locate (`Ident expr)) in
          env#lookupConst expr -?-> 
	    (function `Const x -> reloc x | x -> reloc (`Ident (env#extractInternal x, x)))
	  )
	  (new l1_resolve_conexpr_old) env expr in
      res env expr -?->> 
      (fun expr -> 
         try !! (reloc (locate expr) (SimpleExpression.evaluate expr))
         with Division_by_zero -> 
           Fail[Ostap.Msg.make "division by zero during constant expression evaluation" 
                  [||] 
                  (locate expr)
           ]
      )

    let expressionGT env expr =
      let rec res env expr =
	GT.transform(l1_expr) (res)
	  (
	    fun env expr -> 
	  let reloc = reloc (locate (`Ident expr)) in
          env#lookup expr -?-> 
	    (function `Const x -> reloc x | x -> reloc (`Ident (env#extractInternal x, x)))
	  )
	  (new l1_resolve_conexpr_old) env expr in
      res env expr
  
(*стандартный l1_expr*)
    let expression env (expr) =
      let rec res env expr =
	GT.transform(l1_expr) (res)
	  (
	    fun env expr -> 
	  let reloc = reloc (locate (`Ident expr)) in
          env#lookup expr -?-> 
	    (function `Const x -> reloc x | x -> reloc (`Ident (env#extractInternal x, x)))
	  )
	  (new l1_resolve_conexpr_old) env expr in
      res env expr
(*	SimpleExpression.resolve (reference lookup env) expr*)

    let declarations typ env (c, t, v) =
      let mc, c = 
        resolveDecls 
          (fun (name, value) -> 
             constantExpr env value  -?->>
             (fun value -> env#updateConst name value -?-> return (name, value))
          ) 
          c 
      in
      let mt, t =
        resolveDecls
          (fun (name, t) -> 
             typ env t -?->>
             (fun t -> 
                let iname = env#getInternal name in
                env#update name (`Type (iname, t)) -?-> return (iname, t)
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
                return (List.map (fun name -> env#getInternal name) names, t)
             )
          ) 
          v
      in
      (tuple (mc, tuple (mt, mv)) -?-> return ()), !!(c, t, v)
   
    let program m =
      let env = new env in
      Module.resolve
        env
        (declarations PrimitiveType.resolve)
        (SimpleStatement.resolve (destination env) (expression env) apply)
        m
      -?-> (fun x -> x, env#namer ())

end

(* --------------------------------------- Typechecker ------------------------------ *)

module Typecheck =
  struct
 
(*    class['expr, 'ref, 'ts, 'r] l1_typecheck ts = object
      inherit['expr, 'ts, 'r, 'ref, 'ts, 'r, 'ts, ('r, Ostap.Msg.t) Checked.t] @l1_expr
      inherit['expr, 'ts, 'r] SimpleExpression.typecheck (SimpleExpression.tch_ob ts)
      method c_Ident inh a x =
	let rec typeOfConst = function 
	  | (`Ident (_, (`Const _ as v))) -> SimpleExpression.typeOf typeOfConst v 
	  | _ -> invalid_arg "" in
	match x.GT.x with
	| (_, `Const _) -> !! (`Ident x.GT.x, typeOfConst x.GT.x)
	| (_, `Var (_, t)) -> !! (`Ident x.GT.x,t)
	| x -> invalid_arg""
    end
*)
    let rec typeOfConst = function 
    | (`Ident (_, (`Const _ as v))) -> SimpleExpression.typeOf typeOfConst v 
    | _ -> invalid_arg ""

    let reference ext = function
    | `Ident (_, `Const _) as x -> !! (x, typeOfConst x)
    | `Ident (_, `Var (_, t)) as x -> !! (x, t)
    | x -> ext x

    let declarations (ts: < equal : [> `Bool | `Int ] -> [> `Bool | `Int ] -> bool; .. >) (c, t, v) =
      let mc, c = 
        resolveDecls (fun x -> SimpleExpression.typecheck ts reference ((snd x)) -?-> return x) c 
      in
      mc -?-> return (c, t, v)

   let program stmt m =
     let expr e = SimpleExpression.typecheck PrimitiveType.ts reference e in
     Module.typecheck (declarations PrimitiveType.ts) (stmt PrimitiveType.ts expr apply) m

  end

(* ------------------------------------------ Toplevel ------------------------------ *)

class ['ref] eval_ref = object 
  inherit ['ref, unit, GT.int, unit, GT.int] @l1_ref
  method c_Ident _ _ id = id.GT.fx ()
end

class ['expr, 'ref] l1_eval = object 
  inherit ['expr, unit, GT.int, 'ref, unit, GT.int, unit, GT.int] @l1_expr
  inherit ['expr] SimpleExpression.eval
  inherit ['ref] eval_ref
end


open Lazy
open Checked 

let empty _ = "(*** not supported ***)", "/*** not supported ***/"

let toplevel generate (parse, print, resolve, typecheck) source =
  let parsed   = lazy_from_fun (fun _ -> check (parse (new Lexer.t source))) in
  let resolved = lazy_from_fun (fun _ -> force parsed -?->> resolve) in  

  let checked  = lazy_from_fun (fun _ -> force resolved -?->> (fun (t, _) -> typecheck t)) in

  object
    method parse     () = force parsed   -?-> return ()
    method print     () = force parsed   -?-> (fun t -> Ostap.Pretty.toString (print t))
    method resolve   () = force resolved -?-> return ()
    method typecheck () = force checked  -?-> (fun x -> return ())
(*    method generate  () = force resolved -?-> generate
*)
  end

let toplevel0 s t = toplevel empty s t
let top source = 
  toplevel0 
     (Parse.program, Print.program, Resolve.program , Typecheck.program SimpleStatement.typecheck) 
     source

