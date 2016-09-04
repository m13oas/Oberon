open Ostap.Pretty
open Common
open List

@type 'ref l1_ref = [`Ident of 'ref] with gmap, foldl

@type ('expr, 'ref) l1_expr = [ 'ref l1_ref | 'expr SimpleExpression.expr] with gmap, foldl


@type ('expr, 'ref) res_expr = [ 'expr l1_ref
			       | ('expr, 'ref) l1_expr] with gmap, foldl
  
class ['ref] eval_ref = object 
  inherit ['ref, unit, GT.int, unit, GT.int] @l1_ref
  method c_Ident _ _ id = raise SimpleExpression.Not_a_constant(*id.GT.fx ()*)
end

class ['expr, 'ref] l1_eval = object 
  inherit ['expr, unit, GT.int, 'ref, unit, GT.int, unit, GT.int] @l1_expr
  inherit ['expr] SimpleExpression.eval
  inherit ['ref] eval_ref
end

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

    let reference, expression, declarations, statement, program =
      let reference r = GT.transform(l1_ref) (GT.lift (fun s -> Ostap.Pretty.string s, 0)) (new print_ref) () r in
      let rec expr e = GT.transform(l1_expr) (GT.lift expr) (GT.lift (fun s -> Ostap.Pretty.string s, 0)) (new l1_print SimpleExpression.ob_ps) () e in
      let expr x = fst (expr x) in
      let referenc x = fst (reference x) in
      let decl expr typ (c, t, v) = 
        vert ((ConstDecl.print expr c) @ (TypeDecl.print typ t) @ (VarDecl.print typ v)) 
      in  
      let rec stmt s = 
        GT.transform(SimpleStatement.stmt) 
            (GT.lift stmt) 
            (GT.lift referenc)
            (GT.lift expr)
            (new SimpleStatement.print SimpleStatement.ob_ps)
            ()
            s
      in
      referenc, expr, decl, stmt, (fun m -> Module.print (decl expr PrimitiveType.print) stmt m)
  end

(* --------------------------------------- Name resolver ---------------------------- *)
open Checked

module Resolve =
  struct

  let rec safeLocate e =
  try ulocate e with Not_found ->
    (match e with
     | `Binop (_, x, y) ->
        let l, r = safeLocate x, safeLocate y in
        Ostap.Msg.Locator.makeInterval l r
     | _ -> Ostap.Msg.Locator.No
    )

  class ['expr, 'env, 'rexpr, 'r] resolve = object
  inherit ['expr, 'env, 'rexpr, 'env, 'r] @SimpleExpression.expr
  constraint 'r = ([> `Const of SimpleExpression.const | `Ident of 'e * 'c ] as 'd, Ostap.Msg.t) Checked.t
  method c_Const inh aug   x      =  (*В комментариях верный вызов (через aug), но он возвращает не то что нужно*)
    !! (Common.reloc (safeLocate (*aug.GT.x*)(`Const x) ) (`Const x))
  method c_Unop  inh aug op x   = invalid_arg""
    (*let generate op x = `Unop op x in
    x.GT.fx inh -?->>
    (fun a -> !! (Common.reloc (safeLocate (*aug.GT.x*)(`Unop op x) ) (generate op a) ))*)
  method c_Binop inh aug op x y = invalid_arg""
    (*let generate op x y = `Binop (op, x, y) in
    tuple (x.GT.fx inh, y.GT.fx inh) -?->>
    (fun (a, b) -> !! (Common.reloc (safeLocate (aug.GT.x) ) (generate op a b) ))*)
end
      (*lookUp - преобразователь для ref, возвращает ('rref, Ostap.Msg.t) Checked.t*)
      (*но сама функция возвращает ([> `Ident of 'd * 'rref ], Ostap.Msg.t) Checked.t
    где 'd - результат extactInternal*)
    class ['ref, 'env, 'rref, 'r] resolve_ref = object
      inherit ['ref, 'env, 'rref, 'env, 'r] @l1_ref
      constraint 'rref = ((([> `Const of
                                  [> `Const of SimpleExpression.const | `Ident of 'e * 'c ] as 'd ]
                             as 'c), Ostap.Msg.t) Checked.t)
      constraint 'r = ('d, Ostap.Msg.t) Checked.t
      method c_Ident inh aug x = 
      let reloc = reloc (locate aug.GT.x) in
      (*преобразуем ref так как описано в GT.transform*)
        aug.GT.t#ref inh x.GT.x -?-> 
        (function `Const x -> reloc x | x -> reloc (`Ident (inh#extractInternal x, x)))
    end
        
    class ['expr, 'ref, 'env, 'rexpr, 'rref, 'r] l1_resolve = object
      inherit ['expr, 'env, 'rexpr, 
               'ref,  'env, 'rref,
	                    'env, 'r] @l1_expr
      inherit ['ref, 'env, 'rref, 'r] resolve_ref
      inherit ['expr, 'env, 'rexpr, 'r] resolve
      constraint 'rref = ((([> `Const of
                                  [> `Const of SimpleExpression.const | `Ident of 'e * 'c ] as 'd ]
                             as 'c), Ostap.Msg.t) Checked.t)
      constraint 'r = ([> `Const of SimpleExpression.const | `Ident of 'e * 'c ] as 'd, Ostap.Msg.t) Checked.t
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
        (function `Const (x: [> `Const of SimpleExpression.const]) -> reloc x 
          | (x: [> `Const of
                                  [> `Ident of 'e * 'c ] as 'd ]) 
            -> reloc (`Ident (env#extractInternal x, x)))
      | x -> fail "not a reference" [||] x
	
    let destination env = function
      | `Ident name as ref ->
	  GT.transform(l1_ref) (fun env expr -> env#lookupVar expr) (new resolve_ref) env ref
      | x -> noext x

    let constantExpr env (expr: ('a, 'b) l1_expr) =	
      let rec res env (expr) =
        GT.transform(l1_expr) 
        (fun env expr -> res env expr) (*преобразование еxpr*)
        (fun env expr -> env#lookupConst expr )	(*преобразование ref*)  
        (new l1_resolve) (*класс трансформер*)
        env (*inh атрибут*)
        expr (*что преобразовываем*)
        in
        res env expr
        (*SimpleExpression.resolve (reference (fun env -> env#lookupConst) env) expr*)
-?->> 
      (fun expr ->  
        try !! (reloc (locate expr) (*(let rec eval inh expr = 
					GT.transform(l1_expr) 
					  (eval) 
					  (fun _ _ -> 0) 
					  (new l1_eval) inh expr
				       in SimpleExpression.wrap expr (eval () expr)))*)
		   (SimpleExpression.wrap  expr (SimpleExpression.evaluate expr)))
         with Division_by_zero -> 
           Fail[Ostap.Msg.make "division by zero during constant expression evaluation" 
                  [||] 
                  (locate expr)
           ]
      )
  
    let expression env expr = 
SimpleExpression.resolve (reference lookup env) expr
(*      let rec res_expr env expr = 
	GT.transform(SimpleExpression.expr) 
	  (res_expr)
	  (new SimpleExpression.resolve) env expr in
      let rec res env expr =
	GT.transform(l1_expr) 
	  (res)
	  (fun env expr -> env#lookup expr)
	  (new l1_resolve) env expr in
      res env expr
*)
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
(*    (let rec resstmt env stmt = 
      GT.transform(SimpleStatement.stmt) (resstmt) (destination) (expression) (new SimpleStatement.resolve) (env) (stmt) in
    resstmt env) m*)
	(SimpleStatement.resolve (destination env) (expression env) apply) m
      -?-> (fun x -> x, env#namer ())

end

(* --------------------------------------- Typechecker ------------------------------ *)

module Typecheck =
  struct
    
    let rec typeOfConst = function 
    | (`Ident (_, (`Const _ as v))) -> SimpleExpression.typeOf typeOfConst v 
    | _ -> invalid_arg ""

    let rec safeLocate e =
  try ulocate e with Not_found ->
    (match e with
     | `Binop (_, x, y) ->
        let l, r = safeLocate x, safeLocate y in
        Ostap.Msg.Locator.makeInterval l r
     | _ -> Ostap.Msg.Locator.No
    )

    class ['expr, 'ts, 'r] typecheck = object
  inherit ['expr, 'ts, ('r, Ostap.Msg.t) Checked.t, 
                  'ts, ('r, Ostap.Msg.t) Checked.t] @SimpleExpression.expr
  constraint 'r = (('f, 'l) l1_expr * 'a)
  method c_Const inh aug c = invalid_arg""
(*    let reloc x y = reloc (safeLocate x) y in
    match c with
    | `Literal _ -> !! (reloc aug.GT.x (`Const c), `Int)
    | `True | `False -> !! (reloc aug.GT.x (`Const c), `Bool)*)
  method c_Unop inh aug op x = invalid_arg""
(*)    let reloc x y = reloc (safeLocate x) y in
    (x.GT.fx inh) -?->> (fun ((a,t) as z) ->
      match op with (*(reloc aug.GT.x (`Unop (`Neg, z))) -> 'expr - результат*)
      | `Neg -> Common.int inh (reloc aug.GT.x (`Unop (`Neg, z))) t `Int
      | `Not -> Common.bool inh (reloc aug.GT.x (`Unop (`Not, z))) t `Bool)*)
  method c_Binop inh aug op a b = invalid_arg""
(*)    let reloc x y = reloc (safeLocate x) y in
    tuple (a.GT.fx inh, b.GT.fx inh) -?->> (fun (x, y) -> 
      let t', ensureType =
      match op with          
      | `And | `Or -> `Bool, fun ( l, t) -> Common.bool inh l t `Bool  
      | `Eq  | `Ne  | `Le  | `Lt  | `Ge  | `Gt -> `Bool, fun (l, t) -> Common.int inh l t `Int
      | _ -> `Int, fun (l, t) -> Common.int inh l t `Int
    in
      tuple (ensureType x, ensureType y) -?-> (fun _ -> reloc aug.GT.x (`Binop (op, x, y)), t'))*)
end


    class ['ref, 'env, 'r] typecheck_ref = object
      inherit ['ref, 'env, ('r, Ostap.Msg.t) Checked.t, 'env, ('r, Ostap.Msg.t) Checked.t] @l1_ref
      constraint 'r = (('f, 'l) l1_expr * 'a)
      method c_Ident inh a ref = 
	      match a.GT.x with
        | `Ident (_, `Const _) as x -> !! (x, typeOfConst x)
        | `Ident (_, `Var (_, t)) as x -> !! (x, t)
    end

    class['expr, 'ref, 'env, 'r] l1_typecheck = object
      inherit['ref, 'env, 'r] typecheck_ref
      inherit['expr, 'env, 'r] typecheck
      inherit['expr, 'env, ('r, Ostap.Msg.t) Checked.t, 
              'ref, 'env, ('r, Ostap.Msg.t) Checked.t, 
                    'env, ('r, Ostap.Msg.t) Checked.t] @l1_expr
      constraint 'r = (('f, 'l) l1_expr * 'a)
    end

    let ref ext = function
       | `Ident (_, `Const _) as x -> !! (x, typeOfConst x)

    let reference ext = function
    | `Ident (_, `Const _) as x-> !! (x, typeOfConst x)
    | `Ident (_, `Var (_, t)) as x -> !! (x, t)
    | x -> invalid_arg""

    let declarations ts (c, t, v) =
      let mc, c = 
        resolveDecls (fun x ->
	(*let rec tch env expr =
	    GT.transform(l1_expr) 
	      (tch)			 
        (tch)
	      (new l1_typecheck) 
	      ts 
	      expr in
	tch ts (snd x)*)
	    SimpleExpression.typecheck ts reference (snd x) 
	  -?-> return x) c(*какой-то лист*)
      in
      mc -?-> return (c, t, v)

   let program stmt m =
     let expr e = 
(*       let rec tch inh e =
	 GT.transform(SimpleExpression.expr) (tch) (new SimpleExpression.typecheck) (inh) e in
       tch PrimitiveType.ts e in*)
       SimpleExpression.typecheck PrimitiveType.ts reference e in
     Module.typecheck (declarations PrimitiveType.ts) (stmt PrimitiveType.ts expr apply) m

  end

(* ------------------------------------------ Toplevel ------------------------------ *)

open Lazy
open Checked 

let rec typeOfConst = function 
    | (`Ident (_, (`Const _ as v))) -> SimpleExpression.typeOf typeOfConst v 
    | _ -> invalid_arg ""

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
 (*  method generate  () = force resolved -?-> generate
*)
  end

let toplevel0 s t = toplevel empty s t
let top source = 
(*  let rec l1_expr_typecheck inh e =
    GT.transform(l1_expr) (l1_expr_typecheck) 
      (fun ts y  ->
	match y with
	| (_, `Const _) as x -> !! (`Ident x, typeOfConst (`Ident x))
	| (_, `Var (_, t)) as x -> !! (`Ident x, t)
	| x -> invalid_arg"")
      (new l1_typecheck) inh e in
  let rec sstmttypecheck inh e =
    GT.transform(SimpleStatement.stmt) (sstmttypecheck) (l1_expr_typecheck) (l1_expr_typecheck) (new SimpleStatement.typecheck) inh e in*)
  toplevel0 
    (Parse.program, Print.program, Resolve.program, Typecheck.program (*sstmttypecheck*) SimpleStatement.typecheck)
     source

