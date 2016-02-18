
open Common

(* ----------------------------------------- Parser --------------------------------- *)

module Parse =
  struct

    open Ostap.Combinators

    ostap (  
      reference: loc[ostap (-base:!(L1.Parse.reference) selectors[base])];
      selectors[base]: 
        loc[ostap(
             -sel:(  loc[ostap ("[" i:expression "]" {`Index (base, i)})]
                   | loc[ostap ("." f:ident          {`Field (base, f)})]
                  ) selectors[sel] 
        )]
      | loc[ostap (!(Ostap.Combinators.empty) {base})];
      expression  : !(SimpleExpression.parse)[reference];
      typ         : !(CompositeType.parse)[L1.Parse.expression][PrimitiveType.parse];
      declarations: !(L3.Parse.declarations)[typ][statement];
      statement   : !(L3.Parse.statement)[reference][L1.Parse.expression][expression];
      program     : !(Module.parse)[declarations][statement]
    )

end

(* -------------------------------------- Pretty-printer ---------------------------- *)

module Print =
  struct

    open Ostap.Pretty 

    let rec ref ext = 
    function 
    | `Index (r, i)   -> hovboxed (seq [reference r; string "["; expression i; string "]"]), 0
    | `Field (r, f)   -> hovboxed (seq [reference r; string "."; string f]), 0
    | (`Ident _) as x -> L1.Print.reference x, 0
    | x -> ext x
    and expr       x = SimpleExpression.print ref x
    and reference  x = fst (ref expr x)
    and expression x = fst (expr x)

    let typ t = 
      CompositeType.print expression 
        (fun self t -> 
           match t with (`Int | `Bool | `User _) as t -> PrimitiveType.print t | x -> self x
        ) 
        t

    let statement s = L3.Print.statement reference expression expression s
    let declarations d = L3.Print.declarations typ statement d
    let program m = Module.print (L3.Print.declarations typ statement) statement m

  end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked

module Resolve =
  struct
    module P = Print
    open L3
    let typ env t = 
      CompositeType.resolve 
        env
        (L1.Resolve.constantExpr env) 
        (fun self typ -> 
           match typ with 
            (`Bool | `Int | `User _) as x -> PrimitiveType.resolve env x 
           | _ -> self typ
        ) 
        t
    let rec reference lookup env ext ref = 
      let reference = reference lookup env ext in
      let reloc = reloc (locate ref) in
      match ref with
      | `Index (r, i) -> 
           tuple (reference r, expression env i) -?->>
           (fun (r, i) -> 
              try !! (reloc (`Index (r, SimpleExpression.evaluate i))) with 
              | SimpleExpression.Not_a_constant -> !! (reloc (`Index (r, i)))
              | Division_by_zero -> 
                  Fail [Ostap.Msg.make "division by zero during constant expression evaluation" 
                          [||] 
                          (locate ref)
                  ]
           )
      | `Field (r, f) ->
           reference r -?-> (fun r -> reloc (`Field (r, f)))
      | x -> L1.Resolve.reference lookup env ext x
    and expression env expr =
      SimpleExpression.resolve 
        (fun self expr -> reference L3.Resolve.lookup env self expr) 
        expr
    and destination env expr =
      reference L1.Resolve.lookupDest env L1.Resolve.noext expr
    and declarations restricted env d = L3.Resolve.declarations restricted typ statement env d 
    and statement env stmt =
      L3.Resolve.statement env destination L1.Resolve.constantExpr expression stmt
    let program m = 
      let env = new Resolve.env in
      Module.resolve env (declarations true) (statement env) m -?-> (fun x -> x, env#namer ())

    module Print =
      struct

        open Ostap.Pretty 

        let l1_reference =
          let ref  ext = function `Ident (name, _) -> string name, 0 | x -> ext x in
          let expr s = SimpleExpression.print ref s in
          let ref  s = fst (ref expr s) in
          ref
    
        let rec ref ext = function 
        | `Index (r, i)   -> hovboxed (seq [reference r; string "["; expression i; string "]"]), 0
        | `Field (r, f)   -> hovboxed (seq [reference r; string "."; string f]), 0
        | (`Ident _) as x -> l1_reference x, 0
        | x -> ext x
        and expr       x = SimpleExpression.print ref x
        and reference  x = fst (ref expr x)
        and expression x = fst (expr x)

        let typ t = 
          CompositeType.print expression 
            (fun self t -> 
               match t with (`Int | `Bool | `User _) as t -> PrimitiveType.print t | x -> self x
            ) 
            t

        let statement s = L3.Print.statement reference expression expression s
        let declarations d = L3.Print.declarations typ statement d
        let program m = Module.print (L3.Print.declarations typ statement) statement m

      end

(*      let f e x = snd (declarations true e x) -?-> (fun e -> Print.declarations e) *)

  end

(* ---------------------------------------- Typechecker ----------------------------- *)

module Typecheck =
  struct

    let ts =      
      object(self)
        method primitive = PrimitiveType.ts#primitive
        method equal x y = 
          let rec representer name = function
	  | `User (name', _, x) -> representer name' x
          | _ -> name
          in
          if self#primitive x && self#primitive y 
          then PrimitiveType.ts#equal x y 
          else match x, y with
          | `User (xn, _, x), `User (yn, _, y) -> (representer xn x) = (representer yn y)
          | _ -> false
        method string x = 
          match x with
          | `User (name, _, _) -> name
          | `Array (_, t) -> "ARRAY OF " ^ (self#string t)
          | `Record f -> 
             "RECORD" ^ 
               (List.fold_left 
                  (fun acc (name, t) -> 
                     (if acc = "" then "" else "; ") ^ name ^ " : " ^ (self#string t)
                  ) 
                  "" 
                  f
               ) ^ 
             " END"
          | `Int -> "INTEGER"
          | `Bool -> "BOOLEAN"
      end

    let rec arrayElementType z = function
    | `Array (_, t) -> !! t
    | `User  (_, _, t) -> arrayElementType z t
    | _ -> Fail[Ostap.Msg.make "array type expected" [||] (locate z)]

    let rec arrayLength = function
    | `Array (`Const x, _) -> x
    | `User (_, _, t) -> arrayLength t
    | _ -> invalid_arg "should not happen"

    let rec fieldType z name = function
    | `Record f ->
        (try
          !! (snd (List.find (fun (n, _) -> n = name) f))
         with 
         | Not_found -> Fail [Ostap.Msg.make "record type does not have field \"%0\"" 
                               [|name|] (locate name)
                             ]
        )   
        | `User (_, _, t) -> fieldType z name t
        | _ -> Fail [Ostap.Msg.make "record type expected" [||] (locate z)]

    let rec reference ts ext ref = 
      let reference = reference ts ext in
      let reloc = reloc (locate ref) in
      match ref with
      | `Index (r, i) -> 
         tuple (reference r, expression ts i) -?->>
         (fun ((z, tr) as r, (i, ti)) -> 
            tuple (int ts i ti ti, arrayElementType z tr) -?->>
            (fun (i, t) -> 
               match i with
               | `Const v, _ -> 
                  if v < 0 || v >= arrayLength tr 
                  then Fail [Ostap.Msg.make "array index out of bounds" [|string_of_int v|] (locate ref)]
                  else !! (reloc (`Index (r, i)), t)
               | _ -> !! (reloc (`Index (r, i)), t)
            )
         )
      | `Field (r, f) ->
         reference r -?->> 
         (fun (z, t) as r -> fieldType z f t -?-> (fun t -> reloc (`Field (r, f)), t))
      | x -> L3.Typecheck.reference ext x
    and expression ts expr = SimpleExpression.typecheck ts (reference ts) expr

    let statement ts stmt =
      L3.Typecheck.statement 
        ts 
        (fun ts r -> reference ts L1.Resolve.noext r) 
        expression
        stmt

    let declarations ts ((_, t, _), _) as d =  
      let mt, _ = 
        resolveDecls 
          (fun (name, t) -> 
             let rec inner t =
               CompositeType.cmap 
                 (expression ts) 
                 (function (`Int | `Bool | `User _) as x -> !! x | x -> inner x) 
                 (function 
                  | `Array ((s, st), t) as x -> Common.int ts s st `Int -?-> (fun _ -> x)  
                  | x -> !! x
                 ) 
                 t 
             in
             inner t -?-> (fun _ -> name, t)
          ) 
          t 
      in
      tuple (mt, L3.Typecheck.declarations ts statement d) -?-> snd

    let program m = Module.typecheck (declarations ts) (statement ts) m
  
  end

(* ----------------------------------------- Lowering ------------------------------- *)

module Lower =
  struct

    let lower namer stmt = 
      let names = ref [] in
      let add (name, typ) = names := ([name], typ) :: !names in
      let rec inner = 
        let f x = List.flatten (List.map inner x) in
        function
        | `For (i, l, u, s, b) ->
           let s = match s with None -> `Const 1 | Some s -> s in
           let upb = namer#getName "upb" in
           add (upb, `Int);
           let upb = `Ident (upb, `Var (upb, `Int )) in
           [`Assign (i, l);
            `Assign (upb, u);
            `While (
               `Binop (`Or, 
                  `Binop (`And, `Binop (`Gt, s, `Const 0), `Binop (`Le, i, upb)), 
                  `Binop (`And, `Binop (`Le, s, `Const 0), `Binop (`Ge, i, upb))
                ), 
               f b @ [`Assign (i, `Binop (`Add, i, s))]
             )
           ]
        | `While (c, b) -> [`While (c, f b)]
        | `If (b, e) -> [`If (List.map (fun c, e -> c, f e) b, f e)]
        | `Case (key, b, e) ->            
           let k = namer#getName "key" in
           add (k, `Int);
           let k = `Ident (k, `Var (k, `Int)) in
           let cond = function 
           | `Atom e -> `Binop (`Eq, k, e) 
           | `Interval (l, u) -> `Binop (`And, (`Binop (`Ge, k, l)), (`Binop (`Le, k, u)))
           in
           [`Assign (k, key);
            `If (
               List.map 
                (fun h::t, s -> 
                   List.fold_left (fun acc c -> `Binop (`Or, acc, cond c)) (cond h) t,
                   f s
                ) b,
               f e
             )
           ]
        | x -> [x]
      in
      inner stmt, !names

    let program ((name, decls, stmts), namer) =
      let statements stmts =
        let stmts, names = List.split (List.map (lower namer) stmts) in
        List.flatten stmts, List.flatten names      
      in 
      let rec declarations ((c, t, v), p) =
        ((c, t, v), 
         List.map  
            (fun (name, args, decls, stmts) ->
               let ((c, t, v), p) = declarations decls in 
               let stmts, names = statements stmts in 
               (name, args, ((c, t, v @ names), p), stmts) 
            )
            p
        )
      in 
      let ((c, t, v), p) = declarations decls in
      let stmts, names = statements stmts in
      (name, ((c, t, v @ names), p), stmts)      

  end

(* ------------------------------------------ Lifting ------------------------------- *)

module Lift =
  struct

    let types (name, d, stmts) =
      let rec decls acc ((c, t, v), p) = 
        let d, p' =
          List.fold_left 
            (fun (lifted, rest) (name, args, d, stmts) ->  
               let lifted', d' = decls lifted d in
               lifted', (name, args, d', stmts) :: rest
            ) 
            (t @ acc, [])
            p
        in
        d, ((c, [], v), p')
      in
      let lifted, ((c, t, v), p) = decls [] d in
      (name, ((c, lifted @ t, v), p), stmts)

    let lambda0 (name, d, stmts) =
      let rec decls acc ((c, t, v), p) = 
        let d, p' =
          List.fold_left 
            (fun (lifted, rest) (name, args, d, stmts) ->  
               let lifted', d' = decls lifted d in
               lifted', (name, args, d', stmts) :: rest
            ) 
            (acc, [])
            p
        in
        d @ p', ((c, t, v), [])
      in
      let lifted, ((c, t, v), p) = decls [] d in
      (name, ((c, t, v), lifted), stmts)
      
  end

(* ---------------------------------------- C generator ----------------------------- *)

module CGen =
  struct
    open Ostap.Pretty
   
    let protect name = name ^ "_id"

    let reference, expression =
      let rec ref ext = function 
      | `Ident (_, `VParam (name, _)) -> string ("*" ^ (protect name)), 0
      | `Ident (_, `Param  (name, _)) -> string (protect name), 0
      | `Ident (_, `Var (name, _)) -> string (protect name), 0 
      | `Ident (name, _) -> string (protect name), 0 
      | `Index (r, i)   -> hovboxed (seq [rboxed (reference r); string "["; expression i; string "]"]), 0
      | `Field (r, f)   -> hovboxed (seq [rboxed (reference r); string "."; string (protect f)]), 0
      | x -> ext x       
      and expr s = SimpleExpression.print_c ref s 
      and reference  s = fst (ref expr s) 
      and expression s = fst (expr s) in
      reference, expression

    let rec typ decl = function
    | `User (name, iname, _) -> hov [string (protect iname); decl]
    | `Int | `Bool -> hov [string "int"; decl]
    | `Array (s, t) -> typ (hov [decl; sboxed (expression s)]) t
    | `Record f -> 
        hov [sblock "struct {" "}" 
               (vert (List.map (fun (name, t) -> hov [typ (string (protect name)) t; string ";"]) f)); 
             decl
        ]   

    let statement ref cexpr expr stmt =
      SimpleStatement.print_c ref cexpr expr 
        (fun self s -> 
           match s with 
           | `Call (_, args, `Proc (name, fargs)) ->                
               hov [string (protect name); 
                    rboxed (
                      listByCommaBreak (
                        List.map 
                          (fun ((t, _, _), e) -> 
                             match t with `Var -> seq [string "&"; rboxed (expr e)] | _ -> expr e
                          ) 
                          (List.combine fargs args)
                      )
                    )
               ]
           | _ -> self s
        )  
        stmt

    let rec declarations typ stmt ((_, t, v), p) =
      vert (
        (TypeDecl.print_c typ t) @ 
        (VarDecl.print_c typ v) @
        (ProcDecl.print_proto_c typ p) @
        (ProcDecl.print_c typ (declarations typ stmt) stmt p)
      )

    let program (_, ((_, p) as d), _) as m =       
      let stmt = statement reference expression expression in
      let predefined ((_, t, v), p) =
        let module S = Set.Make (String) in
        let s = List.fold_left (fun s (name, _, _, _) -> S.add name s) S.empty p in
        let s = List.fold_left (fun s (name, _) -> S.add name s) s t in
        let s = List.fold_left 
          (fun s (names, _) -> 
             List.fold_left (fun s name -> S.add name s) s names
          ) s v 
        in
        let stdprocs =
          List.fold_left
            (fun acc (name, body) ->
               if S.mem name s then acc 
               else body :: acc
            )
            []
            ["Write"  , string "void Write_id (int x){printf (\" %d\", x);}";
             "WriteLn", string "void WriteLn_id (){printf (\"\\n\");}";
             "Read"   , string "void Read_id (int *x){scanf (\"%d\", x);}";
            ]
        in
        match stdprocs with
        | [] -> empty
        | _  -> vert [string "# include <stdio.h>"; string "typedef int int_id;"; vert stdprocs]
      in
      vert [
        predefined d;
        Module.print_c (declarations typ stmt) stmt m
      ]
      
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
    method generate  () = force resolved -?-> (fun (p, n) -> 
                                                 Ostap.Pretty.toString (
                                                   CGen.program (Lower.program ((Lift.lambda0 (Lift.types p)), n))
                                                 )
                                              )
  end
