open Common

(* ----------------------------------------- Parser --------------------------------- *)

module Parse =
  struct
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

open Ostap.Pretty 

module Print =
  struct
    open L3.Print
    let rec ref p = function 
    | `Index (r, i) -> hovboxed (seq [reference p r; string "["; expression p i; string "]"]), 0
    | `Field (r, f) -> hovboxed (seq [reference p r; string "."; string f]), 0
    | `Ident x -> string (p x), 0
    | x -> expr p x
    and expr       f x = SimpleExpression.print (return (ref f)) x
    and reference  f x = fst (ref  f x)
    and expression f x = fst (expr f x)
    let expr e = expression id e
    let rec typ expr p = CompositeType.print expr ++
      (fun ext -> function
       | (`Int | `Bool) as t -> PrimitiveType.print t 
       | `User x -> string (p x) 
       | x -> ext (typ expr p) x
      ) 
        
    let statement s = statement expr apply s
    let program m = Module.print (declarations expr (typ expr id apply) statement) statement m
  end

module PrintR =
  struct
    let expression e = Print.expression fst e
    let typ t = Print.typ expression (fun (_, s, _) -> s) apply t

    let rec statement s = (L2.Print.statement expression ++
      (fun ext -> function 
       | `Call (name, args, _) -> 
           hov [string name; rboxed (listByCommaBreak (List.map expression args))]
       | s -> ext statement s
      )) apply s

    let program m = Module.print (L3.Print.declarations expression typ statement) statement m
  end

(* --------------------------------------- Name resolver ---------------------------- *)

open Checked

module Resolve =
  struct
    open L3
    let rec typ env = (CompositeType.resolve env (L1.Resolve.constantExpr env) ++
      (fun ext -> function
       | (`Bool | `Int | `User _) as x -> PrimitiveType.resolve env x 
       | t -> ext (typ env) t
      )) apply
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
      | `Field (r, f) -> reference r -?-> (fun r -> reloc (`Field (r, f)))
      | x -> L1.Resolve.reference lookup env ext x
    and expression env expr = SimpleExpression.resolve (reference Resolve.lookup env) expr
    and destination env expr = reference L1.Resolve.lookupDest env L1.Resolve.noext expr
    and declarations restricted env d = Resolve.declarations restricted typ statement env d 
    and statement env stmt = Resolve.statement env destination L1.Resolve.constantExpr expression apply stmt
    let program restricted env m =      
      Module.resolve env (declarations restricted) (statement env) m -?-> (fun x -> x, env#namer ())
  end

(* ---------------------------------------- Typechecker ----------------------------- *)

module Typecheck =
  struct
    open L3
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
        method string x = toString (PrintR.typ x)
      end

    let rec arrayElementType z = function
    | `Array (_, t) -> !! t
    | `User  (_, _, t) -> arrayElementType z t
    | _ -> Fail[Ostap.Msg.make "array type expected" [||] (locate z)]

    let rec arrayLength = function
    | `Array (`Const (`Literal x), _) -> x
    | `User (_, _, t) -> arrayLength t
    | _ -> invalid_arg "should not happen"

    let rec fieldType z name = function
    | `Record f ->
        (try !! (snd (List.find (fun (n, _) -> n = name) f)) with 
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
            tuple (Common.int ts i ti ti, arrayElementType z tr) -?->>
            (fun (i, t) -> 
               match i with
               | `Const (`Literal v), _ -> 
                  if v < 0 || v >= arrayLength tr 
                  then Fail [Ostap.Msg.make "array index out of bounds" [|string_of_int v|] (locate ref)]
                  else !! (reloc (`Index (r, i)), t)
               | _ -> !! (reloc (`Index (r, i)), t)
            )
         )
      | `Field (r, f) ->
         reference r -?->> 
         (fun ((z, t) as r) -> fieldType z f t -?-> (fun t -> reloc (`Field (r, f)), t))
      | x -> Typecheck.reference ext x
    and expression ts expr = SimpleExpression.typecheck ts (reference ts) expr

    let statement ts stmt = Typecheck.statement ts expression apply stmt

    let declarations ts (((_, t, _), _) as d) =  
      let mt, _ = 
        resolveDecls 
          (fun (name, t) -> 
             let rec inner t = (
               CompositeType.cmap  
                 (object
                    method array _  ((s, st) as s') t = 
                      Common.int ts s st `Int -?-> (fun _ -> `Array (s', t))  
                    method record _ f = !! (`Record f)
                  end
                 )
                 (expression ts) ++
                 (fun ext t -> match t with (`Int | `Bool | `User _) as x -> !! x | x -> ext inner x)
              ) apply t 
             in
             inner t -?-> return (name, t)
          ) 
          t 
      in
      tuple (mt, Typecheck.declarations ts statement d) -?-> snd

    let program m = Module.typecheck (declarations ts) (statement ts) m
  
  end

(* ----------------------------------------- Lowering ------------------------------- *)

open List

module Lower =
  struct

    let lower namer s =
      let ostap (
        qexpr[qc]: "$" i:ident {qc i};
        expr [qc]: !(SimpleExpression.parse)[qexpr qc];
        stmt [qc]: !(SimpleStatement.parse)[expr qc][expr qc][stmt qc];
        stmts[qc]: oseq[stmt qc] -EOF
      )
      in
      let quote p context str = uncheck (check (p (fun x -> assoc x context) (new Lexer.t str))) in
      let qe, qs, qss = quote expr, quote stmt, quote stmts in
      let names = ref [] in
      let add (name, typ) = names := ([name], typ) :: !names in
      let module M = SimpleStatement.Mapper (Monad.List) in 
      let module E = ExtendedStatement.Mapper (Monad.List) in
      let ext self stmt =
        E.gmap (object
                  method case _ e b s = 
                    let k = namer#getName "key" in
                    add (k, `Int);
                    let k = `Ident (k, `Var (k, `Int)) in
                    let cond = function 
                    | `Atom e -> qe ["k", k; "e", e] "$k = $e"
                    | `Interval (l, u) -> qe ["k", k; "l", l; "u", u] "($k >= $l) & ($k <= $u)"
                    in                  
                    qs ["k", k; "e", e] "$k := $e" ::
                    [`If (map (fun (h::t, s) -> 
                                fold_left (fun acc c -> qe ["acc", acc; "cond", cond c] "$acc OR $cond") 
                                  (cond h) t,
                                s) b,
                          s)
                    ]
                  method forc _ i l u s b =
                    let upb = namer#getName "upb" in
                    add (upb, `Int);
                    let e, s, ss = 
                      (fun qc -> qe qc, qs qc, qss qc)
                      ["i", i; "u", u; "l", l;
                       "upb", `Ident (upb, `Var (upb, `Int )); 
                       "s"  , match s with None -> `Const (`Literal 1) | Some s -> s] 
                    in
                    ss "$i := $l; $upb := $u" @
                    [`While (e "(($s > 0) & ($i <= $upb)) OR (($s <= 0) & ($i >= $upb))", b @ [s "$i := $i + $s"])]
                end) 
                Monad.List.return 
                Monad.List.return 
                Monad.List.return 
                (return (function `Call (p, a, z) -> [`Call (p, a, z)] | x -> self x))
                stmt
      in
      M.gmap (SimpleStatement.mapT (fun _ s -> [s])) Monad.List.return Monad.List.return ext s, !names

    let program ((name, decls, stmts), namer) =
      let statements stmts =
        let stmts, names = split (map (lower namer) stmts) in
        flatten stmts, flatten names      
      in 
      let rec declarations ((c, t, v), p) =
        ((c, t, v), 
         map (fun (name, args, decls, stmts) ->
                let ((c, t, v), p) = declarations decls in 
                let stmts, names = statements stmts in 
                (name, args, ((c, t, v @ names), p), stmts) 
             ) p
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
          fold_left 
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
          fold_left 
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
      | `Index (r, i) -> hovboxed (seq [rboxed (reference r); string "["; expression i; string "]"]), 0
      | `Field (r, f) -> hovboxed (seq [rboxed (reference r); string "."; string (protect f)]), 0
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
               (vert (map (fun (name, t) -> hov [typ (string (protect name)) t; string ";"]) f)); 
             decl
        ]   

    let rec statement ref cexpr expr = (
      SimpleStatement.print_c expr ++
      (fun ext -> function 
       | `Call (_, args, `Proc (name, fargs)) ->
           hov [string (protect name); 
                rboxed (
                  listByCommaBreak (
                    map 
                      (fun ((t, _, _), e) -> 
                         match t with `Var -> seq [string "&"; rboxed (expr e)] | _ -> expr e
                      ) 
                      (combine fargs args)
                  )
                )
           ]
       | s -> ext (statement ref cexpr expr) s
      )) apply

    let rec declarations typ stmt ((_, t, v), p) =
      vert (
        (TypeDecl.print_c typ t) @ 
        (VarDecl.print_c typ v) @
        (ProcDecl.print_proto_c typ p) @
        (ProcDecl.print_c typ (declarations typ stmt) stmt p)
      )

    let program ((_, ((_, p) as d), _) as m) =       
      let stmt = statement reference expression expression in
      let predefined ((_, t, v), p) =
        let module S = Set.Make (String) in
        let s = fold_left (fun s (name, _, _, _) -> S.add name s) S.empty p in
        let s = fold_left (fun s (name, _) -> S.add name s) s t in
        let s = fold_left 
          (fun s (names, _) -> fold_left (fun s name -> S.add name s) s names) s v 
        in
        let stdprocs =
          fold_left
            (fun acc (name, body) -> if S.mem name s then acc else body :: acc)
            []
            ["Write"  , string "void Write_id (int x){printf (\" %d\", x);}";
             "WriteLn", string "void WriteLn_id (){printf (\"\\n\");}";
             "Read"   , string "void Read_id (int *x){scanf (\"%d\", x);}";
            ]
        in
        match stdprocs with
        | [] -> empty
        | _  -> vert [string "# include <stdio.h>"; 
                      string "typedef int INTEGER_id;"; 
                      string "typedef int BOOLEAN_id;"; 
                      vert stdprocs
                ]
      in
      vert [
        predefined d;
        Module.print_c (declarations typ stmt) stmt m
      ]
      
  end

(* ------------------------------------------ Toplevel ------------------------------ *)

let top source = L1.toplevel 
  (fun (p, n) ->
     let lifted = Lower.program ((Lift.lambda0 (Lift.types p)), n) in
     Ostap.Pretty.toString (PrintR.program lifted), 
     Ostap.Pretty.toString (CGen.program lifted)
  ) (Parse.program, Print.program, Resolve.program true (new L3.Resolve.env), Typecheck.program) source 
