open Ostap.Util
open Common

(* ----------------------------------------- Parser --------------------------------- *)

ostap (
  procedureHeading[typ]: key["PROCEDURE"] name:ident args:formalParameters[typ]? {
    name, listify args
  };
  parameterSection[typ]: var:key["VAR"]? args:list[ident] ":" typ:typ {
   let m = match var with Some _ -> `Var | None -> `Val in
    List.map (fun arg -> m, arg, typ) args
  };
  formalParameters[typ]: "(" args:seq[ostap(parameterSection[typ])]? ")" {
    List.flatten (listify args)
  };
  procedureBody[decl][stmt]: decl (-key["BEGIN"] oseq[stmt])?;
  procedureDeclaration[typ][decl][stmt]:
     <(name, args)>  : procedureHeading[typ] ";" 
     <(decls, body)> : procedureBody[decl][stmt] 
     procedureEnd[name] {
    name, args, decls, listify body
  };
  procedureEnd[expectedName]: -key["END"] -expect[expectedName] -";";
  parse[typ][decl][stmt]: procedureDeclaration[typ][decl][stmt]+
)

(* -------------------------------------- Pretty-printer ---------------------------- *)

open Ostap.Pretty
open List

let print typ decl stmt =
  let parameter (v, name, t) =
    hov (
      (match v with `Var -> [string "VAR"] | `Val -> []) @
      [string name; string ":"; typ t]
    )
  in  
  let formalParameters args =
    rboxed (hvboxed (mseq parameter args))
  in
  let procedureBody decls stmts =
    vert (
      [decl decls] @
      (match stmts with 
       | [] -> [empty] 
       | _  -> [plock (string "BEGIN") (mseq stmt stmts)]
      )
    )
  in
  let declaration (name, args, decls, stmts) =
    vert [
      hov [string "PROCEDURE"; string name; seq [formalParameters args; string ";"]];
      procedureBody decls stmts;
      hov [string "END"; seq [string name; string ";"]]
    ]
  in
  function [] -> [] | t -> [vert (List.map declaration t)]

let print_header_c typ (name, args, _, _) =
  let parameter (v, name, t) = 
    typ (string ((match v with `Var -> "*"| `Val -> "") ^ name ^ "_id")) t 
  in  
  let formalParameters args =
    rboxed (hvboxed (listByCommaBreak (List.map parameter args)))
  in
  hov [string "void"; string (name ^ "_id"); formalParameters args]

let print_proto_c typ =
  let declaration p =
    vert [seq [print_header_c typ p; string ";"]]
  in
  function [] -> [] | t -> [vert (List.map declaration t)]
  
let print_c typ decl stmt =
  let procedureBody decls stmts =
    vert (
      [decl decls] @
      (match stmts with 
       | [] -> [] 
       | _  -> [seq [mseq stmt stmts; string ";"]]
      )
    )
  in
  let declaration ((name, args, decls, stmts) as p) =
    vert [
      print_header_c typ p;
      sblock "{" "}" (procedureBody decls stmts);
    ]
  in
  function [] -> [] | t -> [vert (List.map declaration t)]

(* ------------------------------------- Name resolver ------------------------------ *)

open Checked

let resolve restricted env typ decl stmt pdecls =
  let resolveArgs args =
    list (
      List.map 
        (fun (v, name, t) -> 
           typ t -?->> 
           (function 
              (`User _ | `Bool | `Int) as t -> 
              (match v with
               | `Var -> !!(v, name, t)
               | _ -> if env#compositeType t 
                      then Fail [Ostap.Msg.make 
                                   "composite type arguments should be declared as VAR" 
                                   [||] 
                                   (locate name)
                                ]
                      else !!(v, name, t)
              )
               
            | _ -> Fail [Ostap.Msg.make 
                           "type name expected in procedure parameter declaration" 
                            [||] 
                            (locate name)
                        ]
           )
        ) args
    )
  in
  let inner ((name, args, decls, stmts) as t) =
    let iname = env#getInternal name in
    env#down iname;    
    let args' = List.map (fun (v, name, t) -> v, env#getInternal name, t) args in 
    let msg' = list (
      List.map 
        (fun (v, name, t) -> 
           let iname = env#getInternal name in
           env#update name (match v with `Var -> `VParam (iname, t) | _ -> `Param (iname, t))
        ) 
        args
    ) -?-> (fun _ -> ())
    in
    let msg'', decls = decl env decls in
    ignore (env#update name (`Proc (iname, args)));
    let stmts = list (List.map stmt stmts) in
    env#up ();
    env#update name (`Proc (iname, args)) -?->>
    (fun _ ->
       tuple (list [msg'; msg''], tuple (stmts, decls)) -?-> 
       (fun (_, (stmts, decls)) -> (iname, args', decls, stmts))
    )  
  in
  let checkProc f (name, args, d, s) =
    resolveArgs args -?->> 
    (fun args -> 
       let iname = env#getInternal name in
      (* env#update name (`Proc (iname, args)) -?->> 
       (fun _ ->*) f (name, args, d, s) -?-> (fun x -> name, x)  (* ) *)
    )
  in
  if restricted 
  then
    let m, pdecls = Common.resolveDecls (checkProc inner) pdecls in
    tuple (m, !! (snd (List.split pdecls))) -?-> snd
  else
    let m, pdecls = Common.resolveDecls (checkProc (!!)) pdecls in
    tuple (m, list (List.map inner (snd (List.split pdecls)))) -?-> snd

(* ------------------------------------- Typechecker -------------------------------- *)

let typecheck decl stmt p =
  list (
    List.map 
      (fun (name, args, decls, stmts) -> 
         tuple (decl decls, list (List.map stmt stmts)) -?-> 
         (fun (decls, stmts) -> name, args, decls, stmts)
      ) 
      p
  )