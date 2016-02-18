open Printf
open Ostap.Util
open Common

(* ----------------------------------------- Parser --------------------------------- *)

ostap (
  parse[declarations][statement]:
    key["MODULE"] name: ident ";" 
      decls: declarations 
      body : (-key["BEGIN"] oseq[statement])?
    moduleEnd[name] {name, decls, listify body}
  ;
  moduleEnd[expectedName]: -key["END"] -expect[expectedName] -"."
)

(* -------------------------------------- Pretty-printer ---------------------------- *)

open List
open Ostap.Pretty 
open Common

let print d s (name, decls, stmts) = 
  sblock (sprintf "MODULE %s;" name) (sprintf "END %s." name)
    (vert [
       d decls; 
       match stmts with [] -> empty | _ -> plock (string "BEGIN") (mseq s stmts)
     ]
    )    

let print_c d s (name, decls, stmts) = 
  vert [
    d decls; 
    plock (string "int main (char *argv[], int argc)") 
      (sblock "{" "}" (Ostap.Pretty.seq [mseq s stmts; string ";"]))
  ]   

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let resolve env decl stmt (name, decls, stmts) =
  let msg, decls = decl env decls in
  tuple (msg, tuple (decls, list (List.map stmt stmts))) -?-> 
  (fun (_, (decls, stmts)) -> name, decls, stmts) 

(* -------------------------------------- Typechecker ------------------------------- *)

let typecheck decl stmt (name, decls, stmts) =
  tuple (decl decls, list (List.map stmt stmts)) -?-> 
  (fun (decls, stmts) -> (name, decls, stmts))

