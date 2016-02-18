open Common
open Ostap.Util
open List

(* ------------------------------------- Monadic transformer ------------------------ *)

module Mapper (M : Monad.S) =
  struct
    open M
    let map ref cexpr expr ext f =
      let mlist l = list (map ext l) in
      let option f = function None -> return None | Some x -> f x >>= (fun x -> return (Some x)) in
      let caseCond c =
        list
          (List.map 
            (function 
             | `Atom e -> cexpr e >>= (fun e -> return (`Atom e))
             | `Interval (x, y) -> list [cexpr x; cexpr y] >>= (fun [x; y] -> return (`Interval (x, y)))
            )
            c
          )
      in
      function
      | `For (i, l, u, s, b) ->
          tuple (ref i, tuple (expr l, tuple (expr u, tuple (option cexpr s, mlist b)))) >>=
          (fun (i, (l, (u, (s, b)))) -> f (`For (i, l, u, s, b)))
      | `Case (e, b, s) ->
          tuple (
            expr e, 
            tuple (
              list 
                (List.map 
                   (fun (c, s) -> tuple (caseCond c, mlist s) >>= (fun (c, s) -> return (c, s))) 
                   b
                ),
              mlist s
            )
          ) >>= (fun (e, (b, s)) -> f (`Case (e, b, s)))
      | x -> ext x
  end

let cmap ref cexpr expr ext f stmt =
  let module M = Mapper (Monad.Checked) in
  M.map ref cexpr expr ext f stmt

let imap ref cexpr expr ext f stmt =
  let module M = Mapper (Monad.Id) in
  M.map ref cexpr expr ext f stmt

(* ----------------------------------------- Parser --------------------------------- *)

ostap (
  parse[ref][cexpr][expr][stmt]: 
    forStatement[ref][expr][cexpr][stmt] 
  | caseStatement[cexpr][expr][stmt];
  forStatement[ref][expr][cexpr][stmt]: 
    key["FOR"] i:ref ":=" lb:expr key["TO"] ub:expr step:(-key["BY"] cexpr)?
       key["DO"] body:oseq[stmt] key["END"] {
    `For (i, lb, ub, step, body)
  };
  caseCondition[cexpr]: 
   list[ostap (
      a:cexpr b:(-".." cexpr)? {
        match b with None -> `Atom a | Some b -> `Interval (a, b)
      }
  )];
  caseStatement[cexpr][expr][stmt]:
    key["CASE"] e:expr key["OF"] 
       branches:listBy[ostap("|")][ostap(caseCondition[cexpr] -":" oseq[stmt])]
       elsePart:(-key["ELSE"] oseq[stmt])?
    key["END"] {
    `Case (e, branches, listify elsePart)
  }
)

(* --------------------------------------Pretty-printer ----------------------------- *)

open Ostap.Pretty

let rec print ref cexpr expr ext stmt =
  let self = print ref cexpr expr ext in
  imap ref cexpr expr 
    (ext self)
    (function 
     | `For (i, l, u, s, stmts) ->
          plock 
            (listBySpace ([string "FOR"; i; string ":="; l; string "TO"; u] @ 
                          match s with None -> [] | Some s -> [string "BY"; s]
                         )
            )
            (sblock "DO" "END" (pseq stmts))
     | `Case (e, b, elsePart) -> 
          let caseCond c =
            hov [
              listByCommaBreak 
                (List.map 
                   (function `Atom c -> c | `Interval (x, y) -> hov [x; string ".."; y]) 
                   c
                );
              string ":"
            ]
          in
          block 
            (listBySpace[string "CASE"; e; string "OF"]) 
            (string "END") 
            (vert [
               listBy 
                 (seq[string " |"; break]) 
                 (List.map (fun (c, s) -> plock (caseCond c) (pseq s)) b);
               match elsePart with [] -> empty | s -> plock (string "ELSE ") (pseq s)
             ]
            )
    )
    stmt

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let rec resolve ref cexpr expr ext stmt = 
  cmap ref cexpr expr (ext (resolve ref cexpr expr ext)) (!!) stmt

(* --------------------------------------- Typechecker ------------------------------ *)

open Ostap

let rec typecheck ts ref cexpr expr ext stmt = 
  let self = typecheck ts ref cexpr expr ext in
  cmap ref cexpr expr 
    (ext self)
    (function
     | `For ((i, it), (l, lt), (u, ut), s, _) as z ->
         tuple (
           ?| [Common.int ts i it `Int; Common.int ts l lt `Int; Common.int ts u ut `Int], 
           match s with None -> !! () | Some (s, st) -> Common.int ts s st `Int -?-> (fun _ -> ())
         ) -?-> 
         (fun _ -> z)
     | `Case ((e, et), b, _) as z -> 
         tuple (
           list
             (List.map 
               (fun (c, s) -> 
                  list 
                    (List.map 
                      (function 
                       | `Atom (c, t) -> Common.int ts c t `Int -?-> ignore
                       | `Interval ((x, tx), (y, ty)) ->  
                           tuple (Common.int ts x tx `Int, Common.int ts y ty `Int) -?-> ignore                           
                      )
                      c
                    ) -?-> (fun c -> c, s)
               )
               b
             ),
           Common.int ts e et `Int
         ) -?-> (fun _ -> z)
    ) 
    stmt
