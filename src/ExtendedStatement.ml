open Common
open Ostap.Util
open List
open SimpleStatement

@type ('expr) atom = [ `Atom of 'expr
		     | `Interval of 'expr * 'expr] with gmap, foldl

@type ('stmt, 'atom, 'expr, 'ref) extstmt = [ `Case of 'ref * ('atom GT.list * 'stmt GT.list) GT.list * 'stmt GT.list
					    | `For of 'ref * 'expr * 'expr * 'expr GT.option * 'stmt GT.list] with gmap, foldl

(* ------------------------------------- Generic transformer ------------------------ *)

module Mapper (M : Monad.S) =
  struct
    open M
    let rec gmap t ref cexpr expr ext (stmt) = 
      let self = gmap t ref cexpr expr ext in
      match stmt with
      | `For (i, l, u, s, b) -> 
          tuple (
            (match s with None -> return None | Some x -> cexpr x >= (fun x -> Some x)),
            tuple (
              list [ref i; expr l; expr u],
              list (map self b)
            )
          ) >>= (fun (s, ([i; l; u], b)) -> t#forc stmt i l u s b)
      | `Case (e, b, s) -> 
          let condition c =
            list (
              map 
                (function
                 | `Atom x -> cexpr x >= (fun x -> `Atom x) 
                 | `Interval (x, y) -> tuple (cexpr x, cexpr y) >=
                                       (fun (x, y) -> `Interval (x, y))
                ) 
                c
            )
          in
          tuple (
            expr e, 
            tuple (list (map (fun (c, s) -> tuple (condition c, list (map self s))) b),
                   list (map self s)
            )
          ) >>= (fun (e, (b, s)) -> t#case stmt e b s)
      | x -> ext self x
  end

let imap t ref cexpr expr ext stmt =
  let module M = Mapper (Monad.Id) in
  M.gmap t ref cexpr expr ext stmt

let cmap t ref cexpr expr ext stmt =
  let module M = Mapper (Monad.Checked) in
  M.gmap t ref cexpr expr ext stmt

let mapT f = object
               method forc stmt i l u s b = f stmt (`For  (i, l, u, s, b))
               method case stmt e b s     = f stmt (`Case (e, b, s))
             end

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

class ['expr] print_atom = object
  inherit ['expr, unit, printer, unit, printer] @atom
  method c_Atom     _ aug expr = (aug.GT.t#expr () expr)
  method c_Interval _ aug a b  = hov [(aug.GT.t#expr () a); string ".."; (aug.GT.t#expr () b)]
end

class ['stmt, 'atom, 'expr, 'ref] print testmt = object
  inherit ['stmt, unit, printer, 'atom, unit, printer, 'expr, unit, printer, 'ref, unit, printer, unit, printer] @extstmt
  inherit ['atom] print_atom
(*  inherit ['expr, 'ref] L1.l1_print SimpleExpression.ob_ps*)
  method c_For _ a i l u s b = (*invalid_arg ""*)
    plock 
      (listBySpace ([string "FOR"; (a.GT.t#ref () i); string ":="; (a.GT.t#expr () l); string "TO"; (a.GT.t#expr () u)] @ 
                       match s with None -> [] | Some s -> [string "BY"; (a.GT.t#expr () s)]
       )
      )
      (sblock "DO" "END" (pseq (GT.gmap(GT.list) (a.GT.t#stmt ()) b)))
  
  method c_Case _ a e b elsePart =
    let caseCond c =      
           hov [
             listByCommaBreak 
               (GT.gmap(GT.list) (a.GT.t#atom ()) c);
             string ":"
           ]
         in
    block 
           (listBySpace[string "CASE"; (a.GT.t#ref () e); string "OF"]) 
           (string "END") 
           (vert [
              listBy 
                (seq[string " |"; break]) 
                (map (fun (c, s) -> plock (caseCond c) (pseq (GT.gmap(GT.list) (a.GT.t#stmt ()) s))) b);
              match elsePart with [] -> empty | s -> plock (string "ELSE ") (pseq (GT.gmap(GT.list) (a.GT.t#stmt ()) s))
            ]
           )
end

let ob_ext = object
  method forc _ i l u s b = 
    plock 
      (listBySpace ([string "FOR"; i; string ":="; l; string "TO"; u] @ 
                       match s with None -> [] | Some s -> [string "BY"; s]
       )
      )
      (sblock "DO" "END" (pseq b))
  method case _ e b elsePart =
    let caseCond c =
      hov [
        listByCommaBreak 
          (map 
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
          (map (fun (c, s) -> plock (caseCond c) (pseq s)) b);
        match elsePart with [] -> empty | s -> plock (string "ELSE ") (pseq s)
       ]
      )
end

let print expr ext stmt =
  imap  
    (object
       method forc _ i l u s b = 
         plock 
           (listBySpace ([string "FOR"; i; string ":="; l; string "TO"; u] @ 
                         match s with None -> [] | Some s -> [string "BY"; s]
                        )
           )
           (sblock "DO" "END" (pseq b))
       method case _ e b elsePart =
         let caseCond c =
           hov [
             listByCommaBreak 
               (map 
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
                (map (fun (c, s) -> plock (caseCond c) (pseq s)) b);
              match elsePart with [] -> empty | s -> plock (string "ELSE ") (pseq s)
            ]
           )
     end
    ) expr expr expr ext stmt

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let resolve ref cexpr expr ext stmt =
  let reloc x y = reloc (locate stmt) y in
  cmap (mapT (fun stmt s -> !! (reloc stmt s))) ref cexpr expr ext stmt

(* --------------------------------------- Typechecker ------------------------------ *)

open Ostap

let typecheck ts expr ext stmt =
  cmap (object
          method forc _ ((i, it) as i') ((l, lt) as l') ((u, ut) as u') s b =
            tuple (
              ?| [Common.int ts i it `Int; Common.int ts l lt `Int; Common.int ts u ut `Int], 
              match s with 
              | None -> !! () 
              | Some (s, st) -> Common.int ts s st `Int -?-> (fun _ -> ())
            ) -?-> 
            (fun _ -> `For (i', l', u', s, b))
          method case _ ((e, et) as e') b s =
            tuple (
              list
                (List.map 
                  (fun (c, s) -> 
                     list 
                       (List.map 
                          (function 
                           | `Atom (c, t) -> Common.int ts c t `Int -?-> ignore
                           | `Interval ((x, tx), (y, ty)) ->  
                               tuple (Common.int ts x tx `Int, Common.int ts y ty `Int) -?-> 
                               ignore
                          )
                          c 
                       ) -?-> (fun c -> c, s)
                  )
                  b
                ),
                Common.int ts e et `Int
            ) -?-> (fun _ -> `Case (e', b, s))
        end) expr expr expr ext stmt
