open Common
open Ostap.Util
open List

(* ------------------------------------- Monadic transformer ------------------------ *)

module Mapper (M : Monad.S) =
  struct
    open M
    let map ref cexpr expr ext f =
      let mlist l = list (map ext l) in
      function
      | `Assign (x, y) -> tuple (ref x, expr y) >>= (fun (x, y) -> f (`Assign (x, y)))
      | `If (b, e) -> 
          tuple (list (map (fun (e, s) -> tuple (expr e, mlist s)) b), mlist e) >>= 
          (fun (b, e) -> f (`If (b, e)))
      | `While (c, b) -> tuple (expr c, mlist b) >>= (fun (c, b) -> f (`While (c, b))) 
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
    assignment[ref][expr] 
  | ifStatement[expr][stmt] 
  | whileStatement[expr][stmt];
  assignment[ref][expr]: dst:ref ":=" src:expr {`Assign (dst, src)};
  ifStatement[expr][stmt]: 
    key["IF"] cond:expr 
       key["THEN"] thenPart:oseq[stmt]
       branches:(-key["ELSIF"] expr -key["THEN"] oseq[stmt])*
       elsePart:(-key["ELSE"] oseq[stmt])?
    key["END"] {
    `If ((cond, thenPart)::branches, listify elsePart)
  };
  whileStatement[expr][stmt]: 
    key["WHILE"] cond:expr key["DO"] stmts:oseq[stmt] key["END"] {
    `While (cond, stmts)
  }
)

(* --------------------------------------Pretty-printer ----------------------------- *)

open Ostap.Pretty

let rec gprint ps ref cexpr expr ext stmt =
  let self = gprint ps ref cexpr expr ext in
  let branch typ (cond, thenPart) = 
    hov [ps#ifHead typ cond; ps#thenPart (ps#seq thenPart)]
  in
  imap ref cexpr expr 
    (ext self)
    (function 
     | `Assign (dst, src) -> ps#assign dst src 
     | `If ([head], elsePart) -> 
          hov ([branch `If head] @ (ps#elsePart elsePart))
     | `If (head :: branches, elsePart) -> 
          vert ([branch `If head] @ (map (branch `Elsif) branches) @ (ps#elsePart elsePart)) 
     | `While (cond, stmts) -> 
          plock (ps#whileHead cond) (ps#whileBody (ps#seq stmts))
    )
    stmt

let print ref cexpr expr ext stmt = 
  gprint 
    (object(self)
       method seq       x   = pseq x 
       method assign    d s = hov [d; string ":="; s]
       method whileHead c   = listBySpace [string "WHILE"; c]
       method whileBody s   = sblock "DO" "END" s
       method thenPart  s   = hov [string "THEN"; s]
       method ifHead    t c = hov [string (match t with `If -> "IF" | `Elsif -> "ELSIF"); c]
       method elsePart = function
       | []    -> [string "END"] 
       | stmts -> [hov [string "ELSE"; self#seq stmts]; string "END"]
     end
    ) 
    ref cexpr expr ext stmt

let print_c ref cexpr expr ext stmt = 
  gprint 
    (object(self)
       method seq       x   = seq [pseq x; string ";"]
       method assign    d s = hov [d; string "="; s]
       method whileHead c   = listBySpace [string "while"; rboxed c]
       method whileBody s   = sblock "{" "}" s
       method thenPart  s   = sblock "{" "}" s
       method ifHead    t c = hov [string (match t with `If -> "if" | `Elsif -> "else if"); rboxed c]
       method elsePart = function
       | []    -> [] 
       | stmts -> [hov [string "else"; sblock "{" "}" (self#seq stmts)]]
     end
    ) 
    ref cexpr expr ext stmt

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
     | `Assign ((_, dt), (y, st)) as z -> 
        if ts#primitive dt && ts#primitive st
        then Common.same ts dt st y -?-> (fun _ -> z)
        else Fail [Msg.make "assignment is allowed only for primitive types" [||] (locate y)]

     | `While ((y, ct), _) as z -> Common.bool ts y ct `Bool -?-> (fun _ -> z)  
     | `If (b, e) as z -> 
         ?| (List.map (fun ((y, t), _) -> Common.bool ts y t `Bool) b) -?-> (fun _ -> z)
    ) 
    stmt
