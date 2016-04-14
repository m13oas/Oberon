open Common
open Ostap.Util
open List
open SimpleExpression

@type ('stmt, 'ref, 'expr) stmt = [ `Assign of 'ref * 'expr
				  | `If     of ('expr, 'stmt GT.list) GT.pair GT.list * 
                                               'stmt GT.list
				  | `While  of 'expr * 'stmt  GT.list] with gmap, foldl

(* ------------------------------------- Generic transformer ------------------------ *)

module Mapper (M : Monad.S) =
  struct
    open M
    let rec gmap t ref expr ext (stmt) =
      let self = gmap t ref expr ext in
      match stmt with
      | `Assign (x, y) -> tuple (ref x, expr y) >>= (fun (x, y) -> t#assign stmt x y)
      | `If (b, e) -> 
           tuple (list 
		    (map (fun (e, s) -> tuple (expr e, list (map self s)) >= (fun (e, s) -> e, s))
		       b),
                  list (map self e)
           ) >>= (fun (b, e) -> t#ifc stmt b e) (*обход пары двух списков, где первый аргумент - пара из expr и списка stmt*)
      | `While  (c, b) -> tuple (expr c, list (map self b)) >>= (fun (c, b) -> t#whilec stmt c b)
      | x -> ext self x
  end

let cmap t ref expr ext stmt =
  let module M = Mapper (Monad.Checked) in
  M.gmap t ref expr ext stmt

let mapT f = object
               method assign stmt x y = f stmt (`Assign (x, y))
               method ifc    stmt b e = f stmt (`If     (b, e))
               method whilec stmt c b = f stmt (`While  (c, b))
             end

(* ----------------------------------------- Parser --------------------------------- *)

ostap (
  parse[ref][expr][stmt]: 
    assignment[ref][expr] 
  | ifStatement[expr][stmt] 
  | whileStatement[expr][stmt];
  assignment[ref][expr]: 
    dst:ref ":=" src:expr {
      `Assign (dst, src)
  };
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

class ['stmt, 'ref, 'expr] print tstmt = object(self)
  inherit ['stmt, unit, printer, 'ref, unit, printer, 'expr, unit, printer, unit, printer] @stmt
  method c_Assign _ _  ref expr   = tstmt#assign (ref.GT.fx ()) (expr.GT.fx ())
  method c_If     _ a ifprt elprt =
    let b, e = (List.map (fun (x, y) -> ((a.GT.t#expr () x), (GT.gmap(GT.list) (a.GT.f ()) y))) ifprt),(GT.gmap(GT.list) (a.GT.f ()) elprt) in
    let branch typ (cond, thenPart) = hov [tstmt#ifHead typ cond; tstmt#thenPart (tstmt#seq thenPart)] in
    match b with 
    | [head] -> hov ([branch `If head] @ (tstmt#elsePart e))
    | head::branches -> 
      vert ([branch `If head] @ 
               (map (branch `Elsif) branches) @ 
               (tstmt#elsePart e)
      )
  method c_While _ a expr stmt = plock (tstmt#whileHead (expr.GT.fx ())) (tstmt#whileBody (tstmt#seq (List.map (fun x -> a.GT.f () x) stmt)))
end 

let ob_ps = object(self)
  method seq       x   = pseq x
  method assign    d s = hov [d; string ":="; s]
  method whileHead c   = listBySpace [string "WHILE"; c]
  method whileBody s   = sblock "DO" "END" s(*принтер*)
  method thenPart  s   = hov [string "THEN"; s]
  method ifHead    t c = hov [string (match t with `If -> "IF" | `Elsif -> "ELSIF"); c]
  method elsePart = function
  | []    -> [string "END"] 
  | stmts -> [hov [string "ELSE"; self#seq stmts]; string "END"]
end

let ob_ps_c = object(self)
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

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let resolve ref expr ext stmt =
  let reloc x y = reloc (locate x) y in
  cmap (mapT (fun stmt s -> !!(reloc stmt s))) ref expr ext stmt

(* --------------------------------------- Typechecker ------------------------------ *)

let typecheck ts expr ext stmt =
  cmap (object
          method assign _ ((_, dt) as d) ((y, st) as s) = 
            if ts#primitive dt && ts#primitive st
            then Common.same ts dt st y -?-> (fun _ -> `Assign (d, s))
            else Fail [Ostap.Msg.make "assignment is allowed only for primitive types" [||] (locate y)]
          method ifc _ b e = 
            ?| (List.map (fun ((y, t), _) -> Common.bool ts y t `Bool) b) -?-> (fun _ -> `If (b, e))
          method whilec _ ((y, ct) as c) b =
            Common.bool ts y ct `Bool -?-> (fun _ -> `While (c, b))  
        end) expr expr ext stmt
