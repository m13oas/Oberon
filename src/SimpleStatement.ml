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
    let rec gmap t ref expr ext stmt =
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
               method whilec stmt c (b: 'a list) = f stmt (`While  (c, b))
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

class['stmt, 'ref, 'expr, 'envs, 'rs, 'envr, 'rr, 'enve, 're, 'env, 'r] resolve = object
  inherit ['stmt, 'envs, ('r, Ostap.Msg.t) Checked.t, 
           'ref,  'envr, ('rr, Ostap.Msg.t) Checked.t, 
           'expr, 'enve, ('re, Ostap.Msg.t) Checked.t, 
                  'env, ('r, Ostap.Msg.t) Checked.t] @stmt
  (*Остальные элементы также переходят сами в себя. Но непонятно как их указывать, тк l1_ref и l1_expr в L1*)
  constraint 'r = ('stmt, ('rr, Ostap.Msg.t) Checked.t,  ('re, Ostap.Msg.t) Checked.t) stmt
  method c_Assign inh aug ref expr = 
    tuple (ref.GT.fx inh, expr.GT.fx inh) -?->> 
      (fun (x, y) -> !!(reloc (locate (aug.GT.x)) (`Assign x y)))
  method c_If inh aug ifprt thprt =
    tuple (
      list 
      ((GT.gmap(GT.list) (fun (e, s) -> tuple (aug.GT.t#expr inh e, list (GT.gmap(GT.list) (aug.GT.f inh) s) ) -?-> (fun (e, s) -> e, s)))ifprt),  
      list 
      (GT.gmap(GT.list) (aug.GT.f inh) thprt)) 
    -?->> 
      (fun (x, y) -> !! (reloc (locate aug.GT.x) (`If (x, y))))
  method c_While inh aug expr stmt = 
    tuple ((expr.GT.fx inh), list ((GT.gmap(GT.list) (aug.GT.f inh ) stmt))) -?->> 
      (fun (x, y) -> !! (reloc (locate aug.GT.x) (`While x y)) )
end

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

class['stmt, 'ref, 'expr, 'envs, 'ts, 'envr, 'tr, 'enve, 'te, 'env, 't] typecheck = object
  inherit ['stmt, 'envs, ('ts, Ostap.Msg.t) Checked.t, 
           'ref, 'envr, ('tr, Ostap.Msg.t) Checked.t, 
           'expr, 'enve, ('te, Ostap.Msg.t) Checked.t, 
                  'env, ('t, Ostap.Msg.t) Checked.t] @stmt
  (*constraint 'tr = ('ref l1_ref * [> `Bool | `Int ])*)
  constraint 'te = ('f expr * [> `Int | `Bool | `User of 'a * 'b * 'c] as 'f)
  constraint 't  = ('stmt, ('c * [> `Int | `Bool]), ('c * [> `Int | `Bool])) stmt
  method c_Assign inh aug ref expr = 
    tuple (ref.GT.fx inh, expr.GT.fx inh) -?->> 
      (fun (((_, dt) as d), ((y, st) as s)) -> 
	if inh#primitive dt && inh#primitive st
        then Common.same inh dt st y -?-> (fun _ -> `Assign (d, s))
        else Fail [Ostap.Msg.make "assignment is allowed only for primitive types" [||] (locate y)])
  method c_If inh aug ifprt thprt = 
    tuple (
      list 
	(
	  (GT.gmap(GT.list) (fun (e, s) -> tuple ((aug.GT.t#expr inh e, list (GT.gmap(GT.list) (aug.GT.f inh) s) ) )
	   -?-> (fun (e, s) -> e, s)))
	    ifprt),  
      list (GT.gmap(GT.list) (aug.GT.f inh) thprt)) -?->> 
      (fun (b, e) -> ?| (List.map (fun ((y, t), _) -> Common.bool inh y t `Bool) b) -?-> (fun _ -> `If (b, e)) )
  method c_While inh aug expr stmt = 
    tuple ((expr.GT.fx inh), list ((GT.gmap(GT.list) (aug.GT.f inh ) stmt))) -?->> 
      (fun (((y, ct) as c), b) -> Common.bool inh y ct `Bool -?-> (fun _ -> `While (c, b))  )
end
