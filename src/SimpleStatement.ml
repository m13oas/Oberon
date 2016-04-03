open Common
open Ostap.Util
open List
open SimpleExpression

@type ('stmt, 'ref, 'expr) stmt = [ `Assign of 'ref * 'expr
				   | `If     of (('expr, (('stmt, 'ref, 'expr) stmt) GT.list)GT.pair) GT.list * (('stmt, 'ref, 'expr) stmt) GT.list
				   | `While  of 'expr * (('stmt, 'ref, 'expr) stmt  GT.list)] with gmap, foldl
(* ------------------------------------- Generic transformer ------------------------ *)

module Mapper (M : Monad.S) =
  struct
    open M
    let rec gmap t ref expr ext (stmt) =
      let self = gmap t ref expr ext in
      match stmt with
      | `Assign (x, y) -> tuple (ref x, expr y) >>= (fun (x, y) -> t#assign stmt x y)
      | `If (b, e) -> 
           tuple (list (map (fun (e, s) -> tuple (expr e, list (map self s)) >= (fun (e, s) -> e, s)) b),
                  list (map self e)
           ) >>= (fun (b, e) -> t#ifc stmt b e) (*обход пары двух списков, где первый аргумент - пара из expr и списка stmt*)
      | `While  (c, b) -> tuple (expr c, list (map self b)) >>= (fun (c, b) -> t#whilec stmt c b)
      | x -> ext self x
  end

let imap t ref expr ext stmt =
  let module M = Mapper (Monad.Id) in
  M.gmap t ref expr ext stmt

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
  inherit ['stmt, unit, printer, 'ref, unit, printer, 'expr, unit, printer, unit, printer] @stmt as statementobj
  method c_Assign _ _  ref expr   = tstmt#assign (ref.GT.fx ()) (expr.GT.fx ())
  method c_If     _ _ ifprt elprt = invalid_arg ""
(*    let branch typ (cond, thenPart) = invalid_arg ""
      hov [tstmt#ifHead typ (cond.GT.fx ()); tstmt#thenPart (tstmt#seq thenPart)] in
      match ifprt with
      | [head] -> hov ([branch `If head] @ (tstmt#elsePart (elprt.GT.fx ())))
      | _ -> hov ["a"]
      | head::branches -> 
	vert ([branch `If head] @ 
		 (map (branch `Elsif) branches) @ 
		 (tstmt#elsePart (elprt.GT.fx () ) )
	     )*)
  method c_While _ syn expr stmt = invalid_arg ""
(*    let mapstmt (stm: (('stmt, 'ref, 'expr) stmt) GT.list) = 
      List.map (fun x -> 
      match x with
      | `Assign (ref, expr) ->self#c_Assign () syn.GT.x (ref.GT.x) (expr.GT.x)
      | `If (a, b) -> invalid_arg ""
      | `While _ -> invalid_arg "") stm (*invalid_arg "good type"*) in
(* List.map (fun y -> y.GT.f y.GT.tp#) stm*)
    plock (tstmt#whileHead (expr.GT.fx ())) (tstmt#whileBody (tstmt#seq (mapstmt stmt))) *)
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

let gprint ps(*трансформатор*) expr(*выражение, которое в состоянии?*) ext stmt =
  imap 
    (object 
       method assign _ x y = ps#assign x y
       method ifc _ b e =
         let branch typ (cond, thenPart) = 
           hov(*что-то вроде упаковки в коробку*) [ps#ifHead typ cond; ps#thenPart (ps#seq thenPart)]
         in
         match b with 
         | [head] -> hov ([branch `If head] @ (ps#elsePart e))
         | head::branches -> 
             vert ([branch `If head] @ 

                   (map (branch `Elsif) branches) @ 
                   (ps#elsePart e)
             )
       method whilec _ c b = plock (ps#whileHead c) (ps#whileBody (ps#seq b))
     end
    ) expr expr ext stmt

let print expr ext stmt = 
  gprint (object(self)
            method seq       x   = pseq x (*видимо, генерит какую-то последовательность, но почему то без разделителей и прочего*)
            method assign    d s = hov [d; string ":="; s] (*тут изи, просто упаковываем вкоробку, d  - expr, s - stmt*)
            method whileHead c   = listBySpace [string "WHILE"; c](*принт элементов, разделенных проблелом, с - expr*)
            method whileBody s   = sblock "DO" "END" s(*не нашел, но подозреваю, что принт s между "DO" и "While", s - stmt*)
            method thenPart  s   = hov [string "THEN"; s](*упаковка в коробку и принт, s - stmt*)
            method ifHead    t c = hov [string (match t with `If -> "IF" | `Elsif -> "ELSIF"); c](*упаковка в коробку строки IF и с, c - принт expr*)
            method elsePart = function
            | []    -> [string "END"] 
            | stmts -> [hov [string "ELSE"; self#seq stmts]; string "END"] (*если есть else, то упаковываем в список коробку строку "ELSE", последовательность выражений и строку "END"; иначе просто список со строкой "END"*)
          end) expr ext stmt

let print_c expr ext stmt = 
  gprint (object(self)
            method seq       x   = seq [pseq x; string ";"]
            method assign    d s = hov [d; string "="; s]
            method whileHead c   = listBySpace [string "while"; rboxed c]
            method whileBody s   = sblock "{" "}" s
            method thenPart  s   = sblock "{" "}" s
            method ifHead    t c = hov [string (match t with `If -> "if" | `Elsif -> "else if"); rboxed c]
            method elsePart = function
            | []    -> [] 
            | stmts -> [hov [string "else"; sblock "{" "}" (self#seq stmts)]]
          end) expr ext stmt

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
