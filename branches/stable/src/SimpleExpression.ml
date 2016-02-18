open Common
open Ostap.Pretty
open Ostap.Util
open List

(* ------------------------------------ Monadic transformer ------------------------- *)

module Mapper (M : Monad.S) =
  struct
    open M
    let map ext f z =
      let reloc = reloc (locate z) in
      match z with
      | `Not x -> ext x >>= (fun x -> f (reloc (`Not x)))
      | `Neg x -> ext x >>= (fun x -> f (reloc (`Neg x)))
      | `Binop (op, x, y) -> 
           list (map ext [x; y]) >>= (fun [x; y] -> f (reloc (`Binop (op, x, y))))
      | (`Const _ | `True | `False) as x -> f x
      | x -> ext x
  end

let cmap ext f expr =
  let module M = Mapper (Monad.Checked) in
  M.map ext f expr

let imap ext f expr =
  let module M = Mapper (Monad.Id) in
  M.map ext f expr

(* ----------------------------------------- Parser --------------------------------- *)

let r = Ostap.Matcher.Token.repr
let l = Ostap.Matcher.Token.loc 

let rec parse reference s = 
  let binop t x y = `Binop (t, x, y) in
  expr loc [|
   `Nona , List.map (fun (s, t) -> ostap($(s)), binop t) 
           ["=", `Eq; "#", `Ne; "<=", `Le; "<", `Lt; ">=", `Ge; ">", `Gt];
   `Lefta, List.map (fun (s, t) -> s, binop t)
           [ostap ("+"), `Add; ostap ("-"), `Sub; key "OR", `Or];
   `Lefta, List.map (fun (s, t) -> s, binop t)
           [ostap ("*"), `Mul; key "DIV", `Div; key "MOD", `Mod; ostap ("&"), `And]
  |]
  (primary reference)
  s
and ostap (
  primary[reference]: 
   loc[ostap(
         x:LITERAL =>{try ignore (int_of_string (r x)); true with _ -> false}::
                     (new Ostap.Reason.t 
                        (Ostap.Msg.make "integer constant \"%0\" is too large" [|r x|] (l x))
                     )=> {`Const (int_of_string (r x))} 
       | @("TRUE\\b" :"TRUE" ) {`True}
       | @("FALSE\\b":"FALSE") {`False}
       | -"(" x:parse[reference] -")"
       | "~" x:primary[reference] {`Not x}
       | "-" x:primary[reference] {`Neg x}
       | -"+" primary[reference]
       | reference)
      ]
)

(* ------------------------------------ Pretty-printer ------------------------------ *)

let rec gprint ps ext expr =  
  let self = gprint ps ext in
  imap 
    (ext self)
    (fun expr -> 
       let b  x = hovboxed (listBySpaceBreak x) in
       let op (s, p) = string s, p in
       let w p' (x, p) = if p' < p then rboxed x else x in 
       match expr with
       | `Not      x           -> let s, p = op (ps#not ())  in b [s; w p x]       , p
       | `Neg      x           -> let s, p = op (ps#neg ())  in b [s; w p x]       , p
       | `Binop   (o, x, y)    -> let s, p = op (ps#binop o) in b [w p x; s; w p y], p
       | `Const    x           -> int x, 0
       | (`True | `False) as o -> op (ps#bool o)
    )
    expr
   
let print ext expr = gprint 
  (object
     method not () = "~", 0
     method neg () = "-", 0
     method binop  = function 
     | `Mul -> "*" , 1 | `Div  -> "DIV" , 1 | `Mod   -> "MOD"  , 1 | `And -> "&", 1
     | `Add -> "+" , 2 | `Sub  -> "-"   , 2 | `Or    -> "OR"   , 2 
     | `Le  -> "<=", 3 | `Lt   -> "<"   , 3 | `Ge    -> ">="   , 3 | `Gt  -> ">", 3 
     | `Ne  -> "#" , 3 | `Eq   -> "="   , 3 
     method bool = function `True -> "TRUE", 0 | `False -> "FALSE", 0
   end) ext expr

let print_c ext expr = gprint
  (object
     method not () = "!", 0
     method neg () = "-", 0
     method binop  = function
     | `Mul -> "*" , 1 | `Div  -> "/" , 1 | `Mod   -> "%" , 1 | `And -> "&&", 1
     | `Add -> "+" , 2 | `Sub  -> "-" , 2 | `Or    -> "||", 2 
     | `Le  -> "<=", 3 | `Lt   -> "<" , 3 | `Ge    -> ">=", 3 | `Gt  -> ">" , 3 
     | `Ne  -> "!=", 3 | `Eq   -> "==", 3
     method bool = function `True -> "1", 0 | `False -> "0", 0
   end) ext expr

(* ------------------------------------- Name resolver ------------------------------ *)

open Checked 

let rec resolve ext e = cmap (ext (resolve ext)) (!!) e

(* -------------------------------------- Typechecker ------------------------------- *)

let typeOf ref = function
| `Const _ -> `Int
| `True | `False | `Not _ -> `Bool
| `Neg _ -> `Int
| `Binop (op, _, _) ->
    (match op with `Add | `Sub | `Mul | `Mod | `Div -> `Int | _ -> `Bool)
| x -> ref x

let rec typecheck ts ext expr =
  let self = typecheck ts ext in
  cmap 
    (ext self)
    (function
     | `Neg (x, t) as z -> Common.int  ts z t `Int
     | `Not (x, t) as z -> Common.bool ts z t `Bool
     | `Binop (op, x, y) as z -> 
         let t', ensureType =
           match op with          
           | `And | `Or -> `Bool, fun (x, t) -> Common.bool ts x t `Bool  
           | `Eq  | `Ne  | `Le  | `Lt  | `Ge  | `Gt -> `Bool, fun (x, t) -> Common.int ts x t `Int
           | _ -> `Int, fun (x, t) -> Common.int ts x t `Int
        in
        tuple (ensureType x, ensureType y) -?-> (fun _ -> z, t')
     | `Const _         as z -> !! (z, `Int)
     | (`True | `False) as z -> !! (z, `Bool)
    ) 
    expr

(* --------------------------------------- Evaluator -------------------------------- *)

exception Not_a_constant

let evaluate expr = 
  let rec inner expr =
    imap
      (function 
         (`Neg _ | `Not _ | `Binop _ | `Const _ | `True | `False) as x -> inner x 
       | _ -> raise Not_a_constant 
      )
      (function 
       | `Neg x -> -x
       | `Not x -> if x > 0 then 0 else 1
       | `Binop (op, x, y) -> 
           let l f x y = if f x y then 1 else 0 in
           let i f x y = if f (x > 0) (y > 0) then 1 else 0 in
           (match op with
            | `Add -> (+)    | `Sub -> (-)    | `Mul -> ( * )  
            | `Div -> (/)    | `Mod -> (mod) 
            | `Eq  -> l (=)  | `Ne  -> l (<>) 
            | `Le  -> l (<=) | `Lt  -> l (<) 
            | `Ge  -> l (>=) | `Gt  -> l (>)
            | `And -> i (&&) | `Or  -> i (||)
           ) x y 
       | `Const x -> x
       | `True    -> 1
       | `False   -> 0
      )      
      expr
  in
  let x = inner expr in
  let reloc = reloc (locate expr) in
  match typeOf (fun _ -> raise Not_a_constant) expr with
  | `Int  -> reloc (`Const x)
  | `Bool -> reloc (if x > 0 then `True else `False)
