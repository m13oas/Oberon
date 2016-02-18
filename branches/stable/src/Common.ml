open List
open Ostap.Util

let keyword = 
  let module S = Set.Make (String) in
  let s = 
    fold_right
      S.add     
      ["IF"   ; "THEN"; "ELSIF"; "ELSE"  ; "END" ; "MODULE"   ; "VAR"    ; "CONST"  ; "TYPE"; 
       "WHILE"; "DO"  ; "MOD"  ; "DIV"   ; "OR"  ; "PROCEDURE"; "CASE"   ; "OF"     ; "FOR" ; 
       "TO"   ; "BY"  ; "ARRAY"; "RECORD"; "BEGIN"
      ] 
      S.empty 
  in
  fun name -> S.mem (Ostap.Matcher.Token.repr name) s

open Ostap
open Msg

module Trap =
  struct

    module H = Hashtbl.Make (struct type t = unit let hash = Hashtbl.hash let equal = (==) end)

    let (t : Msg.Locator.t H.t) = H.create 1024
    let attach k v = H.add t (Obj.magic k) v
    let locate k   = try H.find t (Obj.magic k) with Not_found -> Msg.Locator.No

  end
 
ostap (
  loc[item]: l:($) x:item r:($) {
    let loc = match l#skip l#pos l#coord with `Skipped (_, loc) -> Msg.Locator.Point loc | _ -> l#loc in 
    Trap.attach x (Msg.Locator.makeInterval loc r#loc); x
  }
)

ostap (
  ident: loc[ostap (id:IDENT =>{not (keyword id)}::
                               (new Reason.t 
                                  (Msg.make "identifier expected" [||] (Matcher.Token.loc id))
                               )=> {Ostap.Matcher.Token.repr id})];
  literal: loc[ostap (lt:LITERAL {Ostap.Matcher.Token.repr lt})];
  seq[item]: listBy[ostap (";")][item];
  key[name]: @(name ^ "\\b" : name);
  expect[name]: key[name]
)

ostap (
  oseq[item]: x:seq[ostap(item?)] {
    List.flatten (List.map (function Some x -> [x] | _ -> []) x)
  }
)

let locate      = Trap.locate 
let reloc loc x = Trap.attach x loc; x

let listify = function None -> [] | Some l -> l

open Ostap.Pretty

let sblock a b c = block    (string a) (string b) c
let mseq   a b   = vboxed   (listBySemicolonBreak (map a b)) 
let pseq   a     = vboxed   (listBySemicolonBreak a) 
let vert   a     = vboxed   (listByBreak a)
let hov    a     = hovboxed (listBySpaceBreak a)  

open Checked

open Checked 

let resolveDecls f t =
  let m, c = List.fold_left 
     (fun (m, c) x -> 
        match f x with
        | Ok (name, value) -> m, (name, value)::c
        | x -> x::m, c
     ) 
     ([], []) 
     t
  in
  list m, List.rev c

let fail s args z  = Fail [Msg.make s args (locate z)] 
let bool ts z t t' = if ts#equal `Bool t then !! (z, t') else fail "boolean expression expected" [||] z 
let int  ts z t t' = if ts#equal `Int  t then !! (z, t') else fail "integer expression expected" [||] z 
let same ts z x y  = if ts#equal z x then !! () else fail "expression of type \"%0\" expected" [|ts#string z|] y
let wrong cat n z  = fail "identifier \"%0\" does not designate a %1" [|n; cat|] z

let apply f x = f x
let id x = x

let check x = 
  Combinators.unwrap x (fun x -> !! x) 
    (fun (Some err) ->
       let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
       let m =  match m with `Msg m -> m | `Comment (s, _) -> Msg.make s [||] loc in
       Fail [m]
    )