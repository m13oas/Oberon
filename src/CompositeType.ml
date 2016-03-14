open Common
open Ostap.Util
open List

(* ------------------------------------ Generic transformer ------------------------- *)

module Mapper (M : Monad.S) =
  struct
    open M
    let rec gmap t expr ext (typ: [> `Array of
                                         ([> `Binop of
					     [< `Add
					     | `And
					     | `Div
					     | `Eq
					     | `Ge
					     | `Gt
					     | `Le
					     | `Lt
					     | `Mod
					     | `Mul
					     | `Ne
					     | `Or
					     | `Sub ] *
					       'b * 'b
					  | `Const of [ `False | `Literal of int | `True ]
					  | `Field of 'b * string
					  | `Index of 'b * 'b
					  | `Unop of [ `Neg | `Not ] * 'b ]
					     as 'b) * 'a
				  | `Bool
				  | `Int
				  | `Record of (string * 'a) list
				(*L5? | `User of 'f * string * 'g*) ] as 'a) = 
      let self = gmap t expr ext in
      match typ with
      | `Array (s, typ) -> tuple (expr s, self typ) >>= (fun (s, typ') -> t#array typ s typ')
      | `Record f -> 
          list (map (fun (n, t) -> self t >= (fun t -> n, t)) f) >>= (fun f -> t#record typ f)
      |  x -> ext self x 
  end

let imap t expr ext typ =
  let module M = Mapper (Monad.Id) in
  M.gmap t expr ext typ

let cmap t expr ext typ =
  let module M = Mapper (Monad.Checked) in
  M.gmap t expr ext typ 

(* ------------------------------------------ Parser -------------------------------- *)

ostap (
  parse[expr][typ]: 
    arrayType[expr][typ] 
  | recordType[expr][typ] 
  | typ; 
  arrayType[expr][typ]: key["ARRAY"] size:expr key["OF"] typ:parse[expr][typ] {
    `Array (size, typ)
  };
  recordType[expr][typ]: key["RECORD"] fields:oseq[ostap (fieldList[parse expr typ])]? key["END"] {
    `Record (
       List.flatten 
         (List.map (fun (names, typ) -> 
            List.map (fun name -> name, typ) names) (listify fields)
         )
     )
  };
  fieldList[typ]: list[ident] -":" typ
)

(* -------------------------------------- Pretty-printer ---------------------------- *)

open Ostap.Pretty

let print expr ext typ =
  imap (object
          method array _ s t = hov [string "ARRAY"; s; string "OF"; t]
          method record _ r = 
            sblock "RECORD" "END" 
              (vert [pseq (List.map (fun (name, typ) -> hov [string name; string ":"; typ]) r)])
        end) expr ext typ

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let resolve env expr ext typ =
  let reloc x y = reloc (locate x) y in
  cmap (object
          method array typ s t =
            match s with 
            | `Const (`Literal x) when x < 0 -> 
                Fail [Ostap.Msg.make "negative size %0 in array type declaration" 
                        [|string_of_int x|] 
                        (locate s)
                ]
            | _ -> !! (reloc typ (`Array (s, t)))
          method record typ f =
            let module S = Set.Make (String) in
            let _, m = 
              fold_left 
                (fun (s, m) (name, _) -> 
                   if S.mem name s 
                   then s, (Ostap.Msg.make "duplicate record field name \"%0\"" [|name|] (locate name)) :: m
                   else S.add name s, m
                ) 
                (S.empty, []) 
                f
            in 
            match m with [] -> !! (reloc typ (`Record f)) | _ -> Fail m
        end) expr ext typ
