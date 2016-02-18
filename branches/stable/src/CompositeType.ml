open Common
open Ostap.Util

(* ------------------------------------- Monadic transformer ------------------------ *)

module Mapper (M : Monad.S) =
  struct
    open M
    let map expr ext f typ = 
      let reloc = reloc (locate typ) in 
      match typ with
      | `Array (size, typ) -> 
         tuple (expr size, ext typ) >>= (fun (size, typ) -> f (reloc (`Array (size, typ))))
      | `Record fields -> 
         list (
           (List.map 
             (fun (name, typ) -> ext typ >= (fun typ -> name, typ)) 
             fields
           )
         ) >>=
         (fun fields -> f (reloc (`Record (fields))))
      |  x -> ext x
  end

let cmap expr ext f typ =
  let module M = Mapper (Monad.Checked) in
  M.map expr ext f typ

let imap expr ext f typ =
  let module M = Mapper (Monad.Id) in
  M.map expr ext f typ

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

let rec print expr ext typ =
  let self = print expr ext in
  imap expr 
    (ext self)
    (function 
     | `Array (s, t) -> hov [string "ARRAY"; s; string "OF"; t]
     | `Record f -> 
         sblock "RECORD" "END" 
           (vert [pseq (List.map (fun name, typ -> hov [string name; string ":"; typ]) f)])
    )
    typ

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let rec resolve env expr ext typ =
  let self = resolve env expr ext in
  cmap expr 
    (ext self) 
    (function 
     | `Array (s, x) -> 
        (match s with 
         | `Const x when x < 0 -> 
            Fail [Ostap.Msg.make "negative size %0 in array type declaration" 
                    [|string_of_int x|] 
                    (locate s)
            ]
         | _ -> !! (`Array (s, x))
        )
        
     | `Record x ->
          let module S = Set.Make (String) in
          let _, m = 
            List.fold_left 
              (fun (s, m) (name, _) -> 
                 if S.mem name s 
                 then s, (Ostap.Msg.make "duplicate record field name \"%0\"" [|name|] (locate name)) :: m
                 else S.add name s, m
              ) 
              (S.empty, []) 
              x
          in 
          match m with [] -> !! (`Record x) | _ -> Fail m
    ) 
    typ

