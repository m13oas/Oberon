open Common
open Ostap.Util

(* ----------------------------------------- Parser --------------------------------- *)

ostap (
  parse[typ]: -key["VAR"] (list[ostap (ident)] -":" typ -";")*
)

(* -------------------------------------- Pretty-printer ---------------------------- *)

open List
open Ostap.Pretty

let print typ = function
| [] -> []
| t ->
    [plock (string "VAR")
      (vert 
         (map 
           (fun (names, t) -> 
              hov [hovboxed (listByCommaBreak (map string names));
                   string ":";
                   seq [typ t; string ";"]
              ]
           ) 
           t
        )       
      )
    ]

let print_c typ = function
| [] -> []
| t ->
  [vert 
    (map 
      (fun (names, t) -> 
         hov (List.map (fun name -> seq [typ (string (name ^ "_id")) t; string ";"]) names)
      ) 
      t
    )       
  ]
