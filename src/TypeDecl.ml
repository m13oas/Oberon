open Common
open Ostap.Util

(* ----------------------------------------- Parser --------------------------------- *)

ostap (parse[typ]: -key["TYPE"] (ident -"=" typ -";") * )

(* --------------------------------------- Pretty-printer --------------------------- *)

open List
open Ostap.Pretty

let print typ = function
| [] -> []
| t ->  [plock (string "TYPE")
          (vert
            (map (fun (name, t) -> seq [hov [string name; string "="; typ t]; string ";"]) 
              t
            )
          )
        ]

let print_c typ = function
| [] -> []
| t ->  [vert
          (map (fun (name, t) -> seq [hov [string "typedef"; typ (string (name ^ "_id")) t]; string ";"])
            t
          )          
        ]
