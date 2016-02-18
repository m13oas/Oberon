open Common
open Ostap.Util

(* --------------------------------------- Parser ----------------------------------- *)

ostap (parse[expr]: -key["CONST"] (ident -"=" expr -";") * )

(* ------------------------------------ Pretty-printer ------------------------------ *)

open List
open Ostap.Pretty

let print expr = function  
  | [] -> []
  | t -> 
      [plock (string "CONST")
        (vert      
           (map 
              (fun (name, value) -> hov [string name; string "="; seq [expr value; string ";"]]) 
              t
           )       
        )
      ]
