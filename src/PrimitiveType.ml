open Common

(* ----------------------------------------- Parser --------------------------------- *)

ostap (parse: name:ident {`User name})

(* -------------------------------------- Pretty-printer ---------------------------- *)

let gprint f t = Ostap.Pretty.string (f t)

let print t = gprint (function `Int -> "INTEGER" | `Bool -> "BOOLEAN" | `User name -> name) t
let print_c t = gprint (function `Int | `Bool -> "int" | `User (name, _) -> name) t
  
let ts = 
  object(self)
    method primitive = function
    | `Int | `Bool -> true
    | `User (_, _, x) -> self#primitive x
    | _ -> false    
    method equal x y = 
      match x, y with
      | `User (_, _, x), _ -> self#equal x y
      | _, `User (_, _, y) -> self#equal x y
      | _ -> x = y
    method string = function `Int -> "INTEGER" | `Bool -> "BOOLEAN" | `User (name, _, _) -> name
  end

(* -------------------------------------- Name resolver ----------------------------- *)

open Checked

let resolve env = function
| `Int  -> !! `Int
| `Bool -> !! `Bool
| `User name -> 
     env#lookup name -?->> 
     (function 
      | `Type (iname, x) -> !! (`User (name, iname, x))
      | _ -> Fail [Ostap.Msg.make "identifier \"%0\" does not designate a type"
                     [|name|] (locate name)
             ]
     )
