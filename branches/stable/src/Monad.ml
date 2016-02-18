module type S = 
  sig

    type 'a t

    val return : 'a -> 'a t
    val (>>=)  : 'a t -> ('a -> 'b t) -> 'b t
    val (>=)   : 'a t -> ('a -> 'b) -> 'b t
    val list   : 'a t list -> 'a list t
    val tuple  : ('a t * 'b t) -> ('a * 'b) t 

  end

module Checked = 
  struct

    open Checked

    type 'a t = ('a, Ostap.Msg.t) Checked.t 
  
    let return = (!!)
    let (>>=)  = (-?->>)
    let (>=)   = (-?->)
    let list   = ( ?| )
    let tuple  = tuple

    let scheme = (bind, list, tuple)

  end

module Id =
  struct

    type 'a t = 'a
      
    let return x   = x
    let (>>=)  x f = f x
    let (>=)       = (>>=) 
    let list   x   = x
    let tuple  x   = x

  end
