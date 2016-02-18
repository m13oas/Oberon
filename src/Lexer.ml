open Ostap
open String
open Printf
open Str
open Ostap.Matcher

let identRegexp = "[a-zA-Z]\([a-zA-Z0-9]\)*\\b" 

class t s = 
  let skip    = Skip.create [Skip.whitespaces " \n\t\r"; Skip.nestedComment "(*" "*)"] in
  let ident   = regexp identRegexp in 
  let literal = regexp "[0-9]+" in
  object (self)
    inherit Matcher.t s 
    method skip p coord = skip s p coord
    method getIDENT     = self#get "identifier" ident
    method getLITERAL   = self#get "literal"    literal         
  end
  