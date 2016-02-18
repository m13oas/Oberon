open Lazy
open Checked

let make parse print resolve typecheck source =
  let parsed   = lazy_from_fun (fun _ -> Common.check (parse (new Lexer.t source))) in
  let resolved = lazy_from_fun (fun _ -> force parsed -?->> resolve) in  
  let checked  = lazy_from_fun (fun _ -> force parsed -?->> typecheck) in
  object
    method parse     () = force parsed -?-> (fun _ -> ())
    method print     () = force parsed -?-> (fun t -> Ostap.Pretty.toString (print t))
    method resolve   () = force resolved -?-> (fun _ -> ())
    method typecheck () = force checked -?-> (fun _ -> ())
  end