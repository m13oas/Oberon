open Printf
open Ostap.Util
open Settings
open List
open Lazy

let _ =
  let extension = ".ob" in
  let options = 
    customize (empty ()) [
      "l", "level"  , Number, Mandatory, "\t --- specify language level (2-4).";
      "p", "print"  , Switch, Mandatory, "\t --- pretty-print file.";
      "r", "resolve", Switch, Mandatory, "\t --- perform name binding.";
      "t", "type"   , Switch, Mandatory, "\t --- perform type-check.";
      "c", "cgen"   , Switch, Mandatory, "\t --- generate C.";
      "f", "format" , Switch, Mandatory, "\t --- output messages in a formatted form.";
      "h", "help"   , Switch, Mandatory, "\t --- show help on options."
    ]
    (fun _ -> [])
  in
  let languages = [|L1.top; L2.top(*; L3.top; L4.top; L5.top*)|] in
  let _ :: args = Array.to_list Sys.argv in  
  let perFile l conf file =
    let source, errors, pp, c, lifted = 
      if Filename.check_suffix file extension
      then 
        let basename = Filename.chop_suffix file extension in 
        file, basename ^ ".errors", basename ^ "_pp" ^ extension, basename ^ ".c", basename ^ "_lifted" ^ extension
      else 
        file ^ extension, file ^ ".errors", file ^ "_pp" ^ extension, file ^ ".c", file ^ "_lifted" ^ extension
    in
    let errors = lazy_from_fun (fun _ -> open_out errors) in
    let verify f =
      match conf.get "f" with
      | Some Flag ->
         (function
         | Checked.Ok x -> f x
         | Checked.Fail m ->
            let lineno :: _ =
              List.sort compare
                (List.map (fun m -> 
                  match Ostap.Msg.loc m with
                  | Ostap.Msg.Locator.Point x | Ostap.Msg.Locator.Interval (_, x) -> fst x
                  )
                  m
                )
            in         
            Printf.printf "line %d\n" lineno
         )
      | None -> 
         (function
         | Checked.Ok x   -> f x
         | Checked.Fail m -> 
             iter 
              (fun m -> 
                 let s = Ostap.Msg.toString m in
                 fprintf (force errors) "%s\n" s;
                 eprintf "%s\n" s
              ) 
              m
         )
    in
    let output f s =
      let ouch = open_out f in
      fprintf ouch "%s" s;
      close_out ouch
    in
    let output2 (f1, f2) (s1, s2) =
      output f1 s1;
      output f2 s2
    in
    let skip _ = () in                                               
    let l = l (read source) in
    (match conf.get "p" with Some Flag -> verify (output pp) (l#print ()) | _ -> ());
    (match conf.get "r" with Some Flag -> verify skip (l#resolve ()) | _ -> ());
    (match conf.get "t" with Some Flag -> verify skip (l#typecheck ()) | _ -> ());
(*    (match conf.get "c" with
     | Some Flag -> 
        verify (fun _ -> verify (output2 (lifted, c)) (l#generate ())) (l#typecheck ())
     | _ -> ()
    );
*)
    if lazy_is_val errors then close_out (force errors)
  in
  match options args with
  | Ok (conf, files) -> 
      (match conf.get "l" with
       | None -> 
          (match conf.get "h" with
           | None -> eprintf "Error: language level not specified.\n"
           | Some _ -> printf "%s\n" (conf.help ())
          )
       | Some (Int n) ->
          if n < 1 || n > Array.length languages
          then eprintf "Error: invalid language level %d.\n" n
          else iter (perFile languages.(n-1) conf) files
      )
  | Warnings (conf, _, warnings) ->
      eprintf "Error parsing command-line arguments:\n";
      iter (fun s -> eprintf "   %s\n" s) warnings
    
