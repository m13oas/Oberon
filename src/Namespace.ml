open Checked
open Ostap
open Common

let make n =
  Random.self_init ();
  let suffix =
    let l = "abcdefghijklmnopqrstuvwxyz" in
    let n = String.length l in
    (fun _ ->
      let buf = Buffer.create 5 in
      for i=0 to 3 do Buffer.add_char buf l.[Random.int n] done;
      Buffer.contents buf
    )
  in
  let module M = Map.Make (String) in
  let module S = Set.Make (String) in
  let context = ref ["", true, M.empty] in
  let names   = ref S.empty in
  object(self)
    method name = n
    method lookupShallow name =
      let rec inner flag = function
      | (namespace, v, m) :: tl when flag or v -> 
         (try !! (M.find name m) with Not_found -> inner false tl)
      | (namespace, _, _) :: tl -> inner false tl
      | [] -> Fail [Msg.make "unresolved %0 \"%1\"" [|n; name|] (locate name)]
      in
      inner true !context
    method lookup name =
      let rec inner = function
      | (_, _, m) :: tl -> (try !! (M.find name m) with Not_found -> inner tl)
      | [] -> Fail [Msg.make "unresolved %0 \"%1\"" [|n; name|] (locate name)]
      in
      inner !context
    method update name value =
      names := S.add name !names;
      let (space, v, m) :: t  = !context in 
        try 
          ignore (M.find name m);
          Fail [Msg.make "duplicate %0 \"%1\"" [|n; name|] (locate name)]
        with Not_found -> 
          context := (space, v, M.add name value m) :: t; 
          !! ()
    method updateList l = 
      list (List.map (fun (n, v) -> self#update n v) l) -?-> (fun _ -> ())
    method getInternal name =
      let (space, _, _)::_ = !context in
      space ^ name
    method genericDown name flag = 
      let (prev, _, _)::_ = !context in      
      let prev = if prev = "" then "" else prev in
      context := (prev ^ name, flag, M.empty) :: !context      
    method downGlobal name = self#genericDown name true
    method down name = self#genericDown name false
    method up    ()   = match !context with [_] -> () | _ :: t -> context := t
    method namer ()   =
      object(self)
        method getName recommendation =
          let rec inner str =
            if not (S.mem str !names)
            then (names := S.add str !names; str)
            else inner (str ^ suffix ())
          in
          inner recommendation
      end
  end
