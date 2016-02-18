open Common
open Checked
open List

(* --------------------------------------- Name resolver ---------------------------- *)

module Resolve =
  struct
    class ['a, 'b] env =
      object(self)
        inherit ['a, 'b] L3.Resolve.env
        method lookup name = (idents#lookup name : ('a, Ostap.Msg.t) t)
      end
  end

(* ------------------------------------------ Lifting ------------------------------- *)

module Lift = 
  struct

    let lambda namer (name, ((c, t, v), p), stmts) = 
      let module S = Set.Make (String) in
      let module M = Map.Make (String) in      
      let types    = ref M.empty in
      let locals   = ref M.empty in
      let addLocals name l  = locals := M.add name l !locals in   
      let addType name typ  = types := M.add name typ !types in
      let typeOf  name      = M.find name !types in
      let localOf name proc = try S.mem name (M.find proc !locals) with Not_found -> false in
      let getVars args v =
        fold_left 
          (fun acc (names, t) -> 
             fold_right (fun name acc -> addType name t; S.add name acc) names acc
          ) 
          (fold_left (fun acc (_, name, t) -> addType name t; S.add name acc) S.empty args)
          v 
      in   
      let testVars vars = (fun name -> not (S.mem name vars)) in
      let rec updateProcInfo notGlobal (calls, uses) (name, args, ((_, _, v), p), stmts) =        
        let vars = getVars args v in
        addLocals name vars;
        let notLocal = testVars vars in
        let called, used = ref S.empty, ref S.empty in
        let var  name = if notLocal name && notGlobal name then used := S.add name !used in
        let proc name = called := S.add name !called in        
        iter (fun stmt -> 
                let rec expr e = ( 
                  SimpleExpression.imap (SimpleExpression.mapT (fun _ _ -> ())) ++
                  (fun ext -> function
                   | `Index (x, i) -> ext expr x; ext expr i
                   | `Field (x, _) -> ext expr x
                   | `Ident (name, _) -> var name
                   | x -> ext expr x                                           
                  )                     
                ) apply e
                in                
                SimpleStatement.imap (SimpleStatement.mapT (fun _ _ -> ())) expr expr 
                (fun self stmt ->
                   ExtendedStatement.imap                        
                     (ExtendedStatement.mapT (fun _ _ -> ()))
                     expr expr expr 
                     (fun _ -> function `Call (name, args, _) -> map expr args; proc name | x -> self x) 
                     stmt
                )
                stmt
             ) stmts;
        fold_left (updateProcInfo notGlobal) (M.add name !called calls, M.add name !used uses) p
      in
      let notGlobal = testVars (getVars [] v) in
      let calls, uses = fold_left (updateProcInfo notGlobal) (M.empty, M.empty) p in
      let rec iterate uses =
        let flag, uses' = 
          M.fold (fun p calls (flag, uses) -> 
                    let current = M.find p uses in
                    let updated = 
                      S.fold (fun g acc -> S.union (try M.find g uses with Not_found -> S.empty) acc) 
                        calls S.empty 
                    in
                    if S.subset updated current 
                    then flag, uses 
                    else true, M.add p updated uses
                 ) calls (false, uses)
        in
        if not flag then uses' else iterate uses'
      in
      let uses = iterate uses in      
      let tdecls = fold_right (fun (name, typ) tdecls ->
                     match typ with 
                     | `User _ | `Bool | `Int -> tdecls
                     | _ -> let tname = namer#getName "typename" in
                            types := M.add name (`User (tname, tname, typ)) !types; 
                            (tname, typ) :: tdecls
                   ) (M.bindings !types) []
      in
      let formals, actuals = 
        M.fold (fun p names (f, a) -> 
                  let names = sort compare (S.elements (S.diff names (M.find p !locals))) in
                  M.add p (map (fun n -> (`Var, n, typeOf n)) names) f, 
                  M.add p (map (fun n -> fun p -> if localOf n p then `Ident (n, `Var (n, typeOf n)) 
                                                                 else `Ident (n, `VParam (n, typeOf n))
                               ) names
                          ) a
               ) uses (M.empty, M.empty) 
      in
      let rec modify (name, args, ((c, t, v), p), stmts) =
        let args  = try args @ M.find name formals with Not_found -> args in
        let stmts = map (fun stmt ->
                           let rec expr e = (
                             SimpleExpression.imap (SimpleExpression.mapT (fun _ x -> x)) ++
                             (fun ext -> function
                               | `Index (a, i) -> `Index (ext expr a, ext expr i)
                               | `Field (x, f) -> `Field (ext expr x, f)
                               | `Ident (id, e) -> 
                                   `Ident (id, if (localOf id name) or (not (notGlobal id)) 
                                               then e 
                                               else `VParam (id, typeOf id)
                                          )
                               | e -> ext expr e
                             ) 
                           ) apply e 
                           in
			   (SimpleStatement.imap (SimpleStatement.mapT (fun _ x -> x)) expr expr ++
                            ExtendedStatement.imap (ExtendedStatement.mapT (fun _ x -> x)) expr expr expr 
                           )
                           (fun self -> function 
                            | `Call (pname', args, `Proc (pname, fargs)) -> 
                                let args = 
                                  try map expr args @ map (fun f -> f name) (M.find pname' actuals) 
                                   with Not_found -> map expr args 
                                in
                                let fargs = try fargs @ M.find pname' formals with Not_found -> fargs in
                                `Call (pname', args, `Proc (pname, fargs))
                            | s -> self s
                           )                                   
                           stmt
                        ) stmts
        in
        let v' = 
          map (fun ([name], t) -> [name], try typeOf name with Not_found -> t)
          (flatten (map (fun (names, t) -> map (fun name -> [name], t) names) v))
        in
        name, args, ((c, t, v'), map modify p), stmts
      in
      L4.Lift.lambda0 (name, ((c, t @ tdecls, v), map modify p), stmts)
  end

(* ------------------------------------------ Toplevel ------------------------------ *)

let top source = L1.toplevel 
  (fun (p, n) ->
     let lifted = L4.Lower.program ((Lift.lambda n (L4.Lift.types p)), n) in
     Ostap.Pretty.toString (L4.PrintR.program lifted), 
     Ostap.Pretty.toString (L4.CGen.program lifted)
  ) (L4.Parse.program, L4.Print.program, L4.Resolve.program false (new Resolve.env), L4.Typecheck.program) source 
