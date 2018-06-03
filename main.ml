open Syntax
open Eval
open Typing

let rec zip l r res = match l with
    [] -> res
  | hl::tl -> match r with
      [] -> res
    | hr::tr -> zip tl tr ((hl, hr) :: res)
let zip l r = zip l r []

let untyped (env, tyenv) (p, decl) =
    let (idvs, newenv) = eval_decl env decl in
      List.iter (fun (id, v) ->
        if p then (Printf.printf "val %s = " id;
        pp_val v;
        print_newline())
      ) idvs;
      (newenv, tyenv)

let typed (env, tyenv) (p, decl) =
    let (newtyenv, tys) = ty_decl tyenv decl in
    let (idvs, newenv) = eval_decl env decl in
      List.iter (fun ((id, v), ty) ->
        if p then (Printf.printf "val %s : " id;
        pp_ty ty;
        print_string " = ";
        pp_val v;
        print_newline())
      ) (zip idvs tys);
      (newenv, newtyenv)

let opt_typed = typed

let rec need_print ids = function
    [] -> []
  | (Decl ((h,_)::_) as d)::t -> if List.mem h ids
      then (false, d) :: need_print ids t
      else (true, d) :: need_print (h::ids) t
  | d::t -> (true, d) :: need_print ids t

let need_print l = List.rev (need_print [] (List.rev l))

let rec read_eval_print batch ch env tyenv =
  if not batch then ( print_string "# "; flush stdout ) else ();
  try
    let lexch = Lexing.from_channel ch in
    let decls = Parser.toplevel Lexer.main lexch in
    let (newenv, newtyenv) =
      List.fold_left opt_typed (env, tyenv) (need_print decls)
    in read_eval_print batch ch newenv newtyenv
  with e ->
    Printexc.to_string e |> print_endline;
    Printexc.print_backtrace stdout;
    read_eval_print batch ch env tyenv

let initial_env = 
  Environment.extend "i" (IntV 1) @@
  Environment.extend "ii" (IntV 2) @@
  Environment.extend "iii" (IntV 3) @@
  Environment.extend "iv" (IntV 4) @@
  Environment.extend "v" (IntV 5)  @@
  Environment.extend "x" (IntV 10) Environment.empty

let initial_tyenv = Environment.map tysc_of_ty @@
  Environment.extend "i" TyInt @@
  Environment.extend "ii" TyInt @@
  Environment.extend "iii" TyInt @@
  Environment.extend "iv" TyInt @@
  Environment.extend "v" TyInt @@
  Environment.extend "x" TyInt Environment.empty

let _ =
  Printexc.record_backtrace true;
  let batch = Array.length Sys.argv = 2 in
  let ch = if not batch then stdin else open_in Sys.argv.(1) in
  read_eval_print batch ch initial_env initial_tyenv
