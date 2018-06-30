open Syntax 

type exval = 
    IntV of int
  | BoolV of bool
  | NilV
  | ConsV of exval * exval
  | ProcV of id * exp * dnval Environment.t ref
  | DProcV of id * exp
  | TupleV of exval list
  | GadtV of id * exval option
and dnval = exval

exception Error of string

let err s = raise (Error s)

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | NilV -> "[]"
  | ConsV (l, r) ->
    let rec string_of_cons = function
        NilV -> ""
      | ConsV (l, r) -> "; " ^ string_of_exval l ^ string_of_cons r
      | o -> string_of_exval o (* weird *) in
     "[" ^ string_of_exval l ^ string_of_cons r ^ "]"
  | ProcV (id, exp, env) -> "<function>"
  | DProcV (id, exp) -> "<dfunction>"
  | TupleV exps -> "(" ^ String.concat "," (List.map string_of_exval exps) ^ ")"
  | GadtV (id, None) -> id
  | GadtV (id, Some exp) -> "(" ^ id ^ string_of_exval exp ^ ")"

let pp_val v = print_string (string_of_exval v)

let rec apply_prim op arg1 arg2 = match op, arg1, arg2 with Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")
  | Cons, i1, i2 -> ConsV (i1, i2)

let rec bind_pattern p e = match p, e with
    VarP i, e -> Some [(i, e)]
  | NilP, NilV -> Some []
  | ConsP (lp, rp), ConsV (l, r) -> (match bind_pattern lp l with
          None -> None
        | Some lb -> (match bind_pattern rp r with
              None -> None
            | Some rb -> Some (lb @ rb)))
  | TupleP [], TupleV [] -> Some []
  | TupleP (hp::tp), TupleV (h::t) -> (match bind_pattern hp h with
          None -> None
        | Some hb -> (match bind_pattern (TupleP tp) (TupleV t) with
              None -> None
            | Some tb -> Some (hb @ tb)
      ))
  | GadtP (x, None), GadtV (y, None) when x = y -> Some []
  | GadtP (x, Some p), GadtV (y, Some v) when x = y -> bind_pattern p v
  | _ -> None

let rec check_unique_ids = function
    [] -> true
  | (h,_)::t -> List.for_all (fun (x,_) -> x <> h) t && check_unique_ids t

let rec eval_exp env = function
    Var x -> 
      (try Environment.lookup x env with 
        Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | Nil -> NilV
  | BinOp (op, exp1, exp2) -> 
      let arg1 = eval_exp env exp1 in
      let arg2 = eval_exp env exp2 in
      apply_prim op arg1 arg2
  | MatchExp (c, bs) ->
    let cond = eval_exp env c in
    (match (List.fold_left (function
        None -> fun (p, b) -> (match bind_pattern p cond with
            None -> None
          | Some bl ->
              if check_unique_ids bl then
                let newenv = (List.fold_left (fun env' (i, e) ->
                  Environment.extend i e env') env bl) in
                Some (eval_exp newenv b)
              else err ("Duplicate variables in a pattern")
        )
      | Some x -> fun _ -> Some x
    ) None bs) with
      None -> err ("No Matched")
    | Some x -> x)
  | IfExp (exp1, exp2, exp3) ->
      let test = eval_exp env exp1 in
        (match test with
            BoolV true -> eval_exp env exp2 
          | BoolV false -> eval_exp env exp3
          | _ -> err ("Test expression must be boolean: if"))
  | LetExp (idexps, exp2) ->
      if check_unique_ids idexps then
        let newenv = List.fold_left (fun e (id, exp) ->
          Environment.extend id (eval_exp env exp) e) env idexps in
        eval_exp newenv exp2
      else err ("Bind same variables")
  | LetRecExp (id, para, exp1, exp2) ->
      let dummyenv = ref Environment.empty in
      let newenv = Environment.extend id (ProcV (para, exp1, dummyenv)) env in
      dummyenv := newenv;
      eval_exp newenv exp2
  | FunExp (id, exp) -> ProcV (id, exp, ref env)
  | DFunExp (id, exp) -> DProcV (id, exp)
  | AppExp (exp1, exp2) ->
      let funval = eval_exp env exp1 in
      let arg = eval_exp env exp2 in
        (match funval with
            ProcV (id, body, env') ->
              let newenv = Environment.extend id arg !env' in
                eval_exp newenv body
          | DProcV (id, body) ->
              let newenv = Environment.extend id arg env in
                eval_exp newenv body
          | _ -> err ("Non-function value is applied"))
  | TupleExp exps ->
      TupleV (List.map (fun e -> eval_exp env e) exps)
  | GadtExp (x, None) -> GadtV (x, None)
  | GadtExp (x, Some exp) -> GadtV (x, Some (eval_exp env exp))

let fresh_x () = "x" ^ string_of_int (fresh_tyvar ())

let conv_gadtbranch = function
    GadtLeaf (x, _, _) -> (x, GadtExp (x, None))
  | GadtBranch (x, _, _, _) -> 
      let y = fresh_x () in (x, FunExp (y, GadtExp (x, Some (Var y))))

let conv_gadt bs =
  Decl (List.map conv_gadtbranch bs)

let rec eval_decl env = function
    Exp e -> let v = eval_exp env e in ([("-", v)], env)
  | Decl ides ->
      if check_unique_ids ides then
        let (newenv, res) = List.fold_left (fun (e, r) (id, exp) ->
          let v = eval_exp env exp in
          (Environment.extend id (eval_exp env exp) e, (id,v)::r))
            (env, []) ides in
        (List.rev res, newenv)
      else err ("Bind same variables")
  | RecDecl (id, para, e) ->
      let dummyenv = ref Environment.empty in
      let f = ProcV (para, e, dummyenv) in
      let newenv = Environment.extend id f env in
      dummyenv := newenv;
      ([(id, f)], Environment.extend id f env)
  | Gadt (t, bs) -> eval_decl env (conv_gadt bs)
