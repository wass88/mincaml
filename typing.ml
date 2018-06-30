open Syntax

exception Error of string

let err s = raise (Error s)

(* Type Environment *)
type tyenv = tysc Environment.t

type subst = (tyvar * ty) list

let print_subst subst = List.iter
  (fun (tv, ty) -> print_int tv;print_string ":"; pp_ty ty; print_newline ()) subst

let print_eps eps = List.iter
  (fun (x, y) -> pp_ty x;print_string ":"; pp_ty y; print_newline ()) eps

let rec tvty_type tv ty t = match t with
    TyVar tv' when tv' = tv -> ty
  | TyFun (dom, cod) -> TyFun (tvty_type tv ty dom, tvty_type tv ty cod)
  | TyList t -> TyList (tvty_type tv ty t)
  | t -> t

let rec subst_type (st:subst) (t:ty) =
  List.fold_left (fun t' (tv, ty) -> tvty_type tv ty t') t st

let eps_of_subst (st:subst) = List.map (fun (tv, t) -> (TyVar tv, t)) st

let subst_eps (st:subst) (eps:(ty * ty) list) =
  List.map (fun (t1, t2) -> (subst_type st t1, subst_type st t2)) eps

let rec unify = function
    [] -> []
  | (t1, t2) :: rest -> if t1 = t2 then unify rest
      else match t1, t2 with
          TyFun (td1, tc1), TyFun(td2, tc2) ->
            unify ((td1, td2) :: (tc1, tc2) :: rest)
        | TyList tv1, TyList tv2 -> unify ((tv1, tv2) :: rest)
        | TyTuple (h1::t1), TyTuple (h2::t2) -> unify ((h1, h2) :: (TyTuple t1, TyTuple t2) :: rest)
        | TyTuple [], TyTuple [] -> unify rest
        | TyVar tv, t ->
            if MySet.member tv (freevar_ty t)
              then err ("recursion type")
              else let st = (tv, t) in st :: unify (subst_eps [st] rest)
        | t, TyVar tv -> unify ((TyVar tv, t) :: rest)
        | _, _ -> err("unmatched types")

let rec freevar_tyenv (tyenv : tysc Environment.t) =
  Environment.fold_right (fun (TyScheme (_, ty)) (res: tyvar MySet.t) ->
    MySet.union (freevar_ty ty) res) tyenv MySet.empty

let closure ty (tyenv : tysc Environment.t) subst =
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
        (fun id -> freevar_ty (subst_type subst (TyVar id)))
        fv_tyenv') in
  let ids = MySet.diff (freevar_ty ty) fv_tyenv in
  TyScheme (MySet.to_list ids, ty)

let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)
  | Cons -> ([(TyList ty1, ty2)], ty2)

let rec eps_bind cty p = match p with
    VarP id -> let t = fresh_ty () in
      ([(id, t)], [(t, cty)])
  | NilP -> let t = fresh_ty () in ([], [(TyList t, cty)])
  | ConsP (x, xs) -> let t = fresh_ty () in
      let (xb,  xe ) = eps_bind t x in
      let (xsb, xse) = eps_bind (TyList t) xs in
        (xb @ xsb, (TyList t, cty) :: xe @ xse)
  | TupleP xs ->
      let res = List.map (fun p ->
        let t = fresh_ty () in
        let (sub, e) = eps_bind t p in
        (t, sub, e)) xs in
      let ts = List.map (fun (t,_,_)->t) res in
      let subs = List.concat (List.map (fun (_,s,_)->s) res) in
      let es = List.concat (List.map (fun (_,_,e)->e) res) in
        (subs, (TyTuple ts, cty) :: es)
      

let rec eps_env_branch (cty:ty) (tyenv:tysc Environment.t) (p:pat) =
  let (binds, eps_b) = eps_bind cty p in
    if not (Eval.check_unique_ids binds) then err ("Exist duplicate binds")
    else
      let tyenv' = List.fold_left (fun tyenv (id, ty) ->
        Environment.extend id (tysc_of_ty ty) tyenv) tyenv binds in
      (eps_b, tyenv')

let rec ty_exp (tyenv : tysc Environment.t) = function
    Var x ->
      (try
        let TyScheme (vars, ty) = Environment.lookup x tyenv in
        let s = List.map (fun id -> (id, TyVar (fresh_tyvar ()))) vars in
          ([], subst_type s ty)
      with  Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit _ -> ([], TyInt)
  | BLit _ -> ([], TyBool)
  | Nil -> ([], TyList (fresh_ty ()))
  | BinOp (op, exp1, exp2) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (eps3, ty) = ty_prim op ty1 ty2 in
      let eps = (eps_of_subst s1) @ (eps_of_subst s2) @ eps3 in
      let s3 = unify eps in (s3, subst_type s3 ty)
  | IfExp (exp1, exp2, exp3) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (s3, ty3) = ty_exp tyenv exp3 in
      let eps = (ty1, TyBool) :: (ty2, ty3) ::
                (eps_of_subst s1) @ (eps_of_subst s2) @ (eps_of_subst s3) in
      let res = unify eps in (res, subst_type res ty2)
  | LetExp (ides, exp2) ->
      let (s, tyenv') = List.fold_left
        (fun (eps_, (env_ : tysc Environment.t)) (id, exp) ->
          let (s1, ty1) = ty_exp tyenv exp in
            (eps_of_subst s1 @ eps_, Environment.extend id (closure ty1 tyenv s1) env_)
        ) ([], tyenv) ides in
      let (s2, ty2) = ty_exp tyenv' exp2 in
      let eps = (eps_of_subst s2) @ s in
      let res = unify eps in (res, subst_type res ty2)
  | LetRecExp (f, d, c, e) ->
      let domty = fresh_ty () in
      let codty = fresh_ty () in
      let tyenv' = Environment.extend f (tysc_of_ty (TyFun (domty, codty))) tyenv in
      let tyenv'' = Environment.extend d (tysc_of_ty domty) tyenv' in
      let (cs, cty) = ty_exp tyenv'' c in
      let (es, ety) = ty_exp tyenv' e in
      let eps = (codty, cty) :: eps_of_subst cs @ eps_of_subst es in
      let res = unify eps in (res, subst_type res ety)
  | FunExp (id, exp) ->
      let domty = fresh_ty () in
      let s, ranty = ty_exp (Environment.extend id (tysc_of_ty domty) tyenv) exp in
        (s, TyFun (subst_type s domty, ranty))
  | DFunExp _ -> err ("Not Implemented")
  | AppExp (exp1, exp2) ->
      let codty = fresh_ty () in
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let eps = (ty1, TyFun(ty2, codty)) ::
                  (eps_of_subst s1) @ (eps_of_subst s2) in
      let res = unify eps in (res, subst_type res codty)
  | MatchExp (c, bs) ->
      let (cs, cty) = ty_exp tyenv c in
      let resty = fresh_ty () in
      let eps = List.fold_left (fun eps' (p, e) ->
        let (b_eps, b_env) = eps_env_branch cty tyenv p in
        let (es, ety) = ty_exp b_env e in
          (resty, ety) :: eps_of_subst es @ b_eps @ eps'
      ) (eps_of_subst cs) bs in
      let res = unify eps in (res, subst_type res resty)
  | TupleExp es ->
     let s_tys = List.map (ty_exp tyenv) es in
     let eps = List.concat (List.map (fun (s, ty) -> eps_of_subst s) s_tys) in
     let res = unify eps in
     let tys = List.map (fun (s, ty) -> subst_type res ty) s_tys in
     (res, TyTuple tys)

let ty_decl tyenv = function
    Exp e -> let (_, ty) = ty_exp tyenv e in (tyenv, [ty])
  | Decl ides ->
      let (eps, tyenv, tys) = List.fold_left (fun (eps_, tyenv_, tys) (id, e) ->
        let (s1, ty1) = ty_exp tyenv e in
          (eps_of_subst s1 @ eps_,
           Environment.extend id (closure ty1 tyenv s1) tyenv_, ty1::tys))
        ([], tyenv, []) ides in
      let res = unify eps in
        (tyenv, List.map (subst_type res) (List.rev tys))
  | RecDecl _ -> err ("Not Implemented!")
