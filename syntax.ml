(* ML interpreter / type reconstruction *)
open MySet

type id = string
let dummy_id x = "dummy" ^ string_of_int x

type pat =
  | VarP of id
  | NilP
  | ConsP of pat * pat

type binOp = Plus | Mult | Cons | Lt

type exp =
    Var of id
  | ILit of int
  | BLit of bool
  | Nil
  | BinOp of binOp * exp * exp
  | IfExp of exp * exp * exp
  | LetExp of ((id * exp) list) * exp
  | LetRecExp of id * id * exp * exp
  | FunExp of id * exp
  | DFunExp of id * exp
  | AppExp of exp * exp
  | MatchExp of exp * (pat * exp) list

type program = 
    Exp of exp
  | Decl of (id * exp) list
  | RecDecl of id * id * exp

type tyvar = int
let print_tyvar tv = print_string "'a"; print_int tv

type ty =
    TyInt
  | TyBool
  | TyList of ty
  | TyVar of tyvar
  | TyFun of ty * ty

let parens p x = print_string "("; p x; print_string ")"
let arrow () = print_string " -> "
let rec pp_ty = function
    TyInt -> print_string "int"
  | TyBool ->  print_string "bool"
  | TyList (TyFun _ as f) -> parens pp_ty f; print_string " list"
  | TyList ty -> pp_ty ty; print_string " list"
  | TyVar tv -> print_tyvar tv
  | TyFun (TyFun _ as f, ty2) -> 
      parens pp_ty f; arrow (); pp_ty ty2
  | TyFun (TyList _ as l, ty2) -> 
      parens pp_ty l; arrow (); pp_ty ty2
  | TyFun (ty1, ty2) -> 
      pp_ty ty1; arrow (); pp_ty ty2

let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
      counter := v + 1; v
  in body

let fresh_ty () = TyVar (fresh_tyvar ())

let rec freevar_ty = function
    TyVar tv -> singleton tv
  | TyFun (ty1, ty2) -> union (freevar_ty ty1) (freevar_ty ty2)
  | TyList ty -> freevar_ty ty
  | _ -> empty

type tysc = TyScheme of tyvar list * ty
let tysc_of_ty ty = TyScheme ([], ty)
let freevar_tysc (TyScheme (s, ty)) = MySet.diff (freevar_ty ty) (from_list s)

let pp_tysc (TyScheme (cl, ty)) =
  List.iter (fun c -> print_string "@"; print_tyvar c) cl; pp_ty ty
