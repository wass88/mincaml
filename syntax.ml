(* ML interpreter / type reconstruction *)
open MySet

type id = string
let dummy_id x = "dummy" ^ string_of_int x

type pat =
  | VarP of id
  | NilP
  | ConsP of pat * pat
  | TupleP of pat list
  | GadtP of id * pat option

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
  | TupleExp of exp list
  | GadtExp of id * exp option

type tyvar = int
let p_tyvar tv = "'a" ^ string_of_int tv
let print_tyvar tv = print_string (p_tyvar tv)

type ty =
    TyInt
  | TyBool
  | TyList of ty
  | TyVar of tyvar
  | TyFun of ty * ty
  | TyTuple of ty list

type tySyntax =
    TySyntaxVar of id
  | TySyntaxName of id
  | TySyntaxFun of tySyntax * tySyntax
  | TySyntaxTuple of tySyntax list
  | TySyntaxGadt of tySyntax * id

let rec p_tysyn = function
    TySyntaxVar x -> x
  | TySyntaxName x -> x
  | TySyntaxFun (x, y) -> "(" ^ p_tysyn x ^ "->" ^ p_tysyn y ^ ")"
  | TySyntaxTuple xs -> "(" ^ String.concat "*" (List.map p_tysyn xs) ^ ")"
  | TySyntaxGadt (t, x) -> p_tysyn t ^ "->" ^ x

type gadtBranch =
    GadtLeaf of id * tySyntax * id
  | GadtBranch of id * tySyntax * tySyntax * id

let p_gadtbranch = function
    GadtLeaf (x, ty, y) -> x ^ ":" ^ p_tysyn ty ^ " " ^ y
  | GadtBranch (x, tyd, ty, y) -> x ^ ":" ^ p_tysyn tyd ^ "->" ^ p_tysyn ty ^ " " ^ y
  
type program = 
    Exp of exp
  | Decl of (id * exp) list
  | RecDecl of id * id * exp
  | Gadt of id * gadtBranch list

let parens p x = "(" ^ p x ^ ")"
let arrow () = " -> "
let rec p_ty = function
    TyInt -> "int"
  | TyBool ->  "bool"
  | TyList (TyFun _ as f) -> parens p_ty f ^ " list"
  | TyList ty -> p_ty ty ^ " list"
  | TyVar tv -> p_tyvar tv
  | TyFun (TyFun _ as f, ty2) -> 
      parens p_ty f ^ arrow () ^ p_ty ty2
  | TyFun (TyList _ as l, ty2) -> 
      parens p_ty l ^ arrow () ^ p_ty ty2
  | TyFun (ty1, ty2) -> 
      p_ty ty1 ^ arrow () ^ p_ty ty2
  | TyTuple [] -> "unit"
  | TyTuple l -> String.concat "*" (List.map p_ty l)

let pp_ty t = print_string (p_ty t)

let p_exp e = "<exp>"
let p_decl (x, c) = x ^ " " ^ p_exp c
let p_gadt ty b =
  ty ^ " = \n" ^ String.concat "\n|" (List.map p_gadtbranch b)

let p_program = function
    Exp e -> "EXP " ^ p_exp e
  | Decl ls -> "DECL " ^ String.concat ";;\n" (List.map p_decl ls)
  | RecDecl (f, x, c) -> "REC " ^ f ^ p_decl (x, c)
  | Gadt (ty, b) -> "GADT " ^ p_gadt ty b

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
