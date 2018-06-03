#計算機実験SW 課題2

## 2項

### ex3.2.1

main.mlの環境に値を追加する。
```
let initial_env = 
  Environment.extend "i" (IntV 1) @@
  Environment.extend "ii" (IntV 2) @@
  Environment.extend "iii" (IntV 3) @@
  Environment.extend "iv" (IntV 4) @@
  Environment.extend "v" (IntV 5)  @@
  Environment.extend "x" (IntV 10) Environment.empty
```

実行結果は以下のとおりである。ローマ数字がIntVに評価されている。
```
# iv + iii * ii;;
val - = 10
```

### ex3.2.2

実行結果は以下のとおりである。パースの失敗や実行時例外が表示され, 継続している。
```
# 1 + 1;;
val - = 2
# 1 +;;
Parser.MenhirBasics.Error
# a;;
Eval.Error("Variable not bound: a")
Raised at file "list.ml", line 158, characters 10-25
Called from file "environment.ml", line 9, characters 6-22
```

try - withを追加することで例外を標準出力している。
```
let rec read_eval_print env =
  print_string "# ";
  flush stdout;
  try
    let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    let (id, newenv, v) = eval_decl env decl in
      Printf.printf "val %s = " id;
      pp_val v;
      print_newline();
      read_eval_print newenv
  with e ->
    Printexc.to_string e |> print_endline;
    Printexc.print_backtrace stdout;
    read_eval_print env

let _ =
  Printexc.record_backtrace true;
  read_eval_print initial_env
```

### ex3.2.3


lexer.mll: トークンに記号`&&` `||`を追加
```
main = parse
...
| "&&" { Parser.ANDAND }
| "||" { Parser.OROR }
```

parser.mly: 左結合である。IFの糖衣構文に変換する。
```
%token PLUS MULT LT ANDAND OROR
...
ORORExpr :
    l=ORORExpr OROR r=ANDANDExpr { IfExp (l, l, r) }
  | e=ANDANDExpr { e }

ANDANDExpr :
    l=ANDANDExpr ANDAND r=LTExpr { IfExp (l, r, l) }
  | e=LTExpr { e }
```

### ex3.2.4

lexer.mll: コメントエントリポイントを追加。

ネストしたコメントに対応できるようにする必要がある。

```
rule main = parse
...
| "(*" { commentout lexbuf |> ignore; main lexbuf }

and commentout = parse
  "(*" { commentout lexbuf |> ignore; commentout lexbuf }
| "*)" { () }
| _ { commentout lexbuf }
```

## 3項

### ex3.3.1

let宣言, let式の文法を追加。
```
toplevel :
...
  | LET x=ID EQ e=Expr SEMISEMI { Decl (x, e) }
Expr :
...
  | e=LetExpr { e }

LetExpr :
    LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }
```


Let式を評価する時, 束縛を追加した環境で式を評価する。
Let宣言を評価する時, 束縛を追加して新しい環境を返す。
```
let rec eval_exp env = function
...
  | LetExp (id, exp1, exp2) ->
      let value = eval_exp env exp1 in
      eval_exp (Environment.extend id value env) exp2

let eval_decl env = function
...
  | Decl (id, e) -> let v = eval_exp env e in
      (id, Environment.extend id v env, v)
```

### ex3.3.2

以下のようなケースに対応する必要がある。
```
# let x = 1 let y = 2 let x = 3;;
val y = 2
val x = 3
```

### ex3.3.3

`read_eval_print`に引数batchとチャンネルchを付け加えた。
実行時の引数があるときにはbatchがtrueになる。
chにはstdinまたは実行時の引数のファイルが与えられる。

```
let rec read_eval_print batch ch env tyenv =
  if not batch then ( print_string "# "; flush stdout ) else ();

let _ =
  Printexc.record_backtrace true;
  let batch = Array.length Sys.argv = 2 in
  let ch = if not batch then stdin else open_in Sys.argv.(1) in
  read_eval_print batch ch initial_env initial_tyenv
```

`./miniml test.ml`で引数のファイルを評価する。

### ex3.3.4

定義を束縛のリストにする。

```
Decl :
    LET x=ID ps=ID* EQ e=Expr { Decl (x, append_params ps e) }
    LET b=LetBody t=list(AND l=LetBody {l}) { Decl (b::t) }

LetBody :
    x=ID ps=ID* EQ e1=Expr { (x, append_params ps e1) }
type program =
...
  | Decl of (id * exp) list
```

複数の束縛を同じ環境で評価する。

```
let eval_decl env = function
...
  | Decl ides ->
      if check_unique_ids ides then
        let (newenv, res) = List.fold_left (fun (e, r) (id, exp) ->
          let v = eval_exp env exp in
          (Environment.extend id (eval_exp env exp) e, (id,v)::r))
            (env, []) ides in
        (List.rev res, newenv)
      else err ("Bind same variables")
```

## 4項

### ex3.4.1

関数適用と関数の文法を追加。
関数適用は最も結合が強い。
```
AppExpr :
    e1=AppExpr e2=AExpr { AppExp (e1, e2) }
  | e=AExpr { e }

FunExpr :
    FUN x=ID RARROW e=Expr { FunExp (x, e) }
```

関数を評価すると現在の環境をクロージャとして持つProcVを返す。
関数適用ではProcVのクロージャにに束縛を追加して評価する。

```
let rec eval_exp env = function
...
  | FunExp (id, exp) -> ProcV (id, exp, env)
  | AppExp (exp1, exp2) ->
      let funval = eval_exp env exp1 in
      let arg = eval_exp env exp2 in
        (match funval with
            ProcV (id, body, env') ->
              let newenv = Environment.extend id arg env' in
                eval_exp newenv body
          | _ -> err ("Non-function value is applied"))
```

```
# (fun x -> x + 1) 1;;
val - = 2
# (fun f -> fun x -> f (f x)) (fun x -> x + 1) 1;;
val - = 3
# let x = 1 in let f = (fun y -> x + y) in let x = 2 in f 0;;
val - = 1
# let i = fun x -> x;;
val i = <function>
# i 1;;
val - = 1
```

### ex3.4.2

糖衣構文の変換を行う。以下のような変換を行っている。

```
(+) => (fun x0 -> fun x1 -> x0 + x1)
```

```
  | LPAREN o=BinOP RPAREN {
    FunExp(dummy_id 0, FunExp(dummy_id 1,
      BinOp(o, Var (dummy_id 0), Var (dummy_id 1)))) }

BinOP :
    PLUS { Plus }
  | MULT { Mult }
  | LT { Lt }
```

### ex3.4.3

糖衣構文の変換を行う。以下のような変換を行っている。

```
let f x y = e => let f = fun x -> fun y -> e
```

補助関数として, 式に引数のリストを与えて関数木を渡す関数を定義。
```
let append_params ps e =
  List.fold_left (fun e p -> FunExp(p, e)) e (List.rev ps)

Decl :
    LET x=ID ps=ID* EQ e=Expr { Decl (x, append_params ps e) }
```

### ex3.4.4

```
let makefact = fun maker -> fun x ->
  if x < 1 then 1 else x * maker maker (x + -1) in
  let fact = fun x -> makefact makefact x in
    fact 5;;
```

```
$ ./ex2/miniml ./ex2/report/fact.ml
val - = 120
```

### ex3.4.5

評価を現在の環境で行う。クロージャを持つ必要が無いので, コンストラクタに環境を与えていない。

```
let rec eval_exp env = function
            ProcV (id, body, env') ->
              let newenv = Environment.extend id arg !env' in
                eval_exp newenv body
          | DProcV (id, body) ->
              let newenv = Environment.extend id arg env in
                eval_exp newenv body
```
### ex3.4.6

1行目のfactには自由変数が存在しないのでfunとdfunの違いはない。
2行目でdfunで定義することでfactが2行目のfactになる。

```
let fact = fun n -> n + 1 in
let fact = dfun n -> if n < 1 then 1 else n * fact (n + -1) in
fact 5;;
```

## 5項

### ex3.5.1

実行結果は以下のとおりである。
```
# let rec f = fun x -> if 10 < x then 0 else f (x + 1) + 1;;
val f = <function>
# f 0;;
val - = 11
# let rec f = fun x -> if 10 < x then 0 else f (x + 1) + 1 in f 0;;
val - = 11
```

ProcVのクロージャの型を参照にする。
ProcVのコストラクタで現在の環境に自身の束縛を追加した環境を与える。

```
type exval =
...
  | ProcV of id * exp * dnval Environment.t ref

let rec eval_exp env = function
...
  | LetRecExp (id, para, exp1, exp2) ->
      let dummyenv = ref Environment.empty in
      let newenv = Environment.extend
          id (ProcV (para, exp1, dummyenv)) env in
      dummyenv := newenv;
      eval_exp newenv exp2
```

## 6項
## ex3.6.1


match式とそこで用いるパターンの文法を追加。
```
MatchExpr :
    MATCH c=Expr WITH pat=Branch pats=list(PIPE b=Branch { b })
      {MatchExp (c, pat::pats) }

Branch :
    p=Pattern RARROW e=Expr { (p, e) }

Pattern :
  | x=ID { VarP x }
  | NIL { NilP }
  | l=Pattern CONS r=Pattern { ConsP (l, r) }
```

match式では条件にあうパターンを選び, パターンの変数を束縛して式を評価する。
```
let rec bind_pattern p e = match p, e with
    VarP i, e -> Some [(i, e)]
  | NilP, NilV -> Some []
  | ConsP (lp, rp), ConsV (l, r) -> (match bind_pattern lp l with
          None -> None
        | Some lb -> (match bind_pattern rp r with
              None -> None
            | Some rb -> Some (lb @ rb)))
  | _ -> None

let rec eval_exp env = function
...
  | MatchExp (c, bs) ->
    let cond = eval_exp env c in
    (match (List.fold_left (function
        None -> fun (p, b) -> (match bind_pattern p cond with
            None -> None
          | Some bl ->
              let newenv = (List.fold_left (fun env' (i, e) ->
                Environment.extend i e env') env bl) in
              Some (eval_exp newenv b)
        )
      | Some x -> fun _ -> Some x
    ) None bs) with
      None -> err ("No Matched")
    | Some x -> x)
```

## ex3.6.2

以下のような糖衣構文の変換を行う。
```
[1; 2; 3] => 1 :: 2 :: 3 :: []
```

```
  | LSQUARE h=Expr t=list(SEMI e=Expr{e}) RSQUARE {
      List.fold_left (fun l x -> BinOp (Cons, x, l)) Nil (List.rev (h::t)) }
```

## ex3.6.3

次の関数でパターンによる変数束縛に同一の変数名が存在しないことを確認する。
```
let rec check_unique_ids = function
    [] -> true
  | (h,_)::t -> List.for_all (fun (x,_) -> x <> h) t && check_unique_ids t
```

## ex3.6.5

全ての二項演算子の右側でExprを受理するように変更する。
```
choice(X, Y) : x=X { x } | y=Y { y }

ORORExpr :
    l=ORORExpr OROR r=choice(ANDANDExpr,Expr) { IfExp (l, l, r) }
  | e=ANDANDExpr { e }
```
