%{
open Syntax

let append_params ps e =
  List.fold_left (fun e p -> FunExp(p, e)) e (List.rev ps)
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MULT LT ANDAND OROR
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ AND
%token RARROW FUN DFUN REC
%token NIL CONS MATCH WITH PIPE
%token LSQUARE SEMI RSQUARE
%token TYPE CORON COMMA

%left PLUS MULT ANDAND OROR
%nonassoc LT

%token <int> INTV
%token <Syntax.id> ID
%token <Syntax.id> TYVAR
%token <Syntax.id> CTOR

%start toplevel
%type <Syntax.program list> toplevel
%%

toplevel :
    d=Decl* SEMISEMI { d }
  | LET REC x=ID EQ FUN p=ID RARROW e=Expr SEMISEMI { [RecDecl (x, p, e)] }
  | e=Expr SEMISEMI { [Exp e] }
  | TYPE x=ID EQ h=GadtBranch br=list(PIPE b=GadtBranch { b }) SEMISEMI { [Gadt (x, h::br)] }

Decl :
    LET b=LetBody t=list(AND l=LetBody {l}) { Decl (b::t) }

LetBody :
    x=ID ps=ID* EQ e1=Expr { (x, append_params ps e1) }

Expr :
    e=IfExpr { e }
  | e=MatchExpr { e }
  | e=ORORExpr { e }
  | e=LetExpr { e }
  | e=LetRecExpr { e }
  | e=FunExpr { e }
  | e=DFunExpr { e }

choice(X, Y) : x=X { x } | y=Y { y }

ORORExpr :
    l=ORORExpr OROR r=choice(ANDANDExpr,Expr) { IfExp (l, l, r) }
  | e=ANDANDExpr { e }

ANDANDExpr :
    l=ANDANDExpr ANDAND r=choice(LTExpr,Expr) { IfExp (l, r, l) }
  | e=LTExpr { e }

LTExpr :
    l=PExpr LT r=choice(PExpr,Expr) { BinOp (Lt, l, r) }
  | e=CONSExpr { e }

CONSExpr :
    l=PExpr CONS r=choice(CONSExpr,Expr) { BinOp (Cons, l, r) }
  | e=PExpr { e }

PExpr :
    l=PExpr PLUS r=choice(MExpr,Expr) { BinOp (Plus, l, r) }
  | e=MExpr { e }

MExpr :
    l=MExpr MULT r=choice(AppExpr,Expr) { BinOp (Mult, l, r) }
  | e=AppExpr { e }

AppExpr :
    f=AppExpr x=AExpr { AppExp (f, x) }
  | x=AExpr { x }

AExpr :
    i=INTV { ILit i }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | NIL    { Nil }
  | i=ID   { Var i }
  | i=CTOR { Var i }
  | LPAREN e=Expr RPAREN { e }
  | LPAREN o=BinOP RPAREN {
    FunExp(dummy_id 0, FunExp(dummy_id 1,
      BinOp(o, Var (dummy_id 0), Var (dummy_id 1)))) }
  | LPAREN ANDAND RPAREN {
    FunExp(dummy_id 0, FunExp(dummy_id 1,
      IfExp(Var (dummy_id 0), Var (dummy_id 1), Var (dummy_id 0)))) }
  | LPAREN OROR RPAREN {
    FunExp(dummy_id 0, FunExp(dummy_id 1,
      IfExp(Var (dummy_id 0), Var (dummy_id 0), Var (dummy_id 1)))) }
  | LSQUARE h=Expr t=list(SEMI e=Expr{e}) RSQUARE {
      List.fold_left (fun l x -> BinOp (Cons, x, l)) Nil (List.rev (h::t)) }
  | LPAREN RPAREN { TupleExp [] }
  | LPAREN h1=Expr COMMA h2=Expr t=list(COMMA e=Expr{e}) RPAREN { TupleExp (h1::h2::t) }

BinOP :
    PLUS { Plus }
  | MULT { Mult }
  | LT { Lt }

MatchExpr :
    MATCH c=Expr WITH pat=Branch pats=list(PIPE b=Branch { b })
      {MatchExp (c, pat::pats) }

Branch :
    p=Pattern RARROW e=Expr { (p, e) }

Pattern :
    x=ID { VarP x }
  | NIL { NilP }
  | l=Pattern CONS r=Pattern { ConsP (l, r) }
  | LPAREN RPAREN { TupleP [] }
  | LPAREN h1=Pattern COMMA h2=Pattern t=list(COMMA p=Pattern{p}) RPAREN { TupleP (h1::h2::t) }
  | x=CTOR { GadtP (x, None) }
  | x=CTOR p=Pattern { GadtP (x, Some p) }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

LetExpr :
    LET b=LetBody t=list(AND l=LetBody {l}) IN e2=Expr { LetExp (b::t, e2) }

LetRecExpr :
    LET REC x=ID EQ FUN p=ID RARROW e1=Expr IN e2=Expr { LetRecExp (x, p, e1, e2) }

FunExpr :
    FUN ps=ID+ RARROW e=Expr { append_params ps e }

DFunExpr :
    DFUN x=ID RARROW e=Expr { DFunExp (x, e) }

TypeAtom :
    t=ID { TySyntaxName t }
  | tv=TYVAR { TySyntaxVar tv }
  | t=TypeAtom g=ID { TySyntaxGadt (t, g) }
  | LPAREN t=Type RPAREN { t }

Type :
    td=TypeAtom RARROW tc=Type { TySyntaxFun (td, tc) }
  | h=TypeAtom t=list(MULT a=TypeAtom {a}) { TySyntaxTuple (h :: t) }
    
GadtBranch :
    x=CTOR CORON f=TypeAtom y=ID { GadtLeaf (x, f, y) }
  | x=CTOR CORON c=TypeAtom RARROW f=TypeAtom y=ID { GadtBranch (x, c, f, y) }