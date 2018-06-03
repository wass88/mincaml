{
let reservedWords = [
  (* Keywords *)
  ("and", Parser.AND);
  ("dfun", Parser.DFUN);
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("fun", Parser.FUN);
  ("if", Parser.IF);
  ("in", Parser.IN);
  ("let", Parser.LET);
  ("match", Parser.MATCH);
  ("rec", Parser.REC);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("with", Parser.WITH);
] 
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "(*" { commentout lexbuf |> ignore; main lexbuf }

| "-"? ['0'-'9']+
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| ";;" { Parser.SEMISEMI }
| "+" { Parser.PLUS }
| "*" { Parser.MULT }
| "::" { Parser.CONS }
| "[]" { Parser.NIL }
| "[" { Parser.LSQUARE }
| "]" { Parser.RSQUARE }
| ";" { Parser.SEMI }
| "<" { Parser.LT }
| "=" { Parser.EQ }
| "&&" { Parser.ANDAND }
| "||" { Parser.OROR }
| "->" { Parser.RARROW }
| "|" { Parser.PIPE }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try 
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| eof { exit 0 }

and commentout = parse
  "(*" { commentout lexbuf |> ignore; commentout lexbuf }
| "*)" { () }
| _ { commentout lexbuf }
