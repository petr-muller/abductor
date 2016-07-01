type token =
  | AMPER
  | AMPERAMPER
  | BANGEQUAL
  | BAR
  | BARBAR
  | COLON
  | COMMA
  | DLLSEGNE
  | DLLSEGPE
  | DOLLAR
  | DOT
  | END
  | EOF
  | EQUAL
  | EQUALEQUAL
  | EXISTS
  | IDENT of (string)
  | QIDENT of (string)
  | FIDENT of (string)
  | LAM
  | LBRACE
  | LBRACKET
  | LPAREN
  | LSEGNE
  | LSEGPE
  | MINUS
  | NAT of (int)
  | PAR
  | PLUS
  | POINTSTO
  | PROP
  | RBRACE
  | RBRACKET
  | RPAREN
  | SEMI
  | STAR
  | UNARYOP of (string)

val proplist_iter :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> bool * Prop.prop list
val proplist :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Prop.prop list
val prop :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Prop.prop
val hpred :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Sil.hpred
val strexp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Sil.strexp
val atom :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Sil.atom
val exp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Sil.exp
val ident :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ident.ident
