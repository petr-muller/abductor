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

open Parsing;;
# 11 "parser.mly"
 (* header *)
 
(* implicitly called when no grammar rules apply *)
let parse_error _ =
  raise(
    Location.Parse_error("Syntax error.",
      match !Location.lexbuf with
	| None -> Location.symbol_loc()
	| Some lexbuf ->
	    (* the Parsing library only updates symbol_end_pos when successfully
	     * reducing a grammar rule, so here we ask the lexer for the current
	     * position directly *)
	    Location.mkloc (Parsing.symbol_start_pos()) lexbuf.Lexing.lex_curr_p))

let locUnknown = { Cil.line = -1; 
		   Cil.file = ""; 
		   Cil.byte = -1;}

let makeVarinfo global name typ =
  let vi = 
    { Cil.vname = name;
      Cil.vid   = 0;
      Cil.vglob = global;
      Cil.vtype = typ;
      Cil.vdecl = locUnknown;
      Cil.vinline = false;
      Cil.vattr = [];
      Cil.vstorage = Cil.NoStorage;
      Cil.vaddrof = false;
      Cil.vreferenced = false;
    } in
  vi

let makeGlobalVar name typ =
  let vi = makeVarinfo true name typ in
  vi

let mkBlock slst = 
  { Cil.battrs = []; Cil.bstmts = slst; }

let voidType = Cil.TVoid([])

let emptyFunction name = 
  { Cil.svar  = makeGlobalVar name (Cil.TFun(voidType, Some [], false,[]));
    Cil.smaxid = 0;
    Cil.slocals = [];
    Cil.sformals = [];
    Cil.sbody = mkBlock [];
    Cil.smaxstmtid = None;
    Cil.sallstmts = [];
  }

# 95 "parser.ml"
let yytransl_const = [|
  257 (* AMPER *);
  258 (* AMPERAMPER *);
  259 (* BANGEQUAL *);
  260 (* BAR *);
  261 (* BARBAR *);
  262 (* COLON *);
  263 (* COMMA *);
  264 (* DLLSEGNE *);
  265 (* DLLSEGPE *);
  266 (* DOLLAR *);
  267 (* DOT *);
  268 (* END *);
    0 (* EOF *);
  269 (* EQUAL *);
  270 (* EQUALEQUAL *);
  271 (* EXISTS *);
  275 (* LAM *);
  276 (* LBRACE *);
  277 (* LBRACKET *);
  278 (* LPAREN *);
  279 (* LSEGNE *);
  280 (* LSEGPE *);
  281 (* MINUS *);
  283 (* PAR *);
  284 (* PLUS *);
  285 (* POINTSTO *);
  286 (* PROP *);
  287 (* RBRACE *);
  288 (* RBRACKET *);
  289 (* RPAREN *);
  290 (* SEMI *);
  291 (* STAR *);
    0|]

let yytransl_block = [|
  272 (* IDENT *);
  273 (* QIDENT *);
  274 (* FIDENT *);
  282 (* NAT *);
  292 (* UNARYOP *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\003\000\009\000\009\000\010\000\
\010\000\010\000\010\000\011\000\011\000\012\000\012\000\004\000\
\004\000\004\000\014\000\017\000\018\000\020\000\015\000\015\000\
\021\000\021\000\013\000\013\000\016\000\016\000\005\000\005\000\
\005\000\023\000\023\000\024\000\024\000\022\000\022\000\025\000\
\025\000\006\000\006\000\007\000\007\000\007\000\007\000\007\000\
\019\000\019\000\026\000\026\000\008\000\008\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yylen = "\002\000\
\002\000\002\000\000\000\005\000\001\000\000\000\001\000\001\000\
\001\000\003\000\003\000\000\000\001\000\001\000\003\000\004\000\
\011\000\015\000\009\000\009\000\007\000\009\000\000\000\001\000\
\001\000\003\000\001\000\001\000\001\000\001\000\001\000\003\000\
\005\000\000\000\001\000\003\000\005\000\000\000\001\000\003\000\
\005\000\003\000\003\000\001\000\001\000\002\000\004\000\003\000\
\000\000\001\000\001\000\003\000\003\000\003\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\055\000\000\000\056\000\000\000\030\000\029\000\
\000\000\000\000\028\000\027\000\000\000\045\000\057\000\000\000\
\000\000\000\000\044\000\005\000\007\000\000\000\000\000\058\000\
\000\000\000\000\000\000\059\000\000\000\060\000\000\000\000\000\
\062\000\000\000\002\000\001\000\000\000\000\000\000\000\046\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\039\000\000\000\000\000\000\000\053\000\054\000\
\011\000\010\000\000\000\048\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\032\000\000\000\000\000\047\000\016\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\035\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\
\000\000\000\000\041\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\050\000\000\000\
\000\000\000\000\000\000\037\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\021\000\052\000\000\000\000\000\000\000\
\024\000\000\000\000\000\000\000\000\000\019\000\013\000\000\000\
\017\000\000\000\020\000\000\000\000\000\026\000\022\000\000\000\
\015\000\000\000\000\000\018\000"

let yydgoto = "\009\000\
\011\000\012\000\023\000\024\000\036\000\025\000\026\000\027\000\
\028\000\029\000\142\000\143\000\030\000\072\000\136\000\031\000\
\074\000\082\000\118\000\085\000\137\000\058\000\089\000\090\000\
\059\000\119\000"

let yysindex = "\084\000\
\253\254\253\254\021\255\021\255\047\255\053\255\053\255\016\255\
\000\000\002\255\000\000\005\000\000\000\024\255\000\000\000\000\
\040\255\049\255\000\000\000\000\031\255\000\000\000\000\029\255\
\039\255\013\255\000\000\000\000\000\000\073\255\074\255\000\000\
\012\255\083\255\076\255\000\000\064\255\000\000\022\255\064\255\
\000\000\099\255\000\000\000\000\097\255\082\255\084\255\000\000\
\021\255\021\255\053\255\095\255\053\255\047\255\094\255\098\255\
\108\255\085\255\000\000\115\255\021\255\107\255\000\000\000\000\
\000\000\000\000\064\255\000\000\064\255\118\255\105\255\096\255\
\106\255\100\255\047\255\000\000\053\255\253\254\000\000\000\000\
\016\255\117\255\109\255\016\255\119\255\110\255\127\255\025\255\
\104\255\000\000\000\000\132\255\125\255\053\255\135\255\128\255\
\053\255\083\255\047\255\000\000\016\255\123\255\042\255\016\255\
\126\255\044\255\000\000\141\255\142\255\016\255\053\255\145\255\
\016\255\053\255\053\255\016\255\146\255\122\255\000\000\045\255\
\016\255\130\255\059\255\000\000\131\255\016\255\147\255\053\255\
\150\255\148\255\053\255\000\000\000\000\021\255\070\255\133\255\
\000\000\016\255\021\255\086\255\129\255\000\000\000\000\053\255\
\000\000\136\255\000\000\053\255\021\255\000\000\000\000\087\255\
\000\000\053\255\134\255\000\000"

let yyrindex = "\000\000\
\006\000\165\000\169\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\008\000\
\009\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\139\255\000\000\000\000\003\000\000\000\000\000\171\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\010\000\000\000\000\000\000\000\
\000\000\000\000\001\000\000\000\002\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\140\255\004\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\143\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\144\255\000\000\149\255\000\000\000\000\
\149\255\000\000\000\000\149\255\151\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\152\255\
\000\000\000\000\000\000\000\000\000\000\153\255\154\255\000\000\
\000\000\149\255\153\255\000\000\155\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\152\255\000\000\000\000"

let yygindex = "\000\000\
\000\000\254\255\112\000\011\000\219\255\172\000\007\000\255\255\
\000\000\226\255\036\000\028\000\000\000\000\000\025\000\000\000\
\000\000\000\000\161\255\000\000\038\000\000\000\000\000\065\000\
\086\000\063\000"

let yytablesize = 296
let yytable = "\013\000\
\043\000\042\000\031\000\003\000\044\000\003\000\041\000\009\000\
\008\000\006\000\033\000\037\000\039\000\040\000\032\000\051\000\
\070\000\122\000\065\000\066\000\125\000\014\000\052\000\052\000\
\051\000\053\000\010\000\042\000\015\000\016\000\099\000\017\000\
\052\000\018\000\053\000\052\000\017\000\087\000\018\000\045\000\
\054\000\054\000\146\000\019\000\020\000\021\000\022\000\014\000\
\111\000\046\000\114\000\128\000\052\000\014\000\052\000\052\000\
\048\000\067\000\047\000\069\000\037\000\108\000\017\000\049\000\
\018\000\131\000\034\000\035\000\017\000\052\000\018\000\021\000\
\022\000\050\000\052\000\091\000\144\000\021\000\022\000\092\000\
\052\000\037\000\095\000\088\000\001\000\002\000\003\000\004\000\
\005\000\006\000\007\000\008\000\148\000\154\000\055\000\056\000\
\052\000\052\000\057\000\109\000\103\000\060\000\112\000\106\000\
\061\000\037\000\062\000\063\000\117\000\064\000\068\000\117\000\
\071\000\075\000\117\000\076\000\073\000\120\000\077\000\129\000\
\123\000\088\000\079\000\080\000\117\000\081\000\084\000\093\000\
\083\000\096\000\094\000\097\000\086\000\098\000\135\000\100\000\
\117\000\140\000\101\000\102\000\033\000\104\000\105\000\110\000\
\141\000\033\000\113\000\115\000\116\000\141\000\135\000\121\000\
\126\000\127\000\152\000\033\000\138\000\134\000\139\000\141\000\
\135\000\130\000\132\000\149\000\003\000\145\000\156\000\151\000\
\006\000\038\000\061\000\034\000\078\000\040\000\147\000\036\000\
\153\000\038\000\155\000\124\000\049\000\150\000\051\000\107\000\
\023\000\012\000\025\000\014\000\133\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\031\000\031\000\000\000\000\000\043\000\042\000\000\000\003\000\
\043\000\003\000\000\000\009\000\008\000\006\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\043\000\042\000\
\000\000\031\000\031\000\043\000\042\000\009\000\008\000\006\000"

let yycheck = "\002\000\
\000\000\000\000\000\000\000\000\000\000\000\000\008\000\000\000\
\000\000\000\000\004\000\005\000\006\000\007\000\004\000\003\001\
\054\000\113\000\049\000\050\000\116\000\001\001\011\001\011\001\
\003\001\013\001\030\001\026\001\008\001\009\001\006\001\016\001\
\011\001\018\001\013\001\011\001\016\001\075\000\018\001\016\001\
\029\001\029\001\138\000\023\001\024\001\025\001\026\001\001\001\
\007\001\010\001\007\001\007\001\011\001\001\001\011\001\011\001\
\026\001\051\000\010\001\053\000\054\000\099\000\016\001\035\001\
\018\001\007\001\020\001\021\001\016\001\011\001\018\001\025\001\
\026\001\035\001\011\001\078\000\007\001\025\001\026\001\081\000\
\011\001\075\000\084\000\077\000\001\000\002\000\003\000\004\000\
\005\000\006\000\007\000\008\000\007\001\007\001\022\001\022\001\
\011\001\011\001\016\001\101\000\094\000\026\001\104\000\097\000\
\006\001\099\000\010\001\026\001\110\000\026\001\016\001\113\000\
\019\001\006\001\116\000\031\001\019\001\111\000\004\001\121\000\
\114\000\115\000\016\001\006\001\126\000\021\001\021\001\011\001\
\033\001\011\001\022\001\022\001\033\001\007\001\128\000\032\001\
\138\000\131\000\007\001\015\001\134\000\007\001\015\001\021\001\
\134\000\139\000\021\001\007\001\007\001\139\000\144\000\007\001\
\007\001\032\001\148\000\149\000\007\001\011\001\011\001\149\000\
\154\000\032\001\032\001\035\001\000\000\033\001\033\001\032\001\
\000\000\031\001\000\000\032\001\061\000\031\001\139\000\032\001\
\149\000\006\000\154\000\115\000\032\001\144\000\032\001\098\000\
\033\001\033\001\033\001\033\001\126\000\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\006\001\007\001\255\255\255\255\012\001\012\001\255\255\012\001\
\012\001\012\001\255\255\012\001\012\001\012\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\030\001\030\001\
\255\255\031\001\032\001\035\001\035\001\030\001\030\001\030\001"

let yynames_const = "\
  AMPER\000\
  AMPERAMPER\000\
  BANGEQUAL\000\
  BAR\000\
  BARBAR\000\
  COLON\000\
  COMMA\000\
  DLLSEGNE\000\
  DLLSEGPE\000\
  DOLLAR\000\
  DOT\000\
  END\000\
  EOF\000\
  EQUAL\000\
  EQUALEQUAL\000\
  EXISTS\000\
  LAM\000\
  LBRACE\000\
  LBRACKET\000\
  LPAREN\000\
  LSEGNE\000\
  LSEGPE\000\
  MINUS\000\
  PAR\000\
  PLUS\000\
  POINTSTO\000\
  PROP\000\
  RBRACE\000\
  RBRACKET\000\
  RPAREN\000\
  SEMI\000\
  STAR\000\
  "

let yynames_block = "\
  IDENT\000\
  QIDENT\000\
  FIDENT\000\
  NAT\000\
  UNARYOP\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Prop.prop list) in
    Obj.repr(
# 139 "parser.mly"
                 ( (false,_1) )
# 366 "parser.ml"
               : bool * Prop.prop list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Prop.prop list) in
    Obj.repr(
# 140 "parser.mly"
                 ( (true,_1) )
# 373 "parser.ml"
               : bool * Prop.prop list))
; (fun __caml_parser_env ->
    Obj.repr(
# 144 "parser.mly"
                ( [] )
# 379 "parser.ml"
               : Prop.prop list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Prop.prop) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Prop.prop list) in
    Obj.repr(
# 145 "parser.mly"
                                 ( _4 :: _5 )
# 388 "parser.ml"
               : Prop.prop list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prop_elem_seq) in
    Obj.repr(
# 149 "parser.mly"
                       ( let x,y = _1 in Prop.prop_create_verbatim x y )
# 395 "parser.ml"
               : Prop.prop))
; (fun __caml_parser_env ->
    Obj.repr(
# 153 "parser.mly"
                      ( ([],[]) )
# 401 "parser.ml"
               : 'prop_elem_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prop_elem_notempty_seq) in
    Obj.repr(
# 154 "parser.mly"
                           ( _1 )
# 408 "parser.ml"
               : 'prop_elem_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Sil.atom) in
    Obj.repr(
# 158 "parser.mly"
         ( ([_1],[]) )
# 415 "parser.ml"
               : 'prop_elem_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Sil.hpred) in
    Obj.repr(
# 159 "parser.mly"
          ( ([],[_1]) )
# 422 "parser.ml"
               : 'prop_elem_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_elem_notempty_seq) in
    Obj.repr(
# 160 "parser.mly"
                                     ( let x,y = _3 in (_1::x,y) )
# 430 "parser.ml"
               : 'prop_elem_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.hpred) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_elem_notempty_seq) in
    Obj.repr(
# 161 "parser.mly"
                                      ( let x,y = _3 in (x,_1::y) )
# 438 "parser.ml"
               : 'prop_elem_notempty_seq))
; (fun __caml_parser_env ->
    Obj.repr(
# 165 "parser.mly"
                ( [] )
# 444 "parser.ml"
               : 'hpred_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'hpred_notempty_seq) in
    Obj.repr(
# 166 "parser.mly"
                        ( _1 )
# 451 "parser.ml"
               : 'hpred_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Sil.hpred) in
    Obj.repr(
# 170 "parser.mly"
          ( [_1] )
# 458 "parser.ml"
               : 'hpred_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.hpred) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'hpred_notempty_seq) in
    Obj.repr(
# 171 "parser.mly"
                                  ( _1::_3 )
# 466 "parser.ml"
               : 'hpred_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Sil.strexp) in
    Obj.repr(
# 175 "parser.mly"
                              ( Sil.Hpointsto (_1,_3,Sil.Tvoid) )
# 474 "parser.ml"
               : Sil.hpred))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 10 : 'lseg) in
    let _3 = (Parsing.peek_val __caml_parser_env 8 : 'hpara) in
    let _6 = (Parsing.peek_val __caml_parser_env 5 : Sil.exp) in
    let _8 = (Parsing.peek_val __caml_parser_env 3 : Sil.exp) in
    let _10 = (Parsing.peek_val __caml_parser_env 1 : 'exp_seq) in
    Obj.repr(
# 176 "parser.mly"
                                                                       ( Sil.Hlseg (_1,_3,_6,_8,_10) )
# 485 "parser.ml"
               : Sil.hpred))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 14 : 'dllseg) in
    let _3 = (Parsing.peek_val __caml_parser_env 12 : 'hpara_dll) in
    let _6 = (Parsing.peek_val __caml_parser_env 9 : Sil.exp) in
    let _8 = (Parsing.peek_val __caml_parser_env 7 : Sil.exp) in
    let _10 = (Parsing.peek_val __caml_parser_env 5 : Sil.exp) in
    let _12 = (Parsing.peek_val __caml_parser_env 3 : Sil.exp) in
    let _14 = (Parsing.peek_val __caml_parser_env 1 : 'exp_seq) in
    Obj.repr(
# 177 "parser.mly"
                                                                                                 ( Sil.Hdllseg (_1,_3,_6,_8,_10,_12,_14) )
# 498 "parser.ml"
               : Sil.hpred))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'para_ex) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'ident_seq) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'hpred_seq) in
    Obj.repr(
# 181 "parser.mly"
                                                                     ( let root,next,svars = _2 in {Sil.root=root;Sil.next=next;Sil.svars=svars;Sil.evars=_6;Sil.body=_9} )
# 507 "parser.ml"
               : 'hpara))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'para_ex_dll) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'ident_seq) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'hpred_seq) in
    Obj.repr(
# 185 "parser.mly"
                                                                         ( let cell,blink,flink,svars_dll = _2 in {Sil.cell=cell;Sil.blink=blink;Sil.flink=flink;Sil.svars_dll=svars_dll;Sil.evars_dll=_6;Sil.body_dll=_9} )
# 516 "parser.ml"
               : 'hpara_dll))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ident.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : Ident.ident) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'ident_seq) in
    Obj.repr(
# 189 "parser.mly"
                                                        ( (_2,_4,_6) )
# 525 "parser.ml"
               : 'para_ex))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : Ident.ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : Ident.ident) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : Ident.ident) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'ident_seq) in
    Obj.repr(
# 193 "parser.mly"
                                                                    ( (_2,_4,_6,_8) )
# 535 "parser.ml"
               : 'para_ex_dll))
; (fun __caml_parser_env ->
    Obj.repr(
# 197 "parser.mly"
                ( [] )
# 541 "parser.ml"
               : 'exp_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exp_notempty_seq) in
    Obj.repr(
# 198 "parser.mly"
                     ( _1 )
# 548 "parser.ml"
               : 'exp_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Sil.exp) in
    Obj.repr(
# 202 "parser.mly"
        ( [_1] )
# 555 "parser.ml"
               : 'exp_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp_notempty_seq) in
    Obj.repr(
# 203 "parser.mly"
                               ( _1 :: _3 )
# 563 "parser.ml"
               : 'exp_notempty_seq))
; (fun __caml_parser_env ->
    Obj.repr(
# 207 "parser.mly"
           ( Sil.Lseg_PE )
# 569 "parser.ml"
               : 'lseg))
; (fun __caml_parser_env ->
    Obj.repr(
# 208 "parser.mly"
           ( Sil.Lseg_NE )
# 575 "parser.ml"
               : 'lseg))
; (fun __caml_parser_env ->
    Obj.repr(
# 212 "parser.mly"
             ( Sil.Lseg_PE )
# 581 "parser.ml"
               : 'dllseg))
; (fun __caml_parser_env ->
    Obj.repr(
# 213 "parser.mly"
             ( Sil.Lseg_NE )
# 587 "parser.ml"
               : 'dllseg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Sil.exp) in
    Obj.repr(
# 217 "parser.mly"
             ( Sil.Eexp _1 )
# 594 "parser.ml"
               : Sil.strexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'fld_exp_seq) in
    Obj.repr(
# 218 "parser.mly"
                              ( Sil.Estruct _2 )
# 601 "parser.ml"
               : Sil.strexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'exp_strexp_seq) in
    Obj.repr(
# 219 "parser.mly"
                                             ( Sil.Earray(_2,_4) )
# 609 "parser.ml"
               : Sil.strexp))
; (fun __caml_parser_env ->
    Obj.repr(
# 223 "parser.mly"
                ( [] )
# 615 "parser.ml"
               : 'exp_strexp_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exp_strexp_notempty_seq) in
    Obj.repr(
# 224 "parser.mly"
                            ( _1 )
# 622 "parser.ml"
               : 'exp_strexp_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Sil.strexp) in
    Obj.repr(
# 228 "parser.mly"
                     ( [(_1,_3)] )
# 630 "parser.ml"
               : 'exp_strexp_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Sil.strexp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'exp_strexp_notempty_seq) in
    Obj.repr(
# 229 "parser.mly"
                                                   ( (_1,_3)::_5 )
# 639 "parser.ml"
               : 'exp_strexp_notempty_seq))
; (fun __caml_parser_env ->
    Obj.repr(
# 233 "parser.mly"
                      ( [] )
# 645 "parser.ml"
               : 'fld_exp_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fld_exp_notempty_seq) in
    Obj.repr(
# 234 "parser.mly"
                         ( _1 )
# 652 "parser.ml"
               : 'fld_exp_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Sil.strexp) in
    Obj.repr(
# 238 "parser.mly"
                       ( [(Ident.string_to_name _1,_3)] )
# 660 "parser.ml"
               : 'fld_exp_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Sil.strexp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'fld_exp_notempty_seq) in
    Obj.repr(
# 239 "parser.mly"
                                                  ( (Ident.string_to_name _1,_3)::_5 )
# 669 "parser.ml"
               : 'fld_exp_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Sil.exp) in
    Obj.repr(
# 243 "parser.mly"
                  ( Sil.Aeq (_1,_3) )
# 677 "parser.ml"
               : Sil.atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Sil.exp) in
    Obj.repr(
# 244 "parser.mly"
                      ( Sil.Aneq (_1,_3) )
# 685 "parser.ml"
               : Sil.atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ident.ident) in
    Obj.repr(
# 248 "parser.mly"
                     ( Sil.Var _1 )
# 692 "parser.ml"
               : Sil.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 249 "parser.mly"
                     ( Sil.Const_int _1 )
# 699 "parser.ml"
               : Sil.exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 250 "parser.mly"
                     ( Sil.Const_int (- _2) )
# 706 "parser.ml"
               : Sil.exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 251 "parser.mly"
                             ( Sil.Lvar (Sil.mk_pvar (Ident.string_to_name _4) (emptyFunction _2)) )
# 714 "parser.ml"
               : Sil.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Sil.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 252 "parser.mly"
                     ( Sil.Lfield (_1,Ident.string_to_name _3) )
# 722 "parser.ml"
               : Sil.exp))
; (fun __caml_parser_env ->
    Obj.repr(
# 256 "parser.mly"
                ( [] )
# 728 "parser.ml"
               : 'ident_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ident_notempty_seq) in
    Obj.repr(
# 257 "parser.mly"
                       ( _1 )
# 735 "parser.ml"
               : 'ident_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ident.ident) in
    Obj.repr(
# 261 "parser.mly"
          ( [_1] )
# 742 "parser.ml"
               : 'ident_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ident.ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ident_notempty_seq) in
    Obj.repr(
# 262 "parser.mly"
                                   ( _1::_3 )
# 750 "parser.ml"
               : 'ident_notempty_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 266 "parser.mly"
                          ( Ident.create_normal_ident (Ident.string_to_name _1) _3 )
# 758 "parser.ml"
               : Ident.ident))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 267 "parser.mly"
                           (
      let remove_head s =      
	let n = String.length s in String.sub s 1 (n-1)
      in Ident.create_footprint_ident (Ident.string_to_name (remove_head _1)) _3 )
# 769 "parser.ml"
               : Ident.ident))
(* Entry proplist_iter *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry proplist *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry prop *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry hpred *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry strexp *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry atom *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry exp *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry ident *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let proplist_iter (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : bool * Prop.prop list)
let proplist (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : Prop.prop list)
let prop (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 3 lexfun lexbuf : Prop.prop)
let hpred (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 4 lexfun lexbuf : Sil.hpred)
let strexp (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 5 lexfun lexbuf : Sil.strexp)
let atom (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 6 lexfun lexbuf : Sil.atom)
let exp (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 7 lexfun lexbuf : Sil.exp)
let ident (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 8 lexfun lexbuf : Ident.ident)
;;
# 274 "parser.mly"
 (* trailer *)
# 824 "parser.ml"
