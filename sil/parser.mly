/*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 */

%{ (* header *)
 
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


%} /* declarations */

/* tokens */

%token AMPER
%token AMPERAMPER
%token BANGEQUAL
%token BAR
%token BARBAR
%token COLON
%token COMMA
%token DLLSEGNE
%token DLLSEGPE
%token DOLLAR
%token DOT
%token END
%token EOF
%token EQUAL
%token EQUALEQUAL
%token EXISTS
%token <string> IDENT
%token <string> QIDENT
%token <string> FIDENT
%token LAM
%token LBRACE
%token LBRACKET
%token LPAREN
%token LSEGNE
%token LSEGPE
%token MINUS
%token <int> NAT
%token PAR
%token PLUS
%token POINTSTO
%token PROP
%token RBRACE
%token RBRACKET
%token RPAREN
%token SEMI
%token STAR
%token <string> UNARYOP

/* precedences (increasing) and associativities for expressions */

/* entry points */

%start proplist_iter
%type <bool * Prop.prop list> proplist_iter

%start proplist
%type <Prop.prop list> proplist

%start prop
%type <Prop.prop> prop

%start hpred
%type <Sil.hpred> hpred

%start strexp
%type <Sil.strexp> strexp

%start atom
%type <Sil.atom> atom

%start exp
%type <Sil.exp> exp

%start ident
%type <Ident.ident> ident


%% /* rules */

/* entry points */

proplist_iter:
  | proplist EOF { (false,$1) }
  | proplist END { (true,$1) }
;

proplist:
  | /* empty */ { [] }
  | PROP NAT COLON prop proplist { $4 :: $5 }
;

prop:
  | prop_elem_seq      { let x,y = $1 in Prop.prop_create_verbatim x y }
;

prop_elem_seq:
  | /* empty */       { ([],[]) }
  | prop_elem_notempty_seq { $1 }
;

prop_elem_notempty_seq:
  | atom { ([$1],[]) }
  | hpred { ([],[$1]) }
  | atom STAR prop_elem_notempty_seq { let x,y = $3 in ($1::x,y) }
  | hpred STAR prop_elem_notempty_seq { let x,y = $3 in (x,$1::y) }
;

hpred_seq:
  | /* empty */ { [] }
  | hpred_notempty_seq  { $1 }
;

hpred_notempty_seq:
  | hpred { [$1] }
  | hpred STAR hpred_notempty_seq { $1::$3 }
;

hpred:
  | exp POINTSTO strexp COLON { Sil.Hpointsto ($1,$3,Sil.Sizeof Sil.Tvoid) }
  | lseg LPAREN hpara RPAREN LPAREN exp COMMA exp COMMA exp_seq RPAREN { Sil.Hlseg ($1,$3,$6,$8,$10) }
  | dllseg LPAREN hpara_dll RPAREN LPAREN exp COMMA exp COMMA exp COMMA exp COMMA exp_seq RPAREN { Sil.Hdllseg ($1,$3,$6,$8,$10,$12,$14) }
;

hpara:
  | LAM para_ex DOT EXISTS LBRACKET ident_seq RBRACKET DOT hpred_seq { let root,next,svars = $2 in {Sil.root=root;Sil.next=next;Sil.svars=svars;Sil.evars=$6;Sil.body=$9} }
;

hpara_dll:
  | LAM para_ex_dll DOT EXISTS LBRACKET ident_seq RBRACKET DOT hpred_seq { let cell,blink,flink,svars_dll = $2 in {Sil.cell=cell;Sil.blink=blink;Sil.flink=flink;Sil.svars_dll=svars_dll;Sil.evars_dll=$6;Sil.body_dll=$9} }
;

para_ex:
  | LBRACKET ident COMMA ident COMMA ident_seq RBRACKET { ($2,$4,$6) }
;

para_ex_dll:
  | LBRACKET ident COMMA ident COMMA ident COMMA ident_seq RBRACKET { ($2,$4,$6,$8) }
;

exp_seq :
  | /* empty */ { [] }
  | exp_notempty_seq { $1 }
;

exp_notempty_seq :
  | exp { [$1] }
  | exp COMMA exp_notempty_seq { $1 :: $3 }
;

lseg:
  | LSEGPE { Sil.Lseg_PE }
  | LSEGNE { Sil.Lseg_NE }
;

dllseg:
  | DLLSEGPE { Sil.Lseg_PE }
  | DLLSEGNE { Sil.Lseg_NE }
;

strexp:
  | exp      { Sil.Eexp $1 }
  | LBRACE fld_exp_seq RBRACE { Sil.Estruct $2 }
  | LBRACKET NAT BAR exp_strexp_seq RBRACKET { Sil.Earray($2,$4) }
;

exp_strexp_seq:
  | /* empty */ { [] }
  | exp_strexp_notempty_seq { $1 }
;

exp_strexp_notempty_seq:
  | exp COLON strexp { [($1,$3)] }
  | exp COLON strexp COMMA exp_strexp_notempty_seq { ($1,$3)::$5 }
;

fld_exp_seq:
  | /* empty */       { [] }
  | fld_exp_notempty_seq { $1 }
;

fld_exp_notempty_seq:
  | IDENT COLON strexp { [(Ident.string_to_name $1,$3)] }
  | IDENT COLON strexp COMMA fld_exp_notempty_seq { (Ident.string_to_name $1,$3)::$5 }
;

atom:
  | exp EQUAL exp { Sil.Aeq ($1,$3) }
  | exp BANGEQUAL exp { Sil.Aneq ($1,$3) }
;

exp:
  | ident            { Sil.Var $1 }
  | NAT              { Sil.Const_int $1 }
  | MINUS NAT        { Sil.Const_int (- $2) }
  | AMPER IDENT DOLLAR IDENT { Sil.Lvar (Sil.mk_pvar (Ident.string_to_name $4) (Cil.emptyFunction $2) "") }
  | exp DOT IDENT    { Sil.Lfield ($1,Ident.string_to_name $3) } 
;

ident_seq:
  | /* empty */ { [] }
  | ident_notempty_seq { $1 }
;

ident_notempty_seq:
  | ident { [$1] }
  | ident COMMA ident_notempty_seq { $1::$3 }
;

ident:
  | IDENT DOLLAR NAT      { Ident.create_normal_ident (Ident.string_to_name $1) $3 }
  | FIDENT DOLLAR NAT      {
      let remove_head s =      
	let n = String.length s in String.sub s 1 (n-1)
      in Ident.create_footprint_ident (Ident.string_to_name (remove_head $1)) $3 }
;


%% (* trailer *)
