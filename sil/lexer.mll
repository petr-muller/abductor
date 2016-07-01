(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

{ (* header *)
  
open Lexing
open Parser

(* association list of keywords *)
let keyword_al = [
  ("dllsegpe",DLLSEGPE);
  ("dllsegne",DLLSEGNE);
  ("end",END);
  ("exists",EXISTS);
  ("lam",LAM);
  ("lsegpe",LSEGPE);
  ("lsegne",LSEGNE);
  ("PROP",PROP);
]

(* To store the position of the beginning of a string and comment *)
let string_start_loc = ref Location.none;;
let comment_start_loc = ref [];;
let in_comment () = !comment_start_loc <> [];;

(* Update the current location with file name and line number. *)
let update_loc lexbuf line absolute chars =
  let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with
	  pos_lnum = if absolute then line else pos.pos_lnum + line;
	  pos_bol = pos.pos_cnum - chars; }

(* Initialize file name and starting position *)
let init lexbuf file =
  Location.lexbuf := Some lexbuf;
  update_loc lexbuf 1 true 0;
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file; };
  lexbuf.lex_start_p <- lexbuf.lex_curr_p

}
(* regular expressions *)

let newline = ('\010' | '\013' | "\013\010")
let blank = [' ' '\009' '\012']
let letter = ['A'-'Z' '_' 'a'-'z']
let digit = ['0'-'9']
let alphanum = digit | letter
let ident = letter alphanum*
let qident = '_' ident
let fident = '@' ident
let num = digit+

(* entry points *)

rule token = parse
  | newline { update_loc lexbuf 1 false 0;
              token lexbuf }
  | blank+ { token lexbuf }
  | "//" [^ '\010' '\013']* newline 
	 { update_loc lexbuf 1 false 0;
           token lexbuf }
  | "/*" { comment_start_loc := [lexbuf.lex_curr_p];
           comment lexbuf;
           token lexbuf }
  | "|->" { POINTSTO }
  | ","  { COMMA }
  | "$"  { DOLLAR }
  | "{"  { LBRACE }
  | "["  { LBRACKET }
  | "("  { LPAREN }
  | "|->" { POINTSTO }
  | "}"  { RBRACE }
  | "]"  { RBRACKET }
  | ")"  { RPAREN }
  | ";"  { SEMI }
  | "&" { AMPER }
  | "&&" { AMPERAMPER }
  | "|" { BAR }
  | "||" { BARBAR }
  | ":"  { COLON } 
  | "="  { EQUAL }
  | "!"                     { UNARYOP(Lexing.lexeme lexbuf) }
  | "==" { EQUALEQUAL}
  | "!=" { BANGEQUAL}
  | "+" { PLUS }
  | "-" { MINUS }
  | "*"     { STAR }
  | "."     { DOT }
  | num { NAT(int_of_string(Lexing.lexeme lexbuf)) }
  | ident { let s = Lexing.lexeme lexbuf in
              try List.assoc s keyword_al
              with Not_found -> IDENT(s) }
  | qident { QIDENT(Lexing.lexeme lexbuf) }
  | fident { FIDENT(Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { raise(Location.Parse_error 
		("Illegal character (" ^ Char.escaped (Lexing.lexeme_char lexbuf 0) ^ ").",
		 Location.mkloc(lexbuf.lex_start_p) (lexbuf.lex_curr_p))) }

and comment = parse
    "/*" { comment_start_loc := lexbuf.lex_curr_p :: !comment_start_loc;
           comment lexbuf; }
  | "*/" { match !comment_start_loc with
             | [] -> assert false
             | [x] -> comment_start_loc := [];
             | _ :: l -> comment_start_loc := l;
                 comment lexbuf; }
  | eof { match !comment_start_loc with
            | [] -> assert false
            | loc :: _ -> comment_start_loc := [];
		raise(Location.Parse_error
			("Unterminated comment.",
			 Location.mkloc loc (lexbuf.lex_curr_p))) }
  | newline { update_loc lexbuf 1 false 0;
              comment lexbuf }
  | _ { comment lexbuf }

{ (* trailer *)
}
