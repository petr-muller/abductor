module F = Format
open Lexing

type t_record = {file: string; line: int; eline: int; start_char: int; end_char: int}
type t = t_record option

exception Parse_error of string * t

let none : t = None

let mkloc s e =
  Some{file = e.pos_fname; (* s.pos_fname might not be set *)
       line = s.pos_lnum;
       eline = e.pos_lnum;
       start_char = s.pos_cnum - s.pos_bol;
       end_char = e.pos_cnum - e.pos_bol}
    (* for end_char, subtracting e and s is intentional, to handle
       multiline locations *)

let symbol_loc () = mkloc (Parsing.symbol_start_pos()) (Parsing.symbol_end_pos())
let rhs_loc n = mkloc (Parsing.rhs_start_pos n) (Parsing.rhs_end_pos n)


let sprint loc = match loc with
  | Some{file=f; line=l; eline=l'; start_char=s; end_char=e} ->
      if l=l' then 
	F.sprintf "File \"%s\", line %i, characters %i-%i:@." f l s e
      else 
	F.sprintf "File \"%s\", lines %i-%i, characters %i-%i:@." f l l' s e
  | None -> ""

let print fmt loc = F.pp_print_string fmt (sprint loc)

let lexbuf : Lexing.lexbuf option ref = ref None
