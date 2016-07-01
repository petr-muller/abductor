(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

module F = Format

type colour =
    C30 | C31 | C32 | C33 | C34 | C35 | C36

let black = C30
let red = C31
let green = C32
let yellow = C33
let blue = C34
let magenta = C35
let cyan = C36

let next_c = function
  | C30 -> assert false
  | C31 -> C32
  | C32 -> C33
  | C33 -> C34
  | C34 -> C35
  | C35 -> C36
  | C36 -> C31

let current_thread_colour = ref C31

let next_colour () =
  let c = !current_thread_colour in
  let () = current_thread_colour := next_c c
  in c

let _set_print_colour fmt c = match c with
  | C30 -> F.fprintf fmt "\027[30m"
  | C31 -> F.fprintf fmt "\027[31m"
  | C32 -> F.fprintf fmt "\027[32m"
  | C33 -> F.fprintf fmt "\027[33m"
  | C34 -> F.fprintf fmt "\027[34m"
  | C35 -> F.fprintf fmt "\027[35m"
  | C36 -> F.fprintf fmt "\027[36m"

let change_terminal_colour c = _set_print_colour F.std_formatter c
let change_terminal_colour_stderr c = _set_print_colour F.err_formatter c

(** Can be applied to any number of arguments and throws them all away *)
let rec throw_away x = Obj.magic throw_away

type mode = DEFAULT | ALWAYS | NEVER

let use_colours = ref false

(* =============== START of module DB =============== *)
module DB : sig
  val init : unit -> unit (** Initialize the datbase file *)
  type path = string list
  val relative_path : path -> string
  val absolute_path : path -> string
  val create : path ->  Unix.file_descr
end = struct
let create_dir dir =
  try
    let stats = Unix.stat dir
    in if stats.Unix.st_kind != Unix.S_DIR then
      (F.fprintf F.err_formatter "@.ERROR: file %s exists and is not a directory@." dir;
       assert false)
  with Unix.Unix_error _ ->
    (try Unix.mkdir dir 0o700 with
	Unix.Unix_error _ ->
	  (F.fprintf F.err_formatter "@.ERROR: cannot create directory %s@." dir;
	   assert false))

let curr_filename_base () =
  Filename.concat !Config.db_dir (Filename.basename !Config.curr_filename)

type path = string list

let path_from_base base path =
  let rec f = function
    | [] -> base
    | name::names ->
	Filename.concat (f names) (if name==".." then Filename.parent_dir_name else name)
  in f (List.rev path)

let relative_path path =
  path_from_base Filename.current_dir_name path

let absolute_path path =
  let base = curr_filename_base ()
  in path_from_base base path

let init () =
  let cilhome = Sys.getenv "CILHOME" in
  let artwork = Filename.concat (Filename.concat cilhome Filename.parent_dir_name) "artwork" in
  let background = Filename.concat artwork Config.abd_background in
  let copy_comm = "cp " ^ background ^ " " ^ !Config.db_dir
  in
    create_dir !Config.db_dir;
    create_dir (absolute_path []);
    create_dir (absolute_path ["..";"specs"]);
    ignore (Sys.command copy_comm)

let create path =
  let rec f = function
    | [] ->
	let new_path = absolute_path [] in
	let () = create_dir new_path
	in new_path
    | name::names ->
	let new_path = Filename.concat (f names) name in
	let () = create_dir new_path
	in new_path in
  let filename,dir_path = match List.rev path with
    | filename::dir_path -> filename,dir_path
    | [] -> raise (Failure "create_path") in
  let full_fname = Filename.concat (f dir_path) filename
  in Unix.openfile full_fname [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC] 0o777
end
(* =============== END of module DB =============== *)

(* =============== START of module Html =============== *)
module Html : sig
  val create : ?with_background:bool -> DB.path -> Unix.file_descr * F.formatter
  val open_out : DB.path -> Unix.file_descr * F.formatter
  val close : Unix.file_descr * F.formatter -> unit
  val pp_hline : F.formatter -> unit -> unit (** Print a horizontal line *)
  val pp_start_listing : F.formatter -> unit -> unit (** Print start listing *)
  val pp_end_listing : F.formatter -> unit -> unit (** Print end listing *)
  val pp_node_link : DB.path -> string -> F.formatter -> int -> unit (** Print an html link to the given node *)
  val pp_proc_link : DB.path -> string -> F.formatter -> string -> unit (** Print an html link to the given proc *)
  val pp_line_link : ?with_name:bool -> ?text:(string option) -> DB.path -> F.formatter -> int -> unit (** Print an html link to the given line number of the current source file *)
  val pp_session_link : ?with_name:bool -> string list -> F.formatter -> int * int * int -> unit (** Print an html link given node id and session *)
end = struct
let create ?(with_background=true) path =
  let fname,dir_path = match List.rev path with
    | fname::dir_path -> fname,dir_path
    | [] -> raise (Failure "Html.create") in
  let fd = DB.create (List.rev ((fname ^ ".html") :: dir_path)) in
  let outc = Unix.out_channel_of_descr fd in
  let fmt = F.formatter_of_out_channel outc in
  let background = DB.absolute_path ["..";Config.abd_background] in
  let (++) x y = x ^ "\n" ^ y in
  let s =
    "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">" ++
      "<html>\n<head>\n<title>" ^ fname ^ "</title>" ++
      "<style type=\"text/css\">" ++
      "body { color:#000000; background-color:#ffffff }" ++
      "body { font-family:Helvetica, sans-serif; font-size:10pt }" ++
      "h1 { font-size:14pt }" ++
      ".code { border-collapse:collapse; width:100%; }" ++
      ".code { font-family: \"Andale Mono\", monospace; font-size:10pt }" ++
      ".code { line-height: 1.2em }" ++
      ".comment { color: green; font-style: oblique }" ++
      ".keyword { color: blue }" ++
      ".string_literal { color: red }" ++
      ".directive { color: darkmagenta }" ++
      ".expansion { display: none; }" ++
      ".macro:hover .expansion { display: block; border: 2px solid #FF0000; padding: 2px; background-color:#FFF0F0; font-weight: normal;   -webkit-border-radius:5px;  -webkit-box-shadow:1px 1px 7px #000; position: absolute; top: -1em; left:10em; z-index: 1 }" ++
      ".macro { color: darkmagenta; background-color:LemonChiffon; position: relative }" ++
      ".num { width:2.5em; padding-right:2ex; background-color:#eeeeee }" ++
      ".num { text-align:right; font-size: smaller }" ++
      ".num { color:#444444 }" ++
      ".line { padding-left: 1ex; border-left: 3px solid #ccc }" ++
      ".line { white-space: pre }" ++
      ".msg { background-color:#fff8b4; color:#000000 }" ++
      ".msg { -webkit-box-shadow:1px 1px 7px #000 }" ++
      ".msg { -webkit-border-radius:5px }" ++
      ".msg { font-family:Helvetica, sans-serif; font-size: smaller }" ++
      ".msg { font-weight: bold }" ++
      ".msg { float:left }" ++
      ".msg { padding:0.5em 1ex 0.5em 1ex }" ++
      ".msg { margin-top:10px; margin-bottom:10px }" ++
      ".msg { max-width:60em; word-wrap: break-word; white-space: pre-wrap;}" ++
      ".mrange { background-color:#dfddf3 }" ++
      ".mrange { border-bottom:1px solid #6F9DBE }" ++
      ".PathIndex { font-weight: bold }" ++
      "table.simpletable {" ++
      "padding: 5px;" ++
      "font-size:12pt;" ++
      "margin:20px;" ++
      "border-collapse: collapse; border-spacing: 0px;" ++
      "}" ++
      "td.rowname {" ++
      "text-align:right; font-weight:bold; color:#444444;" ++
      "padding-right:2ex; }" ++
      "</style>" ++
      "</head>" ++
      "<body" ^ (if with_background then "background=\"" ^ background ^ "\"" else "") ^ ">" ++
      ""
  in
    F.fprintf fmt "%s" s;
    (fd,fmt)

let open_out path =
  let fname,dir_path = match List.rev path with
    | fname::dir_path -> fname,dir_path
    | [] -> raise (Failure "Html.open_out") in
  let full_fname = DB.absolute_path (List.rev ((fname ^ ".html") :: dir_path)) in
  let fd = Unix.openfile full_fname [Unix.O_WRONLY;Unix.O_APPEND] 0o777 in
  let outc = Unix.out_channel_of_descr fd in
  let fmt = F.formatter_of_out_channel outc
  in (fd,fmt)

let close (fd,fmt) =
  F.fprintf fmt "</body>@\n</html>@.";
  Unix.close fd

(** Print a horizontal line *)
let pp_hline fmt () =
  F.fprintf fmt "<hr width=\"100%%\">@\n"

(** Print start listing *)
let pp_start_listing fmt () =
  F.fprintf fmt "%s" "<LISTING>"

(** Print end listing *)
let pp_end_listing fmt () =
  F.fprintf fmt "%s" "</LISTING>"

let pp_link ?(name=None) ?(pos=None) path fmt text =
  let pos_str = match pos with
    | None -> ""
    | Some s -> "#" ^ s in
  let link_str = (DB.relative_path path) ^ ".html" ^ pos_str in
  let name_str = match name with
    | None -> ""
    | Some n -> "name=\"" ^ n ^ "\"" in
  let pr_str =
    "<a " ^ name_str ^ "href=\"" ^ link_str ^ "\">" ^ text ^ "</a>"
  in
    F.fprintf fmt " %s" pr_str

(** Print an html link to the given node *)
let pp_node_link path_to_root description fmt id =
  let display_name = if description="" then "N"
    else String.sub description 0 1 in
  let node_name = "node" ^ string_of_int id in
  let node_text = "<span class='macro'>" ^ display_name ^ "<span class='expansion'>node"^ string_of_int id ^ " " ^ description ^ "</span></span>"
  in pp_link (path_to_root @ ["nodes";node_name]) fmt node_text

(** Print an html link to the given proc *)
let pp_proc_link path_to_root proc_name fmt text =
  pp_link (path_to_root @ [proc_name]) fmt text

(** Print an html link to the given line number of the current source file *)
let pp_line_link ?(with_name=false) ?(text=None) path_to_root fmt linenum =
  let fname = Filename.basename !Config.curr_filename in
  let linenum_str = string_of_int linenum in
  let name = "LINE" ^ linenum_str
  in pp_link ~name:(if with_name then Some name else None) (path_to_root @ ["..";fname]) ~pos:(Some name)
 fmt (match text with Some s -> s | None -> linenum_str)

(** Print an html link given node id and session *)
let pp_session_link ?(with_name=false) path_to_root fmt (node_id,session,linenum) =
  let node_name = "node" ^ (string_of_int node_id) in
  let path_to_node = path_to_root @ ["nodes";node_name] in
  let pos = "session" ^ (string_of_int session)
  in
    pp_link ~name:(if with_name then Some pos else None) ~pos:(Some pos) path_to_node fmt (node_name ^ "#" ^ pos);
    F.fprintf fmt "(%a)" (pp_line_link path_to_root) linenum
end
(* =============== END of module Html =============== *)



(* =============== START of module Log_nodes =============== *)
module Log_nodes : sig
  val current_formatter : F.formatter ref
  val start_node : int -> Cil.location -> string -> int list -> int list -> bool
  val finish_node : int -> unit
end = struct
let log_files = Hashtbl.create 11
let current_formatter = ref F.std_formatter
let id_to_fname id = "node" ^ string_of_int id
let start_node nodeid loc proc_name preds succs =
  let node_fname = id_to_fname nodeid in
  let needs_initialization,(fd,fmt) =
    try
      ignore (Hashtbl.find log_files node_fname);
      (false,Html.open_out ["nodes";node_fname])
    with Not_found ->
      (true,Html.create ["nodes";node_fname])
  in
    current_formatter := fmt;
    Hashtbl.replace log_files node_fname fd;
    if needs_initialization then
      (F.fprintf fmt "<center><h1>Cfg Node %a</h1></center>" (Html.pp_line_link ~text:(Some (string_of_int nodeid)) [".."]) loc.Cil.line;
       F.fprintf fmt "PROC: %a LINE:%a\n" (Html.pp_proc_link [".."] proc_name) proc_name (Html.pp_line_link [".."]) loc.Cil.line;
       F.fprintf fmt "<br>PREDS:@\n";
       List.iter (Html.pp_node_link [".."] "" fmt) preds;
       F.fprintf fmt "<br>SUCCS: @\n";
       List.iter (Html.pp_node_link [".."] "" fmt) succs;
       F.pp_print_flush fmt ();
       true
      )
    else false

let finish_node nodeid =
  let fname = id_to_fname nodeid in
  let fd = Hashtbl.find log_files fname
  in
    Unix.close fd;
    current_formatter := F.std_formatter
end
(* =============== END of module Log_nodes =============== *)

(* =============== START of module MyErr =============== *)

(** type of printable elements *)
type print_type =
    | PTstr
    | PTstrln
    | PTpvar
    | PTloc
    | PToff
    | PToff_list
    | PTtyp_full
    | PTtexp_full
    | PTexp
    | PTexp_list
    | PTatom
    | PTsexp
    | PThpred
    | PTtyp_list
    | PTsub
    | PTpi
    | PTsigma
    | PTprop
    | PTpropset
    | PTjprop_short
    | PTjprop_list
    | PTinstr
    | PTinstr_list
    | PTnode_instrs
    | PTpathset

(** delayable print action *)
type print_action =
    print_type * Obj.t (** data to be printed *)

let delayed_actions = ref []

(** extend he current print log *)
let add_print_action pact =
  delayed_actions := pact :: !delayed_actions

let reset_delayed_prints () =
  delayed_actions := []

let force_delayed_print_default (f:Format.formatter) (pa:print_action) : unit =
  assert false

(** hook for a printer for delayed print actions
    implemented and assigned later when all the data structures are visible *)
let force_delayed_print_ref = ref force_delayed_print_default

let force_delayed_prints () =
  List.iter (!force_delayed_print_ref !Log_nodes.current_formatter) (List.rev !delayed_actions);
  reset_delayed_prints ()

module MyErr =
  functor (Elt: sig val mode:mode end) ->
struct
  let current_mode = ref Elt.mode

  let current_colour = ref black

  let set_colour c =
    use_colours := true;
    current_colour := c

  let set_mode m = current_mode := m

  let do_print fmt_string =
    let () = if !Config.num_cores > 1 then
      (if !Config.in_child_process then change_terminal_colour !current_thread_colour
	else change_terminal_colour black)
      else
	(if !use_colours then change_terminal_colour !current_colour)
    in F.fprintf !Log_nodes.current_formatter fmt_string

  let do_print_stderr fmt_string =
    let () = if !Config.num_cores > 1 then
      (if !Config.in_child_process then change_terminal_colour_stderr !current_thread_colour
	else change_terminal_colour_stderr black)
      else
	(if !use_colours then change_terminal_colour_stderr !current_colour)
    in F.fprintf F.err_formatter fmt_string

  let log fmt_string =
    if !Config.test
    then Obj.magic throw_away
    else do_print fmt_string

  (** dump a string *)
  let d_str (s:string) = add_print_action (PTstr, Obj.repr s)
  (** dump a string plus newline *)
  let d_strln (s:string) = add_print_action (PTstrln, Obj.repr s)
  (** dump a newline *)
  let d_ln () = add_print_action (PTstrln, Obj.repr "")
  (** dump an indentation *)
  let d_indent indent =
    let s = ref "" in
    let () = for i=1 to indent do s := "  " ^ !s done
    in if indent <> 0 then add_print_action (PTstr, Obj.repr !s)

  let err fmt_string =
    do_print fmt_string

  let stderr fmt_string =
    do_print_stderr fmt_string

  let log fmt_string = match !current_mode with
    | DEFAULT -> log fmt_string
    | ALWAYS -> err fmt_string
    | NEVER -> Obj.magic throw_away

  let err fmt_string = match !current_mode with
    | DEFAULT -> err fmt_string
    | ALWAYS -> err fmt_string
    | NEVER -> Obj.magic throw_away

  let stderr fmt_string = match !current_mode with
    | DEFAULT -> stderr fmt_string
    | ALWAYS -> stderr fmt_string
    | NEVER -> Obj.magic throw_away
end
(* =============== END of module MyErr =============== *)

let start_node nodeid loc proc_name preds succs =
  Log_nodes.start_node nodeid loc proc_name preds succs

let finish_node nodeid =
  Log_nodes.finish_node nodeid
