(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** The Smallfoot Intermediate Language *)

open Ident

module F = Format
module E = Error.MyErr (struct let mode = Error.DEFAULT end)

(** {2 Programs and Types} *)

(** Names for fields. *)
type fieldname = name

(** Names for named types. *)
type typename = name

(** Names for program variables. *)
type pvar = {pv_name: name; pv_funname: name}

(** types for sil (structured) expressions *)
type typ =
    | Tvar of typename  (** named type *)
    | Tint (** integer type *)
    | Tfloat (** float type *)
    | Tvoid (** void type *)
    | Tfun (** function type *)
    | Tptr of typ (** pointer type *)
    | Tstruct of (fieldname * typ) list (** structure type *)
    | Tarray of typ * int (** array type with fixed size *)

(** program expressions *)
type exp =
    | Var of ident (** pure variable: it is not an lvalue *)
    | Const_int of int  (** integer constants *)
    | Const_fun of name  (** function value *)
    | Cast of typ * exp  (** type cast *)
    | UnOp of Cil.unop * exp (** unary operator *)
    | BinOp of Cil.binop * exp * exp (** binary operator *)
    | Lvar of pvar  (** the address of a program variable *)
    | Lfield of exp * fieldname (** a field offset *)
    | Lindex of exp * exp (** an array index offset: exp1[exp2] *)
    | Sizeof of typ (** a sizeof expression *)

(** An instruction. *)
type instr =
    | Letderef of ident * exp * typ * Cil.location (** declaration [let x = *lexp:typ] *)
    | Set of exp * typ * exp * Cil.location (** assignment [*lexp1:typ = exp2] *)
    | Nullify of pvar * Cil.location (** nullify dead variable *)
    | Call of (exp * typ * typ) option * exp * (exp*typ) list * Cil.location
               (** function call [*lexp1 = (typ)exp2(exp(typ) list)] *) 

(** offset for an lvalue *)
type offset = Off_fld of fieldname | Off_index of exp

(** {2 Components of Propositions} *)

(** structured expressions represent a value of structured type, such as an array or a struct. *)
type strexp =
    | Eexp of exp  (** Base case: normal expression *)
    | Estruct of (fieldname * strexp) list  (** C structure *)
    | Earray of int * (exp * strexp) list  (** Array of fixed size. *)

(** an atom is a pure atomic formula *)
type atom =
    | Aeq of exp * exp (** equality *)
    | Aneq of exp * exp (** disequality*)

type lseg_kind =
    | Lseg_NE (** nonempty (possibly circular) listseg *)
    | Lseg_PE (** possibly empty (possibly circular) listseg *)

(** an atomic heap predicate *)
type hpred =
    | Hpointsto of exp * strexp * exp  (** represents [exp|->strexp:typexp] where [typexp] is an expression representing a type, e.h. [sizeof(t)]. *)
    | Hlseg of lseg_kind * hpara * exp * exp * exp list (** higher-order predicate for singly-linked lists. Should ensure that exp1!=exp2 implies that exp1 is allocated. This assumption is used in the rearrangement. The last [exp list] parameter
							    is used to denote the shared links by all the nodes in the list.*)
    | Hdllseg of lseg_kind * hpara_dll * exp * exp * exp * exp * exp list (** higher-order predicate for doubly-linked lists. *)

(** parameter for the higher-order singly-linked list predicate. Means
    "lambda (root,next,svars). Exists evars. body".
    Assume that root,next,svars,evars are disjoint sets of
    primed identifiers, and include all the free primed identifiers in body. 
    body should not contain any non-primed identifiers or program 
    variables (i.e. pvars). *)
and hpara = 
    {root: ident;
     next: ident;
     svars: ident list;
     evars: ident list;
     body: hpred list}

and hpara_dll = 
    {cell: ident;  (** address cell *)
     blink: ident;  (** backward link *)
     flink: ident;  (** forward link *)
     svars_dll: ident list;
     evars_dll: ident list;
     body_dll: hpred list}



(** {2 Comparision Functions} *)

let pvar_get_name pv = pv.pv_name

let name_seed = string_to_name "seed$"

(** Turn a pvar into a seed pvar (which stored the initial value) *)
let pvar_to_seed pv = {pv with pv_funname = name_seed}

(** Check if the pvar is a seed var *)
let pvar_is_seed pv = name_equal pv.pv_funname name_seed

let pvar_compare pv1 pv2 =
  let n = name_compare pv1.pv_name pv2.pv_name in
    if n<>0 then n else name_compare pv1.pv_funname pv2.pv_funname

let pvar_equal pvar1 pvar2 =
  pvar_compare pvar1 pvar2 = 0

let pvar_names_update ne pvar =
  {pv_name = NameEnv.name_update ne pvar.pv_name; pv_funname = NameEnv.name_update ne pvar.pv_funname}

let fld_compare (fld1 : fieldname) fld2 = name_compare fld1 fld2

let fld_equal fld1 fld2 = fld_compare fld1 fld2 = 0

(** Comparision for types. *)
let rec typ_compare t1 t2 =
  if t1==t2 then 0 else match t1,t2 with
  | Tvar s1, Tvar s2 -> name_compare s1 s2
  | Tvar _, _ -> -1
  | _, Tvar _ -> 1
  | Tint, Tint -> 0
  | Tint, _ -> -1
  | _, Tint -> 1
  | Tfloat, Tfloat -> 0
  | Tfloat, _ -> -1
  | _, Tfloat -> 1
  | Tvoid, Tvoid -> 0
  | Tvoid, _ -> -1
  | _, Tvoid -> 1
  | Tfun, Tfun -> 0
  | Tfun, _ -> -1
  | _, Tfun -> 1
  | Tptr t1', Tptr t2' ->
      typ_compare t1' t2'
  | Tptr _, _ -> -1
  | _, Tptr _ -> 1
  | Tstruct ntl1, Tstruct ntl2 ->
      fld_typ_list_compare ntl1 ntl2
  | Tstruct _, _ -> -1
  | _, Tstruct _ -> 1
  | Tarray (t1,n1), Tarray (t2,n2) ->
      let n = typ_compare t1 t2
      in if n<>0 then n
	else int_compare n1 n2

and fld_typ_compare (f1,t1) (f2,t2) =
  let n = fld_compare f1 f2
  in if n<>0 then n
    else typ_compare t1 t2

and fld_typ_list_compare ftl1 ftl2 = match ftl1,ftl2 with
  | [],[] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | ft1::l1, ft2::l2 ->
      let n = fld_typ_compare ft1 ft2
      in if n<>0 then n
	else fld_typ_list_compare l1 l2

let typ_equal t1 t2 = 
  (typ_compare t1 t2 = 0)

let unop_compare o1 o2 = match o1,o2 with
  | Cil.Neg, Cil.Neg -> 0
  |  Cil.Neg, _ -> -1
  | _,  Cil.Neg -> 1
  |  Cil.BNot,  Cil.BNot -> 0
  |  Cil.BNot, _ -> -1
  | _,  Cil.BNot -> 1
  |  Cil.LNot,  Cil.LNot -> 0

let unop_equal o1 o2 = unop_compare o1 o2 = 0

let binop_compare o1 o2  = match o1,o2 with
  | Cil.PlusA, Cil.PlusA -> 0
  | Cil.PlusA, _ -> -1
  | _, Cil.PlusA -> 1
  | Cil.PlusPI, Cil.PlusPI -> 0
  | Cil.PlusPI, _ -> -1
  | _, Cil.PlusPI -> 1
  | Cil.IndexPI, Cil.IndexPI -> 0
  | Cil.IndexPI, _ -> -1
  | _, Cil.IndexPI -> 1
  | Cil.MinusA, Cil.MinusA -> 0
  | Cil.MinusA, _ -> -1
  | _, Cil.MinusA -> 1
  | Cil.MinusPI, Cil.MinusPI -> 0
  | Cil.MinusPI, _ -> -1
  | _, Cil.MinusPI -> 1
  | Cil.MinusPP, Cil.MinusPP -> 0
  | Cil.MinusPP, _ -> -1
  | _, Cil.MinusPP -> 1
  | Cil.Mult, Cil.Mult -> 0
  | Cil.Mult, _ -> -1
  | _, Cil.Mult -> 1
  | Cil.Div, Cil.Div -> 0
  | Cil.Div,_ -> -1
  | _, Cil.Div -> 1
  | Cil.Mod, Cil.Mod -> 0
  | Cil.Mod, _ -> -1
  | _, Cil.Mod -> 1
  | Cil.Shiftlt, Cil.Shiftlt -> 0
  | Cil.Shiftlt, _ -> -1
  | _, Cil.Shiftlt -> 1
  | Cil.Shiftrt, Cil.Shiftrt -> 0
  | Cil.Shiftrt, _ -> -1
  | _, Cil.Shiftrt -> 1
  | Cil.Lt, Cil.Lt -> 0
  | Cil.Lt, _ -> -1
  | _, Cil.Lt -> 1
  | Cil.Gt, Cil.Gt -> 0
  | Cil.Gt, _ -> -1
  | _, Cil.Gt -> 1
  | Cil.Le, Cil.Le -> 0
  | Cil.Le, _ -> -1
  | _, Cil.Le -> 1
  | Cil.Ge, Cil.Ge -> 0
  | Cil.Ge, _ -> -1
  | _, Cil.Ge -> 1
  | Cil.Eq, Cil.Eq -> 0
  | Cil.Eq, _ -> -1
  | _, Cil.Eq -> 1
  | Cil.Ne, Cil.Ne -> 0
  | Cil.Ne, _ -> -1
  | _, Cil.Ne -> 1
  | Cil.BAnd, Cil.BAnd -> 0
  | Cil.BAnd, _ -> -1
  | _, Cil.BAnd -> 1
  | Cil.BXor, Cil.BXor -> 0
  | Cil.BXor, _ -> -1
  | _, Cil.BXor -> 1
  | Cil.BOr, Cil.BOr -> 0
  | Cil.BOr, _ -> -1
  | _, Cil.BOr -> 1
  | Cil.LAnd, Cil.LAnd -> 0
  | Cil.LAnd, _ -> -1
  | _, Cil.LAnd -> 1
  | Cil.LOr, Cil.LOr -> 0

let binop_equal o1 o2 = binop_compare o1 o2 = 0

module Tick = struct
let tick_count = ref 0
let count_per_tick = 3000000 (* 620000 *)
let last_time = ref 0.0
let tick = ref 0

let tick () =
  incr tick_count;
  if !tick_count = count_per_tick then
    (incr tick;
     if !tick=1 then last_time := Stats.get_current_time ();
     E.stderr "Tick num %d (%f per sec)@." !tick (1.0 /. (Stats.get_current_time() -. !last_time));
     last_time := Stats.get_current_time ();
     tick_count := 0)
end

(** Compare epressions. Variables come before other expressions. *)
let rec exp_compare (e1 : exp) (e2 : exp) : int  =
  if !Config.tick then Tick.tick ();
  (*  if e1==e2 then 0 else *)
  match (e1,e2) with
    | (Var (id1), Var(id2)) ->
        ident_compare id2 id1
    | (Var _, _) ->
	-1 
    | (_, Var _) -> 1
    | Const_int n1, Const_int n2 ->
	int_compare n1 n2
    | Const_int _, _ -> -1
    | _, Const_int _ -> 1
    | Const_fun n1, Const_fun n2 ->
	name_compare n1 n2
    | Const_fun _, _ -> -1
    | _, Const_fun _ -> 1
    | Cast (t1,e1), Cast(t2,e2) ->
	let n = exp_compare e1 e2
	in if n<>0 then n
	  else typ_compare t1 t2
    | Cast _, _ -> -1
    | _, Cast _ -> 1
    | UnOp (o1,e1), UnOp (o2,e2) ->
	let n = unop_compare o1 o2
	in if n<>0 then n
	  else exp_compare e1 e2
    | UnOp _, _ -> -1
    | _, UnOp _ -> 1
    | BinOp (o1,e1,f1), BinOp (o2,e2,f2) ->
	let n = binop_compare o1 o2
	in if n<>0 then n
	  else let n = exp_compare e1 e2
	    in if n<>0 then n
	      else exp_compare f1 f2
    | BinOp _, _ -> -1
    | _, BinOp _ -> 1
    | Lvar i1, Lvar i2 ->
	pvar_compare i1 i2
    | Lvar _, _ -> -1
    | _, Lvar _ -> 1
    | Lfield (e1,f1), Lfield (e2,f2) ->
	let n = exp_compare e1 e2
	in if n<>0 then n
	  else fld_compare f1 f2
    | Lfield _, _ -> -1
    | _, Lfield _ -> 1
    | Lindex (e1,f1), Lindex (e2,f2) ->
	let n = exp_compare e1 e2
	in if n<>0 then n
	  else exp_compare f1 f2
    | Lindex _, _ -> -1
    | _, Lindex _ -> 1
    | Sizeof t1, Sizeof t2 ->
	typ_compare t1 t2

let exp_equal e1 e2 = 
  exp_compare e1 e2 = 0

(** Compare atoms. Equalities come before disequalities *)
let atom_compare a b =
  if a==b then 0 else
    match (a,b) with
      | (Aeq (e1,e2), Aeq(f1,f2)) ->
	  let n = exp_compare e1 f1 in
	    if n<>0 then n else exp_compare e2 f2
      | (Aeq _, Aneq _) -> -1
      | (Aneq _, Aeq _) -> 1
      | (Aneq (e1,e2), Aneq (f1,f2)) ->
	  let n = exp_compare e1 f1 in
	    if n<>0 then n else exp_compare e2 f2

let atom_equal x y = atom_compare x y = 0

let rec strexp_compare se1 se2 =
  if se1==se2 then 0
  else match se1,se2 with
    | Eexp e1, Eexp e2 -> exp_compare e1 e2
    | Eexp _, _ -> -1
    | _, Eexp _ -> 1
    | Estruct fel1, Estruct fel2 -> fld_strexp_list_compare fel1 fel2
    | Estruct _, _ -> -1
    | _, Estruct _ -> 1
    | Earray (n1,esel1), Earray (n2,esel2) ->
	let n = int_compare n1 n2
	in if n<>0 then n
	  else exp_strexp_list_compare esel1 esel2

and fld_strexp_compare (fld1,se1) (fld2,se2) =
  let n = fld_compare fld1 fld2
  in if n<>0 then n
    else strexp_compare se1 se2

and fld_strexp_list_compare fel1 fel2 = match fel1,fel2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | fe1::l1, fe2::l2 ->
      let n = fld_strexp_compare fe1 fe2
      in if n<>0 then n
	else fld_strexp_list_compare l1 l2

and exp_strexp_compare (e1,se1) (e2,se2) =
  let n = exp_compare e1 e2
  in if n<>0 then n
    else strexp_compare se1 se2

and exp_strexp_list_compare esel1 esel2 = match esel1,esel2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | ese1::l1, ese2::l2 ->
      let n = exp_strexp_compare ese1 ese2
      in if n<>0 then n
	else exp_strexp_list_compare l1 l2

let strexp_equal se1 se2 = 
  (strexp_compare se1 se2 = 0)

let fld_strexp_equal fld_sexp1 fld_sexp2 = 
  (fld_strexp_compare fld_sexp1 fld_sexp2 = 0)

let exp_strexp_equal ese1 ese2 = 
  (exp_strexp_compare ese1 ese2 = 0)


let rec exp_list_compare el1 el2 = match el1,el2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | e1::l1, e2::l2 ->
      let n = exp_compare e1 e2
      in if n<>0 then n
	else exp_list_compare l1 l2

let exp_list_equal el1 el2 =
  exp_list_compare el1 el2 = 0

let lseg_kind_compare k1 k2 = match k1,k2 with
  | Lseg_NE, Lseg_NE -> 0
  | Lseg_NE, Lseg_PE -> -1
  | Lseg_PE, Lseg_NE -> 1
  | Lseg_PE, Lseg_PE -> 0

let lseg_kind_equal k1 k2 = 
  lseg_kind_compare k1 k2 = 0

(** Comparsion between heap predicates. Hpointsto comes before others. *)
let rec hpred_compare hpred1 hpred2 =
  if hpred1==hpred2 then 0 else
    match (hpred1,hpred2) with
      | Hpointsto (e1,_,_), Hlseg(_,_,e2,_,_) when exp_compare e2 e1 <> 0 ->
	  exp_compare e2 e1
      | Hpointsto (e1,_,_), Hdllseg(_,_,e2,_,_,_,_) when exp_compare e2 e1 <> 0 ->
	  exp_compare e2 e1
      | Hlseg(_,_,e1,_,_), Hpointsto (e2,_,_) when exp_compare e2 e1 <> 0 ->
	  exp_compare e2 e1
      | Hlseg(_,_,e1,_,_), Hdllseg(_,_,e2,_,_,_,_) when exp_compare e2 e1 <> 0 ->
	  exp_compare e2 e1
      | Hdllseg(_,_,e1,_,_,_,_), Hpointsto (e2,_,_) when exp_compare e2 e1 <> 0 ->
	  exp_compare e2 e1
      | Hdllseg(_,_,e1,_,_,_,_), Hlseg(_,_,e2,_,_) when exp_compare e2 e1 <> 0 ->
	  exp_compare e2 e1
      | Hpointsto (e1,se1,te1), Hpointsto (e2,se2,te2) ->
	  let n = exp_compare e2 e1 in
	    if n<>0 then n else
	      let n = strexp_compare se2 se1 in
		if n<>0 then n else exp_compare te2 te1
      | (Hpointsto _, _) -> -1
      | (_, Hpointsto _) -> 1
      | Hlseg (k1,hpar1,e1,f1,el1), Hlseg (k2,hpar2,e2,f2,el2) ->
	  let n = exp_compare e2 e1
	  in if n<>0 then n
	    else let n = lseg_kind_compare k2 k1
	      in if n<>0 then n
		else let n = hpara_compare hpar2 hpar1
		  in if n<>0 then n
		    else let n = exp_compare f2 f1
		      in if n<>0 then n
			else exp_list_compare el2 el1
      | Hlseg _, Hdllseg _ -> -1
      | Hdllseg _, Hlseg _ -> 1
      | Hdllseg (k1,hpar1,e1,f1,g1,h1,el1), Hdllseg (k2,hpar2,e2,f2,g2,h2,el2) ->
	  let n = exp_compare e2 e1
	  in if n<>0 then n
	    else let n = lseg_kind_compare k2 k1
	      in if n<>0 then n
		else let n = hpara_dll_compare hpar2 hpar1
		  in if n<>0 then n
		    else let n = exp_compare f2 f1
		      in if n<>0 then n
			else let n = exp_compare g2 g1
			  in if n<>0 then n
			    else let n = exp_compare h2 h1
			      in if n<>0 then n
				else exp_list_compare el2 el1

and hpara_compare hp1 hp2 =
  let n = ident_compare hp1.root hp2.root
  in if n<>0 then n
    else let n = ident_compare hp1.next hp2.next
      in if n<>0 then n
	else let n = ident_list_compare hp1.svars hp2.svars
	  in if n<>0 then n
	    else let n = ident_list_compare hp1.evars hp2.evars
	      in if n<>0 then n
		else hpred_list_compare hp1.body hp2.body

and hpara_dll_compare hp1 hp2 =
  let n = ident_compare hp1.cell hp2.cell
  in if n<>0 then n
    else let n = ident_compare hp1.blink hp2.blink
      in if n<>0 then n
	else let n = ident_compare hp1.flink hp2.flink
	  in if n<>0 then n
	    else let n = ident_list_compare hp1.svars_dll hp2.svars_dll
	      in if n<>0 then n
		else let n = ident_list_compare hp1.evars_dll hp2.evars_dll
		  in if n<>0 then n
		    else hpred_list_compare hp1.body_dll hp2.body_dll

and hpred_list_compare hl1 hl2 = match hl1,hl2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | h1::l1, h2::l2 ->
      let n = hpred_compare h1 h2
      in if n<>0 then n
	else hpred_list_compare l1 l2


let hpred_equal hpred1 hpred2 = 
  (hpred_compare hpred1 hpred2 = 0)

let hpara_equal hpara1 hpara2 = 
  (hpara_compare hpara1 hpara2 = 0)

let hpara_dll_equal hpara1 hpara2 = 
  (hpara_dll_compare hpara1 hpara2 = 0)

(** {2 Pretty Printing} *)

(** Pretty print an identifier. *)

(** Print a sequence. *)
let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> F.fprintf f "%a" pp x
  | x::l -> F.fprintf f "%a,@ %a" pp x (pp_seq pp) l

(** Pretty print a unary operator. *)
let str_unop = function
  | Cil.Neg -> "-"
  | Cil.BNot -> "~"
  | Cil.LNot -> "!"

(** Pretty print a binary operator. *)
let str_binop = function
  | Cil.PlusA -> "+"
  | Cil.PlusPI -> "+pi+"
  | Cil.IndexPI -> "+ipi+"
  | Cil.MinusA -> "-"
  | Cil.MinusPI -> "-pi-"
  | Cil.MinusPP -> "-pp-"
  | Cil.Mult -> "*"
  | Cil.Div -> "/"
  | Cil.Mod -> "%"
  | Cil.Shiftlt -> "<<"
  | Cil.Shiftrt -> ">>"
  | Cil.Lt -> "<"
  | Cil.Gt -> ">"
  | Cil.Le -> "<="
  | Cil.Ge -> ">="
  | Cil.Eq -> "=="
  | Cil.Ne -> "!="
  | Cil.BAnd -> "&"
  | Cil.BXor -> "^"
  | Cil.BOr -> "|"
  | Cil.LAnd -> "&&"
  | Cil.LOr -> "||"

(** Pretty print a type. *)
let rec pp_typ f _ = ()
(*
function 
  | Tvar tname -> fprintf f "%a" pp_name tname
  | Tint -> fprintf f "int"
  | Tfloat -> fprintf f "float"
  | Tvoid -> fprintf f "void" 
  | Tfun -> fprintf f "_function_"
  | Tptr typ -> fprintf f "%a*" pp_typ typ
  | Tstruct ftl -> 
      fprintf f "struct {%a}"
      (pp_seq (fun f (fld,t) -> fprintf f "%a %a" pp_typ t pp_name fld)) ftl
  | Tarray (typ,n) -> fprintf f "%a[%d]" pp_typ typ n
*)

(** Pretty print a type with all the details. *)
let rec pp_typ_full f = function 
  | Tvar tname -> F.fprintf f "%a" pp_name tname
  | Tint -> F.fprintf f "int"
  | Tfloat -> F.fprintf f "float"
  | Tvoid -> F.fprintf f "void" 
  | Tfun -> F.fprintf f "_fn_"
(*
  | Tptr typ -> F.fprintf f "_pt_"
*)
  | Tptr typ -> F.fprintf f "%a*" pp_typ_full typ
  | Tstruct ftl -> 
      F.fprintf f "struct {%a}"
      (pp_seq (fun f (fld,t) -> F.fprintf f "%a %a" pp_typ_full t pp_name fld)) ftl
  | Tarray (typ,n) -> F.fprintf f "%a[%d]" pp_typ_full typ n

(** dump a type with all the details. *)
let d_typ_full (t:typ) = Error.add_print_action (Error.PTtyp_full, Obj.repr t)

(** dump a list of types. *)
let d_typ_list (tl:typ list) = Error.add_print_action (Error.PTtyp_list, Obj.repr tl)

let pp_pair f ((fld:fieldname),(t:typ)) =
  F.fprintf f "%a %a" pp_typ t pp_name fld

(** Pretty print a program variable. *)
let pp_pvar f pv =
  F.fprintf f "%a$%a" pp_name pv.pv_funname pp_name pv.pv_name

(** Dump a program variable. *)
let d_pvar (pvar:pvar) = Error.add_print_action (Error.PTpvar, Obj.repr pvar)

(** Pretty print a list of program variables. *)
let pp_pvar_list f pvl =
  F.fprintf f "%a" (pp_seq (fun f e -> F.fprintf f "%a" pp_pvar e)) pvl

(** Pretty print an expression. *)
let rec _pp_exp pp_t f =
  let pp_exp = _pp_exp pp_t
  in function
  | Var id -> pp_ident f id
  | Const_int n -> F.fprintf f "%d" n
  | Const_fun fn -> F.fprintf f "_fun_%a" pp_name fn
  | Cast (typ,e) -> F.fprintf f "(%a)%a" pp_t typ pp_exp e
  | UnOp (op,e) -> F.fprintf f "%s%a" (str_unop op) pp_exp e
  | BinOp (op,e1,e2) -> F.fprintf f "(%a%s%a)" pp_exp e1 (str_binop op) pp_exp e2
  | Lvar pv when name_equal pv.pv_funname name_seed -> F.fprintf f "%a" pp_name pv.pv_name
  | Lvar pv -> F.fprintf f "&%a" pp_pvar pv
  | Lfield (e,fld) -> F.fprintf f "%a.%a" pp_exp e pp_name fld
  | Lindex (e1,e2) -> F.fprintf f "%a[%a]" pp_exp e1 pp_exp e2
  | Sizeof t -> F.fprintf f "sizeof(%a)" pp_t t

let pp_exp f e =
  _pp_exp pp_typ f e

(** dump an expression. *)
let d_exp (e:exp) = Error.add_print_action (Error.PTexp, Obj.repr e)

(** Pretty print a list of expressions. *)
let pp_exp_list f expl = 
  F.fprintf f "%a" (pp_seq (fun f e -> F.fprintf f "%a" pp_exp e)) expl

(** dump a list of expressions. *)
let d_exp_list (el:exp list) = Error.add_print_action (Error.PTexp_list, Obj.repr el)

let pp_texp f = function
  | Sizeof t -> pp_typ f t
  | e -> pp_exp f e

(** Pretty print a type with all the details. *)
let pp_texp_full f = function
  | Sizeof t -> pp_typ_full f t
  | e -> _pp_exp pp_typ_full f e

(** Dump a type expression with all the details. *)
let d_texp_full (te:exp) = Error.add_print_action (Error.PTtexp_full, Obj.repr te)

(** Pretty print an offset *)
let pp_offset f = function
  | Off_fld fld -> F.fprintf f "%a" pp_name fld 
  | Off_index exp -> F.fprintf f "%a" pp_exp exp

(** dump an offset. *)
let d_offset (off:offset) = Error.add_print_action (Error.PToff, Obj.repr off)

(** Pretty print a list of offsets *)
let rec pp_offset_list f = function
  | [] -> ()  
  | [off1;off2] -> F.fprintf f "%a.%a" pp_offset off1 pp_offset off2 
  | off::off_list -> F.fprintf f "%a.%a" pp_offset off pp_offset_list off_list 

(** Dump a list of offsets *)
let d_offset_list (offl:offset list) = Error.add_print_action (Error.PToff_list, Obj.repr offl)

(** Pretty print a location *)
let pp_loc f (loc:Cil.location) =
  F.fprintf f "[line %d]" loc.Cil.line

(** Dump a location *)
let d_loc (loc:Cil.location) = Error.add_print_action (Error.PTloc, Obj.repr loc)

let pp_exp_typ f (e,t) =
  F.fprintf f "%a:%a" pp_exp e pp_typ t

(** Pretty print an instruction. *)
let pp_instr f = function
  | Letderef (id,e,t,loc) -> F.fprintf f "%a=*%a:%a %a" pp_ident id pp_exp e pp_typ t pp_loc loc
  | Set (e1,t,e2,loc) -> F.fprintf f "*%a:%a=%a %a" pp_exp e1 pp_typ t pp_exp e2 pp_loc loc
  | Nullify (pvars,loc) ->
      F.fprintf f "NULLIFY(%a); %a" pp_pvar pvars pp_loc loc
  | Call (eto,e,arg_ts,loc) ->
      (match eto with
	| None -> ()
	| Some (e1,t1,root_t) -> F.fprintf f "*%a=(%a)" pp_exp e1 pp_typ t1);
      F.fprintf f "%a(%a) %a" pp_exp e (pp_seq pp_exp_typ) arg_ts pp_loc loc

(** Dump an instruction. *)
let d_instr (i:instr) = Error.add_print_action (Error.PTinstr, Obj.repr i)

let rec pp_instr_list f = function
  | [] -> F.fprintf f ""
  | i::is -> F.fprintf f "%a;@ %a" pp_instr i pp_instr_list is

(** Dump a list of instructions. *)
let d_instr_list (il:instr list) = Error.add_print_action (Error.PTinstr_list, Obj.repr il)

let pp_atom f = function
  | Aeq (e1,e2) -> F.fprintf f "%a=%a" pp_exp e1 pp_exp e2
  | Aneq (e1,e2) -> F.fprintf f "%a!=%a" pp_exp e1 pp_exp e2

(** dump an atom *)
let d_atom (a:atom) = Error.add_print_action (Error.PTatom, Obj.repr a)

let rec pp_sexp f = function
  | Eexp e -> pp_exp f e
  | Estruct fel ->
      F.fprintf f "{@[%a@]}" (pp_seq (fun f (n,se) -> F.fprintf f "%a:%a" pp_name n pp_sexp se)) fel
  | Earray (size,nel) ->
      F.fprintf f "[%d|%a]" size (pp_seq (fun f (i,se) -> F.fprintf f "%a:%a" pp_exp i pp_sexp se)) nel

(** dump a strexp. *)
let d_sexp (se:strexp) = Error.add_print_action (Error.PTsexp, Obj.repr se)

(** Print a *-separated sequence. *)
let rec pp_star_seq pp f = function
  | [] -> ()
  | [x] -> F.fprintf f "%a" pp x
  | x::l -> F.fprintf f "%a * %a" pp x (pp_star_seq pp) l

let pp_lseg_kind f = function
  | Lseg_NE -> F.fprintf f "ne"
  | Lseg_PE -> F.fprintf f "pe"

let rec pp_hpred f = function
  | Hpointsto (e,se,te) -> F.fprintf f "%a|->%a:%a" pp_exp e pp_sexp se pp_texp te
  | Hlseg (k,pred,e1,e2,elist) -> 
      F.fprintf f "lseg%a@ (%a)@ (%a,%a,%a)" pp_lseg_kind k pp_hpara pred pp_exp e1 pp_exp e2 (pp_seq pp_exp) elist
  | Hdllseg (k,pred,iF,oB,oF,iB,elist) ->
      F.fprintf f "dllseg%a@ (%a)@ (%a,%a,%a,%a,%a)" pp_lseg_kind k pp_dll_hpara pred pp_exp iF pp_exp oB  pp_exp oF pp_exp iB (pp_seq pp_exp) elist


and pp_hpara f pred =
  let (r,n,svars, evars,b) = (pred.root, pred.next, pred.svars, pred.evars, pred.body) 
  in F.fprintf f "lam [%a,%a,%a]. exists [%a]. %a" 
       pp_ident r 
       pp_ident n 
       (pp_seq pp_ident) svars
       (pp_seq pp_ident) evars
       (pp_star_seq pp_hpred) b 

and pp_dll_hpara f pred =
  let (iF,oB,oF,svars, evars,b) = (pred.cell, pred.blink,pred.flink, pred.svars_dll, pred.evars_dll, pred.body_dll) 
  in F.fprintf f "lam [%a,%a,%a,%a]. exists [%a]. %a" 
       pp_ident iF      
       pp_ident oB
       pp_ident oF      
       (pp_seq pp_ident) svars
       (pp_seq pp_ident) evars
       (pp_star_seq pp_hpred) b 

(** dump a hpred. *)
let d_hpred (hpred:hpred) = Error.add_print_action (Error.PThpred, Obj.repr hpred)

let rec pp_hpred_list f = function
  | [] -> ()
  | [hp] -> 
      F.fprintf f "%a" pp_hpred hp
  | hp::hps -> 
      F.fprintf f "%a * %a" pp_hpred hp pp_hpred_list hps

(** {2 Functions for traversing SIL data types} *)  

let rec strexp_expmap (f:exp->exp) = function
  | Eexp e ->
      Eexp (f e)
  | Estruct fld_se_list ->
      let f_fld_se (fld,se) = (fld, strexp_expmap f se) in
      Estruct (List.map f_fld_se fld_se_list)
  | Earray (size, idx_se_list) ->
      let f_idx_se (idx,se) = (f idx, strexp_expmap f se) in
      Earray (size, List.map f_idx_se idx_se_list)

let hpred_expmap (f:exp->exp) = function
  | Hpointsto (e, se, te) -> 
      let e' = f e in
      let se' = strexp_expmap f se in
      let te' = f te in
      Hpointsto(e', se', te')  
  | Hlseg (k, hpara, root, next, shared) -> 
      let root' = f root in
      let next' = f next in
      let shared' = List.map f shared in
      Hlseg (k, hpara, root', next', shared')     
  | Hdllseg (k, hpara, iF, oB, oF, iB, shared) -> 
      let iF' = f iF in
      let oB' = f oB in
      let oF' = f oF in
      let iB' = f iB in
      let shared' = List.map f shared in
      Hdllseg (k, hpara, iF', oB', oF', iB', shared')

let hpred_list_expmap (f:exp->exp) (hlist:hpred list) =
  List.map (hpred_expmap f) hlist

let atom_expmap (f:exp->exp) = function
  | Aeq (e1,e2) -> Aeq (f e1, f e2)
  | Aneq (e1,e2) -> Aneq (f e1, f e2)

let atom_list_expmap (f:exp->exp) (alist:atom list) =
  List.map (atom_expmap f) alist

(** {2 Function for computing lexps in sigma} *)

let hpred_get_lexp acc = function 
  | Hpointsto(e,_,_) -> e::acc
  | Hlseg(_,_,e,_,_) -> e::acc
  | Hdllseg(_,_,e1,_,_,e2,_) -> e1::e2::acc

let sigma_get_lexps (filter:exp->bool) (sigma:hpred list) : exp list =
  let lexps = List.fold_left hpred_get_lexp [] sigma in
  List.filter filter lexps  

(** {2 Utility Functions for Expressions} *)

(** Return the root of [lexp]. *)
let rec root_of_lexp lexp = match lexp with
    | Var _ -> lexp
    | Const_int _ -> lexp
    | Const_fun _ -> lexp
    | Cast (t,e) -> root_of_lexp e
    | UnOp _ | BinOp _ -> lexp
    | Lvar _ -> lexp
    | Lfield(e,_) -> root_of_lexp e
    | Lindex(e,_) -> root_of_lexp e
    | Sizeof _ -> lexp

(** Checks whether an expression denotes a location by pointer arithmetic. 
    Currently, catches array-indexing expressions such as a[i] only. *)
let rec exp_pointer_arith = function
  | Lfield (e, _) -> exp_pointer_arith e
  | Lindex _ -> true
  | _ -> false

let exp_get_undefined () = 
  Var (Ident.create_fresh_primed_ident name_siltmp)

(** {2 Functions for computing program variables} *)

let rec exp_fpv = function 
  | Var id -> []
  | Const_int n -> []
  | Const_fun n -> []
  | Cast (_, e) | UnOp (_, e) -> exp_fpv e
  | BinOp (_, e1, e2) -> exp_fpv e1 @ exp_fpv e2 
  | Lvar name -> [name] 
  | Lfield (e, _) -> exp_fpv e
  | Lindex (e1, e2) -> exp_fpv e1 @ exp_fpv e2
  | Sizeof _ -> []

let rec strexp_fpv = function
  | Eexp e -> exp_fpv e
  | Estruct fld_se_list -> 
      let f (_,se) = strexp_fpv se
      in List.flatten (List.map f fld_se_list)
  | Earray (size, idx_se_list) ->
      let f (idx,se) = exp_fpv idx @ strexp_fpv se
      in List.flatten (List.map f idx_se_list)

let atom_fpv = function
  | Aeq (e1,e2) -> exp_fpv e1 @ exp_fpv e2
  | Aneq (e1,e2) -> exp_fpv e1 @ exp_fpv e2

let rec hpred_fpv = function
  | Hpointsto (base, se, te) -> 
      exp_fpv base @ strexp_fpv se @ exp_fpv te
  | Hlseg (_,para, e1, e2, elist) -> 
      let fpvars_in_elist = List.flatten (List.map exp_fpv elist)
      in hpara_fpv para (* Hongseok: This set has to be empty. *)  
         @ exp_fpv e1 
         @ exp_fpv e2 
         @ fpvars_in_elist
  | Hdllseg (_,para,e1,e2,e3,e4,elist) -> 
      let fpvars_in_elist = List.flatten (List.map exp_fpv elist)
      in hparadll_fpv para (* Hongseok: This set has to be empty. *)
         @ exp_fpv e1 
         @ exp_fpv e2 
         @ exp_fpv e3
         @ exp_fpv e4 
         @ fpvars_in_elist

(** Hongseok: hpara should not contain any program variables.
    This is because it might cause problems when we do interprocedural
    analysis. In interprocedural analysis, we should consider the issue
    of scopes of program variables. *)
and hpara_fpv para = 
  let fpvars_in_body = List.flatten (List.map hpred_fpv para.body) 
  in match fpvars_in_body with
    | [] -> []
    | _ -> assert false

(** Hongseok: hparadll should not contain any program variables.
    This is because it might cause problems when we do interprocedural
    analysis. In interprocedural analysis, we should consider the issue
    of scopes of program variables. *)
and hparadll_fpv para = 
  let fpvars_in_body = List.flatten (List.map hpred_fpv para.body_dll) 
  in match fpvars_in_body with
    | [] -> []
    | _ -> assert false

(** {2 Functions for computing free non-program variables} *)

(** Type of free variables. These include primed, normal and footprint variables. We keep a count of how many types the variables appear. *)
type fav = ident list ref

let fav_new () =
  ref []

(** Emptyness check. *)
let fav_is_empty fav = match !fav with
  | [] -> true
  | _ -> false

(** Check whether a predicate holds for all elements. *)
let fav_for_all fav predicate =
  List.for_all predicate !fav

(** Check whether a predicate holds for some elements. *)
let fav_exists fav predicate =
  List.exists predicate !fav

(** extend [fav] with a [id] *)
let (++) fav id =
  fav := id::!fav

(** extend [fav] with ident list [idl] *)
let (+++) fav idl =
  List.iter (fun id -> fav ++ id) idl

(** add identity lists to fav *)
let ident_list_fav_add idl fav = 
  fav +++ idl

(** Convert a list to a fav. *)
let fav_from_list l =
  let fav = fav_new () in
  let _ = List.iter (fun id -> fav ++ id) l
  in fav

let rec remove_duplicates_from_sorted special_equal = function
  | [] -> []
  | [x] -> [x]
  | x::y::l -> 
      if (special_equal x y) 
      then remove_duplicates_from_sorted special_equal (y::l)
      else x::(remove_duplicates_from_sorted special_equal (y::l))

(** Convert a [fav] to a sorted list of identifiers without repetitions. *)
let fav_to_list fav =
  remove_duplicates_from_sorted ident_equal (List.sort ident_compare !fav)

(** Convert a [fav] to a list of identifiers while preserving the order 
that the identifiers were added to [fav]. *)
let fav_to_list_stable fav = 
  let rec f seen = function
    | [] -> seen
    | id::rest -> 
        let rest' = List.filter (fun id' -> not (ident_equal id id')) rest in
        f (id::seen) rest' in
  f [] !fav

(** Pretty print a fav. *)
let pp_fav f fav =
  (pp_seq pp_ident) f (fav_to_list fav)

(** Copy a [fav]. *)
let fav_copy fav =
  ref (List.map (fun x -> x) !fav)

(** Turn a xxx_fav_add function into a xxx_fav function *)
let fav_imperative_to_functional f x =
  let fav = fav_new () in
  let _ = f fav x
  in fav

(** [fav_filter_ident fav f] only keeps [id] if [f id] is true. *)
let fav_filter_ident fav filter =
  fav := List.filter filter !fav

(** Like [fav_filter_ident] but return a copy. *)
let fav_copy_filter_ident fav filter =
  ref (List.filter filter !fav)

(** checks whether every element in l1 appears l2 **)
let rec ident_sorted_list_subset l1 l2 =
  match l1,l2 with
    | [],_ -> true
    | _::_,[] -> false
    | id1::l1, id2::l2 ->
	let n = ident_compare id1 id2 in
	  if n=0 then ident_sorted_list_subset l1 (id2::l2)
	  else if n>0 then ident_sorted_list_subset (id1::l1) l2
	  else false


(** [fav_subset_ident fav1 fav2] returns true if every ident in [fav1]
    is in [fav2].*)
let fav_subset_ident fav1 fav2 =
  ident_sorted_list_subset (fav_to_list fav1) (fav_to_list fav2)

let fav_mem fav id =
  List.mem id !fav

let rec exp_fav_add fav = function 
  | Var id -> fav ++ id
  | Const_int n -> ()
  | Const_fun fn -> ()
  | Cast (_, e) | UnOp (_, e) -> exp_fav_add fav e
  | BinOp (_, e1, e2) -> exp_fav_add fav e1; exp_fav_add fav e2 
  | Lvar id -> () (* do nothing since we only count non-program variables *)
  | Lfield (e, _) -> exp_fav_add fav e
  | Lindex (e1, e2) -> exp_fav_add fav e1; exp_fav_add fav e2
  | Sizeof _ -> ()

let exp_fav =
  fav_imperative_to_functional exp_fav_add

let rec ident_in_exp id e =
  let fav = fav_new () in 
  let _ = exp_fav_add fav e 
  in fav_mem fav id

let rec strexp_fav_add fav = function
  | Eexp e -> exp_fav_add fav e
  | Estruct fld_se_list ->
      List.iter (fun (_,se) -> strexp_fav_add fav se) fld_se_list
  | Earray (_, idx_se_list) ->
      List.iter (fun (e,se) -> exp_fav_add fav e; strexp_fav_add fav se) idx_se_list

let atom_fav_add fav = function
  | Aeq (e1,e2) | Aneq(e1,e2) -> exp_fav_add fav e1; exp_fav_add fav e2

let atom_fav =
  fav_imperative_to_functional atom_fav_add

(** Atoms do not contain binders *)
let atom_av_add = atom_fav_add

let hpara_fav_add fav para = () (* we assume that para is closed *) 
let hpara_dll_fav_add fav para = () (* we assume that para is closed *) 

let rec hpred_fav_add fav = function
  | Hpointsto (base, sexp, te) -> exp_fav_add fav base; strexp_fav_add fav sexp; exp_fav_add fav te
  | Hlseg (_,para, e1, e2, elist) ->
      hpara_fav_add fav para;
      exp_fav_add fav e1; exp_fav_add fav e2;
      List.iter (exp_fav_add fav) elist
  | Hdllseg (_,para, e1, e2,e3,e4, elist) ->
      hpara_dll_fav_add fav para;
      exp_fav_add fav e1; exp_fav_add fav e2;
      exp_fav_add fav e3; exp_fav_add fav e4;
      List.iter (exp_fav_add fav) elist
 
(** {2 Functions for computing all free or bound non-program variables} *)

let exp_av_add = exp_fav_add (** Expressions do not bind variables *)

let strexp_av_add = strexp_fav_add (** Structured expressions do not bind variables *)

let rec hpara_av_add fav para =
  List.iter (hpred_av_add fav) para.body;
  fav ++ para.root; fav ++ para.next;
  fav +++ para.svars; fav +++ para.evars

and hpara_dll_av_add fav para =
  List.iter (hpred_av_add fav) para.body_dll;
  fav ++ para.cell; fav ++ para.blink; fav ++ para.flink;
  fav +++ para.svars_dll; fav +++ para.evars_dll

and hpred_av_add fav = function
  | Hpointsto (base, se, te) ->
      exp_av_add fav base; strexp_av_add fav se; exp_av_add fav te
  | Hlseg (_,para, e1, e2, elist) ->
      hpara_av_add fav para;
      exp_av_add fav e1; exp_av_add fav e2;
      List.iter (exp_av_add fav) elist
  | Hdllseg (_,para, e1, e2, e3,e4,elist) ->
      hpara_dll_av_add fav para;
      exp_av_add fav e1; exp_av_add fav e2;
      exp_av_add fav e3; exp_av_add fav e4;
      List.iter (exp_av_add fav) elist

let hpara_shallow_av_add fav para =
  List.iter (hpred_fav_add fav) para.body;
  fav ++ para.root; fav ++ para.next;
  fav +++ para.svars; fav +++ para.evars

let hpara_dll_shallow_av_add fav para =
  List.iter (hpred_fav_add fav) para.body_dll;
  fav ++ para.cell; fav ++ para.blink; fav ++ para.flink;
  fav +++ para.svars_dll; fav +++ para.evars_dll

(** Variables in hpara, excluding bound vars in the body *)
let hpara_shallow_av = fav_imperative_to_functional hpara_shallow_av_add

(** Variables in hpara_dll, excluding bound vars in the body *)
let hpara_dll_shallow_av = fav_imperative_to_functional hpara_dll_shallow_av_add

(** {2 Functions for Substitution} *)

(** substitution *)
type subst = (ident * exp) list

(** Create a substitution from a list of pairs. *)
let sub_of_list sub =
  sub

(** Convert a subst to a list of pairs. *)
let sub_to_list sub =
  sub

(** The empty substitution. *)
let sub_empty = sub_of_list []

(** Comparison between substitutions. *) 
let rec sub_compare (sub1:subst) (sub2:subst) =
  if sub1==sub2 then 0
  else match (sub1,sub2) with
    | ([],[]) -> 0
    | ([],_::_) -> -1
    | ((i1,e1)::sub1',(i2,e2)::sub2') ->
	let n = ident_compare i1 i2
	in if n<>0 then n
	  else let n = exp_compare e1 e2
	    in if n<>0 then n
	      else sub_compare sub1' sub2'
    | (_::_,[]) -> 1

(** Equality for substitutions. *) 
let sub_equal sub1 sub2 =
  sub_compare sub1 sub2 = 0

(** Join two substitutions into one. *)
(** Hongseok: Dangerous operation. Might break the invariant that no substitutions give
    two definitions of an identifier. *)
let sub_join = (@)

let rec typ_names_add (ns:NameSet.t) = function
  | Tvar n -> NameSet.add ns n
  | Tint | Tfloat | Tvoid | Tfun -> ()
  | Tptr t -> typ_names_add ns t
  | Tstruct ftl ->
      let go (f,t) =
	NameSet.add ns f;
	typ_names_add ns t
      in List.iter go ftl
  | Tarray (t,n) -> typ_names_add ns t

module Typtbl = Hashtbl.Make (struct type t = typ let equal = typ_equal let hash = Hashtbl.hash end)

let typ_update_memo = Typtbl.create 17

let rec _typ_names_update ne _t = match _t with
  | Tvar n ->
      let n' = NameEnv.name_update ne n
      in Tvar n'
  | Tint | Tfloat | Tvoid | Tfun -> _t
  | Tptr t ->
      let t' = typ_names_update ne t
      in Tptr t'
  | Tstruct ftl ->
      let go (f,t) =
	(NameEnv.name_update ne f, typ_names_update ne t)
      in Tstruct (List.map go ftl)
  | Tarray (t,n) ->
      let t' = typ_names_update ne t
      in Tarray (t',n)

and typ_names_update ne t =
  try Typtbl.find typ_update_memo t
  with Not_found ->
    let t' = _typ_names_update ne t in
    let () = Typtbl.add typ_update_memo t t'
    in t'

(** Memoizing typ_names_update so the sharing is preserved *)
let typ_names_update ne t =
  Typtbl.clear typ_update_memo;
  typ_names_update ne t

let rec exp_names_add ns = function
  | Var id ->
      NameSet.add_ident ns id
  | Const_int _ -> ()
  | Const_fun fn ->
      NameSet.add ns fn
  | Cast (t,e) ->
      typ_names_add ns t;
      exp_names_add ns e
  | UnOp (_,e) -> exp_names_add ns e
  | BinOp (_,e1,e2) ->
      exp_names_add ns e1;
      exp_names_add ns e2
  | Lvar pv ->
      NameSet.add ns pv.pv_name;
      NameSet.add ns pv.pv_funname
  | Lfield (e,n) ->
      exp_names_add ns e;
      NameSet.add ns n
  | Lindex (e1,e2) ->
      exp_names_add ns e1;
      exp_names_add ns e2
  | Sizeof t ->
      typ_names_add ns t

let rec exp_names_update ne = function
  | Var id ->
      Var (NameEnv.ident_update ne id)
  | Const_int n -> Const_int n
  | Const_fun fn ->
      let fn' = NameEnv.name_update ne fn
      in Const_fun fn'
  | Cast (t,e) ->
      let t' = typ_names_update ne t in
      let e' = exp_names_update ne e
      in Cast (t',e')
  | UnOp(op,e) ->
      UnOp(op,exp_names_update ne e)
  | BinOp(op,e1,e2) ->
      BinOp(op,exp_names_update ne e1,exp_names_update ne e2)
  | Lvar pv ->
      Lvar (pvar_names_update ne pv)
  | Lfield (e,name) ->
      let e' = exp_names_update ne e in
      let name' = NameEnv.name_update ne name
      in Lfield (e',name')
  | Lindex (e1,e2) ->
      let e1' = exp_names_update ne e1 in
      let e2' = exp_names_update ne e2
      in Lindex (e1',e2')
  | Sizeof t ->
      Sizeof (typ_names_update ne t)

let sub_names_add ns sub =
  let f (i,e) =
    NameSet.add_ident ns i;
    exp_names_add ns e
  in List.iter f sub

let sub_names_update ne sub =
  let f (i,e) = (NameEnv.ident_update ne i, exp_names_update ne e)
  in List.map f sub

(** [sub_find filter sub] returns the expression associated to the first identifier that satisfies [filter]. Raise [Not_found] if there isn't one. *)
let sub_find filter (sub:subst) =
  snd (List.find (fun (i,_) -> filter i) sub)

(** [sub_filter filter sub] restricts the domain of [sub] to the
    identifiers satisfying [filter]. *)
let sub_filter filter (sub:subst) =
  List.filter (fun (i,_) -> filter i) sub

(** [sub_filter_pair filter sub] restricts the domain of [sub] to the
    identifiers satisfying [filter(id,sub(id))]. *)
let sub_filter_pair = List.filter

(** [sub_range_partition filter sub] partitions [sub] according to
    whether range expressions satisfy [filter]. *)
let sub_range_partition filter (sub:subst) =
  List.partition (fun (_,e) -> filter e) sub

(** [sub_domain_partition filter sub] partitions [sub] according to
    whether domain identifiers satisfy [filter]. *)
let sub_domain_partition filter (sub:subst) =
  List.partition (fun (i,_) -> filter i) sub

(** Return the list of identifiers in the domain of the substitution. *)
let sub_domain sub =
  List.map fst sub

(** Return the list of expressions in the range of the substitution. *)
let sub_range sub =
  List.map snd sub

(** [sub_range_map f sub] applies [f] to the expressions in the range of [sub]. *)
let sub_range_map f sub =
  List.map (fun (i,e) -> (i, f e)) sub

(** [sub_map f g sub] applies the renaming [f] to identifiers in the domain
of [sub] and the substitution [g] to the expressions in the range of [sub]. *)
let sub_map f g sub =
  List.map (fun (i,e) -> (f i, g e)) sub

let mem_sub id sub =
  List.exists (fun (id1,_) -> ident_equal id id1) sub

(** Extend substitution and return [None] if not possible. *)
let extend_sub sub id exp : subst option = 
 if mem_sub id sub then None else Some ((id,exp)::sub)

(** Free auxilary variables in the domain and range of the
    substitution. *)
let sub_fav_add fav (sub:subst) =
  List.iter (fun (id,e) -> fav++id; exp_fav_add fav e) sub

(** Substitutions do not contain binders *)
let sub_av_add = sub_fav_add

let rec exp_sub (subst:subst) e = 
  match e with
  | Var id ->
      let rec apply_sub = function
	| [] -> e
	| (i,e)::l -> if ident_equal i id then e else apply_sub l
      in apply_sub subst
  | Const_int n ->
      e
  | Const_fun fn ->
      e
  | Cast (t,e1) -> 
      let e1' = exp_sub subst e1 
      in Cast (t,e1')
  | UnOp (op, e1) ->
      let e1' = exp_sub subst e1
      in UnOp(op, e1')
  | BinOp (op, e1, e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in BinOp (op, e1', e2')
  | Lvar id ->
      e
  | Lfield (e1,fld) ->
      let e1' = exp_sub subst e1 
      in Lfield (e1',fld)
  | Lindex (e1,e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in Lindex (e1',e2')
  | Sizeof t ->
      e

let strexp_sub subst = 
  strexp_expmap (exp_sub subst) 

let atom_sub subst = 
  atom_expmap (exp_sub subst)

let rec hpred_sub subst =  
  hpred_expmap (exp_sub subst)

let hpara_sub subst para = para 

let hpara_dll_sub subst para = para 

(** {2 Functions for replacing occurrences of expressions.} *)

let exp_replace_exp epairs e =
  try
    let (_,e') = List.find (fun (e1,_) -> exp_equal e e1) epairs
    in e'
  with Not_found -> e

let rec strexp_replace_exp epairs = function 
  | Eexp e -> Eexp (exp_replace_exp epairs e)
  | Estruct fsel -> 
      let fsel' = List.map (fun (fld,se) -> (fld, strexp_replace_exp epairs se)) fsel
      in Estruct fsel'
  | Earray (size, isel) ->
      let isel_replace (idx,se) = (exp_replace_exp epairs idx, strexp_replace_exp epairs se) in
      let isel' = List.map isel_replace isel
      in Earray (size,isel')

let atom_replace_exp epairs = function
  | Aeq (e1, e2) -> 
      let e1' = exp_replace_exp epairs e1 in
      let e2' = exp_replace_exp epairs e2 
      in Aeq (e1', e2') 
  | Aneq (e1, e2) ->
      let e1' = exp_replace_exp epairs e1 in
      let e2' = exp_replace_exp epairs e2 
      in Aneq (e1', e2')

let rec hpred_replace_exp epairs = function
  | Hpointsto (root,se,te) ->
      let root_repl = exp_replace_exp epairs root in
      let strexp_repl = strexp_replace_exp epairs se in
      let te_repl = exp_replace_exp epairs te
      in Hpointsto (root_repl, strexp_repl, te_repl) 
  | Hlseg (k,para,root,next,shared) -> 
      let root_repl = exp_replace_exp epairs root in
      let next_repl = exp_replace_exp epairs next in
      let shared_repl = List.map (exp_replace_exp epairs) shared 
      in Hlseg (k,para, root_repl, next_repl, shared_repl) 
  | Hdllseg (k,para,e1,e2,e3,e4,shared) -> 
      let e1' = exp_replace_exp epairs e1 in
      let e2' = exp_replace_exp epairs e2 in
      let e3' = exp_replace_exp epairs e3 in
      let e4' = exp_replace_exp epairs e4 in
      let shared_repl = List.map (exp_replace_exp epairs) shared 
      in Hdllseg (k,para,e1',e2',e3',e4',shared_repl) 

(** {2 Type Environment} *)
(** has tables on strings *)

(** Type for type environment. *)
type tenv = typ NameHash.t

(** Find the type of an identifier in the type environment. *)
let tenv_find tenv key = 
  try (NameHash.find tenv key) with Not_found -> assert false

(** Global type environment. *)
let tenv = NameHash.create 1000

(** Look up a name in the global type environment. *) 
let tenv_lookup name =
  try Some (NameHash.find tenv name)
  with Not_found -> None

(** Add a (name,type) pair to the global type environment. *)
let tenv_add name typ =
  NameHash.add tenv name typ;
  E.log "@[    Extending tenv@.";
  E.log "@[<8>      NAME: %a@." pp_name name;
  E.log "@[<8>      TYPE: %a@." pp_typ_full typ

(** {2 Functions for constructing or destructing entities in this module} *)

let mk_pvar (name:name) (fundec:Cil.fundec) (suffix:string) : pvar =
  let funname = fundec.Cil.svar.Cil.vname
  in {pv_name = name; pv_funname = string_to_name (funname^suffix)}

let mk_pvar_global (name:name) : pvar =
  {pv_name = name; pv_funname = string_to_name "#GB"}

let pvar_add_suffix pvar suffix =
  let name_suffix = string_to_name (name_to_string (pvar.pv_funname) ^ suffix)
  in {pvar with pv_funname = name_suffix}

(** Compute the offset list of an expression *)
let exp_get_offsets exp = 
  let rec f offlist_past e = match e with
    | Var _ | Const_int _ | Const_fun _ | UnOp _ | BinOp _ | Lvar _ | Sizeof _ -> offlist_past
    | Cast(t,sub_exp) -> f offlist_past sub_exp
    | Lfield(sub_exp,fldname) -> f (Off_fld(fldname)::offlist_past) sub_exp
    | Lindex(sub_exp,e) -> f (Off_index(e)::offlist_past) sub_exp
  in f [] exp

(** Convert all the lseg's in sigma to nonempty lsegs. *)
let sigma_to_sigma_ne sigma : (atom list * hpred list) list = 
  if !Config.nelseg then
    let f eqs_sigma_list hpred = match hpred with
      | Hpointsto _ | Hlseg(Lseg_NE,_,_,_,_) | Hdllseg(Lseg_NE,_,_,_,_,_,_) -> 
          let g (eqs,sigma) = (eqs,hpred::sigma) 
  	  in List.map g eqs_sigma_list 
      | Hlseg(Lseg_PE,para,e1,e2,el) ->
          let g (eqs,sigma) = [(Aeq(e1,e2)::eqs, sigma); (eqs, Hlseg(Lseg_NE,para,e1,e2,el)::sigma)]
  	  in List.flatten (List.map g eqs_sigma_list)
      | Hdllseg(Lseg_PE,para_dll,e1,e2,e3,e4,el) ->
	  let g (eqs,sigma) = [(Aeq(e1,e3)::Aeq(e2,e4)::eqs,sigma); (eqs, Hdllseg(Lseg_NE,para_dll,e1,e2,e3,e4,el)::sigma)] 
	  in List.flatten (List.map g eqs_sigma_list)
    in List.fold_left f [([],[])] sigma
  else
    [([],sigma)]

(** [hpara_instantiate para e1 e2 elist] instantiates [para] with [e1],
    [e2] and [elist].  If [para = lambda (x,y,xs). exists zs. b],
    then the result of the instantiation is [b\[e1/x,e2/y,elist/xs,_zs'/zs\]] 
    for some fresh [_zs'].*)
let hpara_instantiate para e1 e2 elist =
  let subst_for_svars = 
    let g id e = (id,e) 
    in try (List.map2 g para.svars elist) 
      with Invalid_argument _ -> assert false in 
  let ids_evars =
    let g id = create_fresh_primed_ident (ident_name id) 
    in List.map g para.evars in
  let subst_for_evars =
    let g id id' = (id, Var id') 
    in try (List.map2 g para.evars ids_evars) 
      with Invalid_argument _ -> assert false in
  let subst = sub_of_list ((para.root,e1)::(para.next,e2)::subst_for_svars@subst_for_evars)
  in (ids_evars, List.map (hpred_sub subst) para.body)

(** [hpara_dll_instantiate para cell blink flink  elist] instantiates [para] with [cell],
    [blink], [flink],  and [elist].  If [para = lambda (x,y,z,xs). exists zs. b],
    then the result of the instantiation is [b\[cell/x, blink/y, flink/z, elist/xs,_zs'/zs\]] 
    for some fresh [_zs'].*)
let hpara_dll_instantiate (para: hpara_dll) cell blink flink  elist =
  let subst_for_svars = 
    let g id e = (id,e) 
    in try (List.map2 g para.svars_dll elist) 
      with Invalid_argument _ -> assert false in 
  let ids_evars =
    let g id = create_fresh_primed_ident (ident_name id) 
    in List.map g para.evars_dll in
  let subst_for_evars =
    let g id id' = (id, Var id') 
    in try (List.map2 g para.evars_dll ids_evars) 
      with Invalid_argument _ -> assert false in
  let subst = sub_of_list ((para.cell,cell)::(para.blink,blink)::(para.flink,flink)::subst_for_svars@subst_for_evars)
  in (ids_evars, List.map (hpred_sub subst) para.body_dll)
