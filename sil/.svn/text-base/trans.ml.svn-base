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
open Cil

module E = Error.MyErr (struct let mode = Error.DEFAULT end)

(** list of instructions to translate impure expressions, and the list
    of local variables generated *)
type temp_list = Ident.ident list * Sil.instr list

let mk_ext e = (([],[]),e)

(** print CIL types *)
let pp_cil_typ f = function 
  | TVoid _ -> F.fprintf f "TVoid"
  | TInt _ -> F.fprintf f "TInt"
  | TFloat _ -> F.fprintf f "TFloat"
  | TPtr (t,_) -> F.fprintf f "TPtr"
  | TArray (t,eo,_) -> F.fprintf f "TArray"
  | TFun _ -> F.fprintf f "TFun"
  | TNamed (ti,_) -> F.fprintf f "TNamed(%s)" ti.tname
  | TComp (ci,_) -> F.fprintf f "TComp(%s)" ci.cname
  | TEnum _ -> F.fprintf f "TEnum"
  | TBuiltin_va_list _ -> F.fprintf f "TBuiltin"


(** Translation of a cil type into a sil type **)
let rec _trans_typ nested (t : typ) : Sil.typ =
  match t with
  | TVoid _ -> Sil.Tvoid
  | TInt _ -> Sil.Tint
  | TFloat _ -> Sil.Tfloat
  | TPtr (t,_) -> Sil.Tptr(_trans_typ true t)
  | TArray (t,eo,_) ->
      (match eo with
       | Some (Const (CInt64 (n,_,_))) -> 
           Sil.Tarray(_trans_typ nested t, Int64.to_int n)
       | _ ->
           E.err "@[WARNING: Treat a nonconstant size parameter of an array by -1@.";
           Sil.Tarray(_trans_typ nested t, -1))
  | TFun _ -> Sil.Tfun
  | TNamed (ti,_) ->
      if (not nested) then trans_typeinfo ti
      else _trans_typ nested ti.ttype
  | TComp (ci,_) ->
      if (not nested) then trans_compinfo ci
      else
        let name = Ident.string_to_name ci.cname in
        Sil.Tvar name
  | TEnum _ -> Sil.Tint
  | TBuiltin_va_list _ ->
      if Config.timeout() <> 0 then Sil.Tvoid
      else assert false

and trans_typ (t : typ) : Sil.typ = _trans_typ false t

and trans_typeinfo (ti : typeinfo) : Sil.typ =
  let name = Ident.string_to_name ti.tname in
  E.log "@[    TRANS_TYPEINFO : %s@." ti.tname;
  match Sil.tenv_lookup name with
  | Some t -> t
  | None ->
      let t = trans_typ ti.ttype in 
      Sil.tenv_add name t;
      t

and trans_compinfo (ci : compinfo) : Sil.typ =
  let fields = ci.cfields in
  let name = Ident.string_to_name ci.cname in
  E.log "@[    TRANS_COMPINFO : %s@." ci.cname;
  match Sil.tenv_lookup name with
  | Some t -> t
  | None ->
     let trans_field fi = (Ident.string_to_name fi.fname, trans_typ fi.ftype) in
     let t = Sil.Tstruct (List.map trans_field fields) in 
     Sil.tenv_add name t;
     t 

let trans_typeinfo_decls tis = 
  List.iter (fun ti -> 
    E.log "@[  TRANS_TYPEINFO_DECL : %s - %a@." ti.tname pp_cil_typ ti.ttype;
    ignore(trans_typeinfo ti)) tis

let trans_compinfo_decls cis = 
  List.iter (fun ci -> 
    E.log "@[  TRANS_COMPINFO_DECL : %s@." ci.cname;
    ignore(trans_compinfo ci)) cis

(** Return the root of an lval *)
let rec root_of_lval lval =
  let (lval',offset) = removeOffsetLval lval
  in if offset=NoOffset then lval'
    else root_of_lval lval'

(** Return the Sil type of the root of an lval *)
let sil_type_of_lval_root lval =
  let lval = root_of_lval lval in
  let cil_t = typeOfLval lval
  in trans_typ cil_t

let print_translation_exp_warning e =
  ignore(Pretty.printf "I can't translate this:\n %a\n" Cil.d_exp e);
    if Config.timeout()=0 then
      assert false
    else mk_ext (Sil.exp_get_undefined ())


(** Set of function names whose address has been taken *)
let fun_address_set = Ident.NameSet.create ()

(** Return the set of function names whose address has been taken *)
let get_fun_address_set () = fun_address_set

(** Check if the address of a function is taken *)
let check_fun_address_taken lhost =
  match lhost with
    | Var vi -> (match vi.vtype with
	| TFun _ -> Ident.NameSet.add_string fun_address_set vi.vname
	| _ -> ())
    | _ -> () 

(** Translation of an expression into a sequence of sil instructions **)
let rec trans_exp (fundec:fundec) (e : exp) loc : temp_list * Sil.exp =
  match e with
    | Const(CInt64(n,_,_)) -> mk_ext (Sil.Const_int (Int64.to_int(n)))
    | Const _ -> mk_ext (Sil.exp_get_undefined ())
    | Lval lval ->  (** note: it's a dereference *)
	let ((idl,stmtl),e) = trans_lval fundec lval loc in
        let id = Ident.create_fresh_normal_ident Ident.name_siltmp in
        let sil_t = sil_type_of_lval_root lval in
	let stmt = Sil.Letderef (id,e,sil_t,loc)
        in ((idl@[id],stmtl@[stmt]),Sil.Var id)
    | SizeOf t -> mk_ext (Sil.Sizeof (trans_typ t))
    | SizeOfE _e ->
	let typ = trans_typ (typeOf _e)
	in mk_ext (Sil.Sizeof typ)
    | SizeOfStr _ -> print_translation_exp_warning e
    | AlignOf _ -> print_translation_exp_warning e
    | AlignOfE _ -> print_translation_exp_warning e
    | UnOp (op,e,_) ->
	let ((idl1,stml1),e1) = trans_exp fundec e loc
	in ((idl1,stml1),Sil.UnOp(op,e1))
    | BinOp (IndexPI,e1,e2,_) | BinOp (PlusPI,e1,e2,_) | BinOp (MinusPI,e1,e2,_) ->
	let ((idl1,stml1),e1) = trans_exp fundec e1 loc in
	let ((idl2,stml2),e2) = trans_exp fundec e2 loc
	in ((idl1@idl2,stml1@stml2),Sil.Lindex (e1,e2)) 
    | BinOp (op,e1,e2,_) ->
	let ((idl1,stml1),e1) = trans_exp fundec e1 loc in
	let ((idl2,stml2),e2) = trans_exp fundec e2 loc
	in ((idl1@idl2,stml1@stml2),Sil.BinOp(op,e1,e2))
    | CastE (t,e) -> 
(*      let t' = trans_typ t in *)
	let ((idl,stml),e') = trans_exp fundec e loc
	in (* ((idl,stml),Sil.Cast (t',e')) *)
          ((idl,stml), e')
    | AddrOf lval -> trans_lval fundec lval loc
    | StartOf lval -> trans_lval fundec lval loc

and trans_lval (fundec:fundec) ((lhost,off) : lval) loc : temp_list * Sil.exp =
  check_fun_address_taken lhost;
  let ((idl1,stml1),e1) = trans_lhost fundec lhost loc in
  let ((idl2,stml2),e2) = trans_offset fundec e1 off loc
  in ((idl1@idl2,stml1@stml2),e2)

and trans_lhost (fundec:fundec) (lhost:lhost) loc : temp_list * Sil.exp =
  match lhost with
    | Var vinfo ->
	let name = Ident.string_to_name vinfo.vname in 
        let pvar = 
          if vinfo.vglob then Sil.mk_pvar_global name 
          else Sil.mk_pvar name fundec "" in
        mk_ext (Sil.Lvar pvar)
    | Mem e -> trans_exp fundec e loc

and trans_offset (fundec:fundec) (e:Sil.exp) (off:offset) loc : temp_list * Sil.exp =
  match off with
    | NoOffset -> mk_ext e
    | Field (fi,off') ->
	let e' = Sil.Lfield (e,Ident.string_to_name fi.fname)
	in trans_offset fundec e' off' loc
    | Index (e',off') ->
	let ((idl1,stml1),e1) = trans_exp fundec e' loc in
	let ((idl2,stml2),e2) = trans_offset fundec (Sil.Lindex (e,e1)) off' loc
	in ((idl1@idl2,stml1@stml2),e2)

let trans_explist (fundec:fundec) el loc =
  let lst = List.map (fun x -> trans_exp fundec x loc) el in   
  let f ((idl,stmtl),e) ((idl',stmtl'),elist) = ((idl@idl', stmtl@stmtl'), e::elist)
  in List.fold_right f lst (([],[]),[])


let print_translation_warning instr =
  ignore(Pretty.printf "I can't translate this:\n %a\n" Cil.d_instr instr); 
  assert false 


(** Translation of an expression into a sequence of sil instructions *)
let rec trans_instr (fundec:fundec) (instr : instr) : temp_list =
  let instr_loc = get_instrLoc instr in
  match instr with
    | Set (lval,e,_) ->
	let ((idl1,stmtl1),e1) = trans_lval fundec lval instr_loc in
	let ((idl2,stmtl2),e2) = trans_exp fundec e instr_loc in
        let sil_t = sil_type_of_lval_root lval in
	let stmt = Sil.Set (e1,sil_t,e2,instr_loc)
	in (idl1@idl2,stmtl1@stmtl2@[stmt])
    | Call (lvalo,e,args,_) ->
	let ((idl1,stmtl1),eto) = match lvalo with
	  | None -> (([],[]),None)
	  | Some lval ->
	      let ((idl1,stmt1),sil_e) = trans_lval fundec lval instr_loc in
              let cil_t = typeOfLval lval in
              let sil_t = trans_typ cil_t in
	      let sil_root_t = sil_type_of_lval_root lval
	      in ((idl1,stmt1),Some (sil_e,sil_t,sil_root_t)) in
	let ((idl2,stmtl2),e2) = match e with
          | Lval (Var vi, NoOffset) ->  (* call without function pointers *)
	      let name = Ident.string_to_name vi.vname
	      in mk_ext (Sil.Const_fun name)
 	  | _ -> trans_exp fundec e instr_loc in
        let ((idl3,stmtl3),args3) = trans_explist fundec args instr_loc in
        let ts3 = List.map (fun e -> trans_typ (typeOf e)) args in
        let arg_ts3 = try List.combine args3 ts3 with Invalid_argument _ -> assert false in
	let stmt = Sil.Call(eto,e2,arg_ts3,instr_loc)
	in (idl1@idl2@idl3,stmtl1@stmtl2@stmtl3@[stmt])
(*
    | Call (lvalo,e,_,_) ->
	let ((idl1,stmtl1),eo) = match lvalo with
	  | None -> (([],[]),None)
	  | Some lval ->
	      let ((idl1,stmt1),e') = trans_lval lval
	      in ((idl1,stmt1),Some e') in
	let ((idl2,stmtl2),e1) = trans_exp e in
	let stmt = Sil.Call(eo,e1)
	in (idl1@idl2,stmtl1@stmtl2@[stmt])
*)
    | Asm _ -> 
        E.err "@[WARNING: Ignoring assembly code@.";
        ([], [])
        (* print_translation_warning instr (** are you kidding? *) *)

