(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Symbolic Execution *)

open Ident
open Sil
open Prop
open Propset
open Prover
open Match
module Exn = Exceptions

module E = Error.MyErr (struct let mode = Error.DEFAULT end)
(*let () = E.set_mode Error.ALWAYS
let () = E.set_colour Error.green*)

exception ARRAY_ACCESS

let rec idlist_assoc id = function
  | [] -> raise Not_found
  | (i,x)::l -> if ident_equal i id then x else idlist_assoc id l

let rec fldlist_assoc fld = function
  | [] -> raise Not_found
  | (fld',x)::l -> if fld_equal fld fld' then x else fldlist_assoc fld l

let rec explist_assoc e = function
  | [] -> raise Not_found
  | (e',x)::l -> if exp_equal e e' then x else explist_assoc e l

let rec unroll_type typ off = match (typ,off) with
  | (Tvar tname,_) -> 
      begin
	match tenv_lookup tname with
	  | Some typ' -> unroll_type typ' off
	  | None -> assert false
      end 
  | (Tstruct ftl, Off_fld fld) -> 
      (try fldlist_assoc fld ftl 
	with Not_found -> 
	  begin
            E.d_strln ".... Invalid Field Access ....";
            E.d_strln ("  Fld : " ^ name_to_string fld); 
            E.d_str "Type : "; Sil.d_typ_full typ; E.d_ln (); 
            raise Prop.Bad_footprint
	  end)
  | (Tarray (typ',_), Off_index _) ->
      typ'
  | (_, Off_index (Const_int 0)) ->
      typ
  | _ -> 
      E.d_strln ".... Invalid Field Access ....";
      E.d_str "  Fld : "; Sil.d_offset off; E.d_ln (); 
      E.d_str "Type : "; Sil.d_typ_full typ; E.d_ln ();
      assert false

let rec unroll_strexp strexp off = match (strexp,off) with
  | (Estruct fsel, Off_fld fld) ->
      (try Some (fldlist_assoc fld fsel)
	with Not_found -> None)
  | (Earray (_,isl),Off_index e) ->
      (try Some (explist_assoc e isl)
	with Not_found -> None)
  | (_,Off_index (Const_int 0)) ->
      Some strexp
  | _ -> assert false

let list_split equal x xys = 
  let (xy,xys') = List.partition (fun (x',_) -> equal x x') xys 
  in match xy with
    | [] -> (xys', None)
    | [(x',y')] -> (xys', Some y')
    | _ -> assert false

let check_bad_index size e = 
  match !Config.array_level, e with
  | 0, Const_int n -> (n >= size)
  | 0, _ -> true
  | _ -> false

let rec construct_strexp exp offlist typ = 
  match offlist with
  | [] -> Eexp exp
  | off::offlist'-> 
      let typ' = unroll_type typ off in  
      let strexp = construct_strexp exp offlist' typ' in 
      match (off,typ) with
      | (Off_fld fld, _) -> Estruct [(fld,strexp)]
      | (Off_index n, Tarray(_,size)) -> 
          if (check_bad_index size n) then assert false
          else Earray (size, [(n,strexp)])
      | (Off_index (Const_int 0), _) -> strexp
      | _ -> assert false

(** apply function [f] to the expression at position [offlist] in [strexp]
    if not found, expand [strexp] and apply [f] to [None] *)
let rec apply_offlist nullify_struct strexp typ offlist (f: exp option -> exp) =
  let pp_error () =
    E.d_strln ".... Invalid Field ....";
    E.d_str "  strexp : "; Sil.d_sexp strexp; E.d_ln (); 
    E.d_str "offlist : "; Sil.d_offset_list offlist; E.d_ln ();
    E.d_str "type : "; Sil.d_typ_full typ; E.d_ln () in
  match (offlist,strexp) with
  | ([],Eexp e) -> 
      let e' = f (Some e) in (e', Eexp e')
  | ((Off_fld fld)::offlist',Estruct fsel) ->
      let typ' = unroll_type typ (Off_fld fld) in
      let (fsel', strexpo) = list_split name_equal fld fsel in
      begin 
        match strexpo with
        | Some strexp' ->
           let (e',strexp'') = apply_offlist nullify_struct strexp' typ' offlist' f in 
           (e', Estruct ((fld,strexp'')::fsel'))
           (* Hongseok's comment: The list above is no longer
	    * sorted above.  The invariant has to be
	    * re-restablished somewhere else *)
        | None ->
            let e' = f None in
            let strexp'' = construct_strexp e' offlist' typ' in 
            (e', Estruct ((fld,strexp'')::fsel'))
	    (* Hongseok's comment: The list above is no longer
	     * sorted above.  The invariant has to be
	     * re-restablished somewhere else *)
      end
  | (Off_index n)::offlist', Earray (size,isl) ->
      if (check_bad_index size n)
      then (pp_error(); assert false)
      else
      begin 
 	let typ' = unroll_type typ (Off_index n) in
	let (isl', strexpo) = list_split exp_equal n isl in 
        match strexpo with
        | Some strexp' ->
            let (e',strexp'') = apply_offlist nullify_struct strexp' typ' offlist' f in 
            (e', Earray (size,(n,strexp'')::isl'))
	    (* Hongseok's comment: The list above is no
  	     * longer sorted above.  The invariant has to be
  	     * re-restablished somewhere else *)
        | None ->
	    let e' = f None in
	    let strexp'' = construct_strexp e' offlist' typ' in 
            (e', Earray (size, (n,strexp'')::isl'))
	    (* Hongseok's comment: The list above is no longer
	     * sorted above.  The invariant has to be
  	     * re-restablished somewhere else *)
      end
  | _,  Earray _ ->
      let offlist' = (Off_index (Const_int 0))::offlist in
      apply_offlist nullify_struct strexp typ offlist' f
  | (Off_index (Const_int 0))::offlist', _ ->
      apply_offlist nullify_struct strexp typ offlist' f
  | ([],Estruct fesl) ->
      if nullify_struct then
	(
	  E.d_strln "WARNING: struct assignment treated as nondeterministic assignment";
	  (f None, Estruct [])
	)
      else
	  (f None, Estruct fesl)
  | _ -> 
      pp_error();
      assert false

(** [ptsto_lookup (lexp,strexp,typ) offlist id] given
    [lexp|->strexp:typ] returns the expression at position
    [offlist] in [strexp], together with [strexp], if the
    location [offlist] exists in [strexp]. If the location
    does not exist, it constructs [strexp'] containing
    [id] at [offlist], and returns ([ident],[strexp']).*)
let ptsto_lookup (lexp,strexp,typ) offlist id =
  let f = function
    | Some exp -> exp
    | None -> Var id
  in apply_offlist false strexp typ offlist f

(** [ptsto_update (lexp,strexp,typ) offlist exp] given
    [lexp|->strexp:typ] returns an updated [strexp] obtained by
    replacing the expression at [offlist] with [exp]. *)
let ptsto_update (lexp,strexp,typ) offlist exp =
  let f _ = exp
  in snd (apply_offlist true strexp typ offlist f)

let name_n = string_to_name "n"

let pp_rearrangement_error prop lexp =
  E.d_strln ".... Rearrangement Error ....";
  E.d_str "  Exp:"; Sil.d_exp lexp; E.d_ln (); 
  E.d_str "Prop:"; Prop.d_prop prop; E.d_ln ()

(* Exposes lexp|->- from iter. In case that it is not possible to
 * expose lexp|->-, this function prints an error message and
 * faults. There are four things to note. First, typ is the type of the
 * root of lexp. Second, prop should mean the same as iter. Third, the
 * result [] means that the given input iter is inconsistent.  This
 * happens when the theorem prover can prove the inconsistency of prop,
 * only after unrolling some predicates in prop. This function ensures
 * that the theorem prover cannot prove the inconsistency of any of the
 * new iters in the result. *)
let rec iter_rearrange lexp typ prop iter : (offset list) prop_iter list =
(*  E.stderr "\n\n iter_rearrange\nlexp:\n%a\nprop:@.%a\niter:@.%a@." pp_exp lexp pp_prop prop pp_prop (prop_iter_to_prop iter); *)

  let filter = function
    | Hpointsto (base,_,_) | Hlseg (_,_,base,_,_) -> 
        is_root prop base lexp 
    | Hdllseg (_,_,first,_,_,last,_) ->
	let result_first = is_root prop first lexp
	in match result_first with
	  | None -> is_root prop last lexp
	  | Some _ -> result_first in

  let default_case_iter iter' =
    if !Config.footprint then
      let iter'' = prop_iter_add_hpred_footprint iter' (lexp,typ) in
      let offsets_default = exp_get_offsets lexp in 
      let iter_default = prop_iter_set_state iter'' offsets_default
      in [iter_default]
    else 
      begin 
	pp_rearrangement_error prop lexp;
	raise Exn.Symexec_memory_error 
      end in

  let recurse_on_iters iters =
    let f_one_iter iter' =
      let prop' = prop_iter_to_prop iter' 
      in if check_inconsistency prop' then []
	else iter_rearrange (Prop.exp_normalize_prop prop' lexp) typ prop' iter' in
    let rec f_many_iters iters_lst = function
      | [] -> List.flatten (List.rev iters_lst)
      | iter'::iters' ->
	  let iters_res' = f_one_iter iter' 
	  in f_many_iters (iters_res'::iters_lst) iters' 		
    in f_many_iters [] iters in

  let do_ne_lseg iter para e1 e2 elist = 
    if (!Config.nelseg) then
      let iter_inductive_case =
        let n' = Var (create_fresh_primed_ident name_n) in
        let (_, para_inst1) = hpara_instantiate para e1 n' elist in
        let hpred_list1 = para_inst1@[mk_lseg Lseg_NE para n' e2 elist] 
        in prop_iter_update_current_by_list iter hpred_list1 in
      let iter_base_case = 
        let (_, para_inst) = hpara_instantiate para e1 e2 elist 
        in  prop_iter_update_current_by_list iter para_inst 
      in
         recurse_on_iters [iter_inductive_case;iter_base_case] 
    else
      let iter_inductive_case =
        let n' = Var (create_fresh_primed_ident name_n) in
        let (_, para_inst1) = hpara_instantiate para e1 n' elist in
        let hpred_list1 = para_inst1@[mk_lseg Lseg_PE para n' e2 elist] 
        in prop_iter_update_current_by_list iter hpred_list1 
      in recurse_on_iters [iter_inductive_case] 
  in
  let do_ne_dllseg_first iter para_dll e1 e2 e3 e4 elist = 
    let iter_inductive_case =
      let n' = Var (create_fresh_primed_ident name_n) in
      let (_, para_dll_inst1) = hpara_dll_instantiate para_dll e1 e2 n' elist in
      let hpred_list1 = para_dll_inst1@[mk_dllseg Lseg_NE para_dll n' e1 e3 e4 elist]
      in prop_iter_update_current_by_list iter hpred_list1 in
    let iter_base_case = 
      let (_, para_dll_inst) = hpara_dll_instantiate para_dll e1 e2 e3 elist in
      let iter' = prop_iter_update_current_by_list iter para_dll_inst in
      let prop' = prop_iter_to_prop iter' in
      let prop'' = conjoin_eq ~footprint:(!Config.footprint) e1 e4 prop' 
      in match (prop_iter_create prop'') with
	| None -> assert false
	| Some iter' -> iter' 
    in recurse_on_iters [iter_inductive_case;iter_base_case] 
  in
  let do_ne_dllseg_last iter para_dll e1 e2 e3 e4 elist =
    let iter_inductive_case =
      let n' = Var (create_fresh_primed_ident name_n) in
      let (_, para_dll_inst1) = hpara_dll_instantiate para_dll e4 n' e3 elist in
      let hpred_list1 = para_dll_inst1@[mk_dllseg Lseg_NE para_dll e1 e2 e4 n' elist]
      in prop_iter_update_current_by_list iter hpred_list1 in
    let iter_base_case = 
      let (_, para_dll_inst) = hpara_dll_instantiate para_dll e4 e2 e3 elist in
      let iter' = prop_iter_update_current_by_list iter para_dll_inst in
      let prop' = prop_iter_to_prop iter' in
      let prop'' = conjoin_eq ~footprint:(!Config.footprint) e1 e4 prop' 
      in match (prop_iter_create prop'') with
	| None -> assert false
	| Some iter' -> iter' 
    in recurse_on_iters [iter_inductive_case;iter_base_case] in

  let do_pe_lseg iter para e1 e2 elist = 
    let iter_nonemp_case =
      let n' = Var (create_fresh_primed_ident name_n) in
      let (_, para_inst1) = hpara_instantiate para e1 n' elist in
      let hpred_list1 = para_inst1@[mk_lseg Lseg_PE para n' e2 elist] 
      in prop_iter_update_current_by_list iter hpred_list1 in
    let iter_subcases = 
      let removed_prop = prop_iter_remove_curr_then_to_prop iter in
      let prop' = conjoin_eq ~footprint:(!Config.footprint) e1 e2 removed_prop 
      in match (prop_iter_create prop') with
	| None -> default_case_iter iter 
	| Some iter' -> [iter_nonemp_case;iter']
    in recurse_on_iters iter_subcases 
  in
  let do_pe_dllseg_first iter para_dll e1 e2 e3 e4 elist = 
    let iter_inductive_case =
      let n' = Var (create_fresh_primed_ident name_n) in
      let (_, para_dll_inst1) = hpara_dll_instantiate para_dll e1 e2 n' elist in
      let hpred_list1 = para_dll_inst1@[mk_dllseg Lseg_PE para_dll n' e1 e3 e4 elist]
      in prop_iter_update_current_by_list iter hpred_list1 in
    let iter_subcases = 
      let removed_prop = prop_iter_remove_curr_then_to_prop iter in
      let prop' = conjoin_eq ~footprint:(!Config.footprint) e1 e3 removed_prop in
      let prop'' = conjoin_eq ~footprint:(!Config.footprint) e2 e4 prop' 
      in match (prop_iter_create prop'') with
	| None -> default_case_iter iter
	| Some iter' -> [iter_inductive_case;iter']
    in recurse_on_iters iter_subcases 
  in
  let do_pe_dllseg_last iter para_dll e1 e2 e3 e4 elist =
    let iter_inductive_case =
      let n' = Var (create_fresh_primed_ident name_n) in
      let (_, para_dll_inst1) = hpara_dll_instantiate para_dll e4 n' e3 elist in
      let hpred_list1 = para_dll_inst1@[mk_dllseg Lseg_PE para_dll e1 e2 e4 n' elist]
      in prop_iter_update_current_by_list iter hpred_list1 in
    let iter_subcases = 
      let removed_prop = prop_iter_remove_curr_then_to_prop iter in
      let prop' = conjoin_eq ~footprint:(!Config.footprint) e1 e3 removed_prop in
      let prop'' = conjoin_eq ~footprint:(!Config.footprint) e2 e4 prop' 
      in match (prop_iter_create prop'') with
	| None -> default_case_iter iter
	| Some iter' -> [iter_inductive_case;iter']
    in recurse_on_iters iter_subcases in 

  match (prop_iter_find iter filter) with
    | None -> 
	default_case_iter iter
    | Some iter ->
	match prop_iter_current iter with 
          | (Hpointsto _,_) ->
	      if !Config.footprint then [prop_iter_extend_ptsto iter lexp]
	      else if !Config.footprint_analysis && !Config.splitting_fields_level>0 then
		(if prop_iter_check_fields_ptsto iter lexp then [iter]
		  else
 		    begin
		      pp_rearrangement_error prop lexp;
		      (* E.stderr "\n\n iter_rearrange\nlexp:\n%a\nprop:@.%a\niter:@.%a@." pp_exp lexp pp_prop prop pp_prop (prop_iter_to_prop iter); *)
		      raise Exn.Symexec_memory_error
		    end)
	      else [iter]
	  | (Hlseg (Lseg_NE,para,e1,e2,elist),_) -> 
	      do_ne_lseg iter para e1 e2 elist
          | (Hlseg (Lseg_PE,para,e1,e2,elist),_) ->
              do_pe_lseg iter para e1 e2 elist
	  | (Hdllseg (Lseg_NE,para_dll,e1,e2,e3,e4,elist),_) -> 
	      begin
		match is_root prop e1 lexp, is_root prop e4 lexp with
		  | None, None -> assert false
		  | Some _, _ -> do_ne_dllseg_first iter para_dll e1 e2 e3 e4 elist 
		  | _, Some _ -> do_ne_dllseg_last iter para_dll e1 e2 e3 e4 elist 
	      end 
          | (Hdllseg (Lseg_PE,para_dll,e1,e2,e3,e4,elist),_) ->   
	      begin
		match is_root prop e1 lexp, is_root prop e4 lexp with
		  | None, None -> assert false
		  | Some _, _ -> do_pe_dllseg_first iter para_dll e1 e2 e3 e4 elist 
		  | _, Some _ -> do_pe_dllseg_last iter para_dll e1 e2 e3 e4 elist 
	      end 

let rearrange_arith lexp prop =
  if (!Config.array_level >= 2) then raise ARRAY_ACCESS
  else
    let root = Sil.root_of_lexp lexp in
    if Prover.check_allocatedness prop root then
      raise ARRAY_ACCESS
    else
      raise Exn.Symexec_memory_error

(** [rearrange lexp typ prop] rearranges [prop] such that [lexp|->...] is
    exposed. [exp|->strexp:typ] is the exposed points-to predicate,
    and [offset list] is the path that leads to the exposed position
    inside [strexp]. *)
let rearrange lexp typ prop =
  let lexp = exp_normalize_prop prop lexp in 
  E.d_strln ".... Rearrangement Start ....";
  E.d_str "Exp: "; Sil.d_exp lexp; E.d_ln ();
  E.d_str "Prop: "; Prop.d_prop prop; E.d_ln ();
  if (!Config.array_level >= 1 && Sil.exp_pointer_arith lexp) 
  then rearrange_arith lexp prop;
  match prop_iter_create prop with
  | None -> 
      if !Config.footprint then
        let iter = prop_iter_add_hpred_footprint_to_prop prop (lexp,typ) in
        let offsets_default = exp_get_offsets lexp in
        let iter_default = prop_iter_set_state iter offsets_default in 
        [iter_default]
      else begin
        pp_rearrangement_error prop lexp;
        raise Exn.Symexec_memory_error
      end
  | Some iter -> iter_rearrange lexp typ prop iter 

let execute_letderef id rhs_exp iter =
  let iter_ren = prop_iter_make_id_primed id iter in
  let (lexp,strexp,typ,offlist) = match prop_iter_current iter_ren with
    | (Hpointsto(lexp,strexp,Sizeof typ),Some offlist) -> (lexp,strexp,typ,offlist)
    | (_, None) -> assert false 
    | _ -> assert false in
  let (contents,new_strexp) = ptsto_lookup (lexp,strexp,typ) offlist id in
  let new_ptsto = mk_ptsto lexp new_strexp (Sizeof typ) in
  let iter_res = prop_iter_update_current iter_ren new_ptsto in
  let prop_res = prop_iter_to_prop iter_res in
  let prop_res' = conjoin_eq (Var(id)) contents prop_res in
  (*
  E.err "@[<2>.... Execute Letderef ....@\n";
  E.err "Inst: %a=*%a@\n" pp_ident id pp_exp rhs_exp;
  E.err "Prop[In]: @[%a@]@\n" pp_prop (prop_iter_to_prop iter);
  E.err "Prop[Out]: @[%a@]@\n@." pp_prop prop_res';
  *)
  prop_res'

let execute_set lhs_exp rhs_exp iter = 
  let (lexp,strexp,typ,offlist) = match prop_iter_current iter with
    | (Hpointsto(lexp,strexp,Sizeof typ),Some offlist) -> (lexp,strexp,typ,offlist)
    | _ -> assert false in
  let new_strexp = ptsto_update (lexp,strexp,typ) offlist rhs_exp in
  let new_ptsto = mk_ptsto lexp new_strexp (Sizeof typ) in
  let iter' = prop_iter_update_current iter new_ptsto in
  let prop_res = prop_iter_to_prop iter' in
  (*
  E.err "@[<2>.... Execute Set ....@\n";
  E.err "Inst:* %a=%a@\n" pp_exp lhs_exp pp_exp rhs_exp;
  E.err "Prop[In]: @[%a@]@\n" pp_prop (prop_iter_to_prop iter);
  E.err "Prop[Out]: @[%a@]@\n@." pp_prop prop_res;
  *)
  prop_res

let name_new = string_to_name "siltmp"
let name_cnt = string_to_name "siltmp"

let execute_allocnonnull lhs_exp cnt_typ iter : prop =
  let id_new = create_fresh_primed_ident name_new in
  let exp_new = Var id_new in
  let ptsto_new = mk_ptsto_exp name_cnt (exp_new, cnt_typ, None) in
  let (lexp,strexp,typ,offlist) = match prop_iter_current iter with
    | (Hpointsto(lexp,strexp,Sizeof typ),Some offlist) -> (lexp,strexp,typ,offlist)
    | _ -> assert false in
  let strexp_old_updated = ptsto_update (lexp,strexp,typ) offlist exp_new in
  let ptsto_old_updated = mk_ptsto lexp strexp_old_updated (Sizeof typ) in
  let iter' = prop_iter_update_current_by_list iter [ptsto_old_updated;ptsto_new] in
  let prop' = prop_iter_to_prop iter'
  in if !Config.splitting_fields_level>0 then prop_extend_all_structs kprimed prop'
    else prop'


let execute_allocnull lhs_exp cnt_typ acc iter : prop list =
  let id_new = create_fresh_primed_ident name_new in
  let exp_new = Var id_new in
  let ptsto_new = mk_ptsto_exp name_cnt (exp_new, cnt_typ, None) in
  let (lexp,strexp,typ,offlist) = match prop_iter_current iter with
    | (Hpointsto(lexp,strexp,Sizeof typ),Some offlist) -> (lexp,strexp,typ,offlist)
    | _ -> assert false in
  let strexp_old_updated1 = ptsto_update (lexp,strexp,typ) offlist exp_new in
  let strexp_old_updated2 = ptsto_update (lexp,strexp,typ) offlist (Const_int 0) in
  let ptsto_old_updated1 = mk_ptsto lexp strexp_old_updated1 (Sizeof typ) in
  let ptsto_old_updated2 = mk_ptsto lexp strexp_old_updated2 (Sizeof typ) in
  let iter1 = prop_iter_update_current_by_list iter [ptsto_old_updated1;ptsto_new] in
  let iter2 = prop_iter_update_current_by_list iter [ptsto_old_updated2] in
  let props = (prop_iter_to_prop iter1) :: (prop_iter_to_prop iter2) :: acc 
  in (* if !Config.footprint_analysis then List.map prop_extend_struct_values_primed props
    else *) props

let execute_free iter = 
  let _ = match prop_iter_current iter with
    | (Hpointsto _, Some []) -> ()
    | (Hpointsto _, Some (o::os)) -> assert false (* alignment error *)
    | _ -> assert false (* should not happen *) 
  in prop_iter_remove_curr_then_to_prop iter

let () = Cfg_new.add_reserved_functions ["malloc";"free";"mallocnonnull";"mallocarray";"exit"]

let name_malloc = string_to_name "malloc"

let name_mallocnonnull = string_to_name "mallocnonnull"

let name_mallocarray = string_to_name "mallocarray"

let name_free = string_to_name "free"

let name_exit = string_to_name "exit"

let name___undo_join = string_to_name "__undo_join"

let name___stop = string_to_name "__stop"

let () = Cfg_new.add_reserved_functions ["__debug_on";"__undo_join";"__stop"]

let rec execute_nullify_se se = match se with
  | Eexp _ -> Eexp (Const_int 0)
  | Estruct fsel ->
      Estruct (List.map (fun (f,se') -> (f,execute_nullify_se se')) fsel)
  | Earray (size,esel) ->
      Earray (size,List.map (fun (e,se') -> (e,execute_nullify_se se')) esel)

(** Execute [instr] with a symbolic heap [prop].*)
let _sym_exec instr (prop:prop) =
  match instr with
    | Letderef (id,rhs_exp,typ,loc) ->
        (try
           let iter_list = rearrange rhs_exp typ prop 
           in List.map (execute_letderef id rhs_exp) iter_list
         with ARRAY_ACCESS ->
           if (!Config.array_level = 0) then assert false 
           else 
             let undef = Sil.exp_get_undefined () in
             [conjoin_eq (Var id) undef prop]) 
    | Set (lhs_exp,typ,rhs_exp,loc) ->
        (try 
           let iter_list = rearrange lhs_exp typ prop 
	   in List.map (execute_set lhs_exp rhs_exp) iter_list
         with ARRAY_ACCESS ->
           if (!Config.array_level = 0) then assert false 
           else [prop])
    | Nullify (pvar,loc) ->
	(match List.partition
	    (function | Hpointsto (Lvar pvar',_,_) -> pvar_equal pvar pvar'
	      | _ -> false) (prop_get_sigma prop) with
	    | [Hpointsto(e,se,typ)],sigma' ->
		let se' = execute_nullify_se se in
		let sigma'' = Hpointsto(e,se',typ)::sigma' in
		let prop' = prop_replace_sigma sigma'' prop
		in [prop']
	    | _ -> assert false)
    | Call (Some (lhs_exp,_,root_t), Const_fun fn, [size_exp,_],loc) 
      when name_equal fn name_mallocnonnull ->  (try
	  let cnt_te = match size_exp with
	    | Sizeof t ->
		E.d_strln "mallocnonnull called";
		size_exp
	    | BinOp(Cil.Mult, (Sizeof _ as size_exp'), _) ->
		E.d_str "WARNING: mallocnonnull called with: "; Sil.d_texp_full size_exp; E.d_str " "; Sil.d_loc loc; E.d_ln ();
	        size_exp'
		(* Sizeof Tvoid *)
	    | _ ->
		E.d_str "WARNING: mallocnonnull called with "; Sil.d_texp_full size_exp;
		E.d_str "instead of sizeof "; Sil.d_loc loc; E.d_ln ();
		size_exp in
	   let iter_list = rearrange lhs_exp root_t prop 
	   in List.map (execute_allocnonnull lhs_exp cnt_te) iter_list
         with ARRAY_ACCESS ->
           if (!Config.array_level = 0) then assert false 
           else
             E.d_strln ".... Array containing allocated heap cells ...";
             E.d_str "  Instr: "; Sil.d_instr instr; E.d_ln ();
             E.d_str "  PROP: "; Prop.d_prop prop; E.d_ln ();
             assert false)
    | Call (Some (lhs_exp,_,root_t),  Const_fun fn, [size_exp,_],loc) 
      when name_equal fn name_malloc ->
        (try
	  let cnt_te = match size_exp with
	    | Sizeof t ->
		size_exp
	    | BinOp(Cil.Mult, (Sizeof _ as size_exp'), _) ->
		E.d_str "WARNING: malloc called with: "; Sil.d_texp_full size_exp; E.d_str " "; Sil.d_loc loc; E.d_ln ();
		size_exp'
		(* Sizeof Tvoid *)
	    | _ ->
		E.d_str "WARNING: malloc called with "; Sil.d_texp_full size_exp; E.d_str "instead of sizeof "; Sil.d_loc loc; E.d_ln ();
		size_exp in
	   let iter_list = rearrange lhs_exp root_t prop 
	   in List.rev (List.fold_left (execute_allocnull lhs_exp cnt_te) [] iter_list)
         with ARRAY_ACCESS ->
           if (!Config.array_level = 0) then assert false 
           else 
             E.d_strln ".... Array containing allocated heap cells ...";
             E.d_str "  Instr: "; Sil.d_instr instr; E.d_ln ();
             E.d_str "  PROP: "; Prop.d_prop prop; E.d_ln ();
             assert false)
    | Call (Some (lhs_exp,Tptr(cnt_typ),root_t),  Const_fun fn, [(size_exp,typ)],loc) 
      when name_equal fn name_mallocarray ->
      (* Hongseok's comment: This part is buggy. Tptr is problematic. *)
        (try
	   let iter_list = rearrange lhs_exp root_t prop in
           let typ = match (Prop.exp_normalize_prop prop size_exp) with
             | Const_int size -> Tarray(cnt_typ, size)
             | _ -> 
                 E.d_strln ".... Array Allocation with Nonconstants ....";
                 E.d_str "  Instr: "; Sil.d_instr instr; E.d_ln ();
                 E.d_str "  PROP: "; Prop.d_prop prop; E.d_ln ();
                 assert false in
           List.map (execute_allocnonnull lhs_exp (Sizeof typ)) iter_list
         with ARRAY_ACCESS ->
           if (!Config.array_level = 0) then assert false 
           else 
             E.d_strln ".... Array containing allocated heap cells ...";
             E.d_str "  Instr: "; Sil.d_instr instr; E.d_ln ();
             E.d_str "  PROP: "; Prop.d_prop prop; E.d_ln ();
             assert false)
    | Call (None,  Const_fun fn, [(lexp,typ)],loc) 
      when name_equal fn name_free ->
        (try
           begin 
             match is_root prop lexp lexp with
	     | None -> 
                 E.d_strln ".... Alignment Error: Freed a non root ...."; 
                 assert false 
             | Some _ ->
      	         List.map execute_free (rearrange lexp typ prop)
           end
         with ARRAY_ACCESS ->
           if (!Config.array_level = 0) then assert false 
           else 
             E.d_strln ".... Array containing allocated heap cells ...";
             E.d_str "  Instr: "; Sil.d_instr instr; E.d_ln ();
             E.d_str "  PROP: "; Prop.d_prop prop; E.d_ln ();
             raise Exn.Array_of_pointsto)
    | Call (None,  Const_fun fn, [(lexp,typ)],loc) 
      when name_equal fn name_exit ->
	[]
    | Call (None, Const_fun fn, [],loc) when name_equal fn name___undo_join ->
	Config.undo_join := true;
	[prop]
    | Call (None,  Const_fun fn, [],loc) when name_equal fn name___stop ->
	E.d_strln " Stopping at"; Prop.d_prop prop; E.d_ln ();
	assert false
    | Call (eto, Const_fun fn, actual_params, loc) ->
	if !Config.footprint_analysis
	then
	  let name_proc = Ident.name_to_string fn in
	  let pdesc =
	    try
	      Cfg_new.proc_name_to_proc_desc name_proc
	    with
	      | Not_found ->
		  E.stderr "ERROR: Can't find proc: %s@." name_proc;
		  raise Exn.Unknown_proc in
	  let remove_ret ret_name p =
	    let iter = match prop_iter_create p with
	      | None -> assert false
	      | Some iter -> iter in
	    let filter = function
	      | Hpointsto (Lvar pv,se,_) -> if pvar_equal pv ret_name then Some se else None
	      | _ -> None
	    in match prop_iter_find iter filter with
	      | None ->
		  E.d_str "@.@.ERROR: cannot find return variable (possibly call with function pointer) "; Sil.d_pvar ret_name; E.d_ln ();
		  E.d_strln "in"; Prop.d_prop p; E.d_ln ();
		  exp_get_undefined (),p
	      | Some iter_ret ->
		  let _,se_ret = prop_iter_current iter_ret in
		  let e_ret = match se_ret with
		    | Some(Eexp e_ret) -> e_ret
		    | _ -> assert false in
		  let p_without_ret = prop_iter_remove_curr_then_to_prop iter_ret
		  in (e_ret,p_without_ret) in
	  let ret_name = Cfg_new.proc_desc_get_cil_ret_var pdesc in
	  let epl = Tabulation.exe_function_call name_proc actual_params prop in
	  let exe_assign_return p0 =
	    let ret_e,p = remove_ret ret_name p0 in match eto with
	    | None -> [p]
	    | Some (lhs_exp,typ,_) ->
		(try 
		    let iter_list = rearrange lhs_exp typ p
		    in List.map (execute_set lhs_exp ret_e) iter_list
		  with ARRAY_ACCESS ->
		    if (!Config.array_level = 0) then assert false 
		    else [p])
	  in List.flatten (List.map exe_assign_return epl)
	else
	  [prop] (* treat unknown function calls as skip *)
    | Call _ -> [prop]

let instr_normalize instr prop = match instr with
  | Call (ret,exp,par,loc) ->
      let exp' = exp_normalize_prop prop exp
      in Call (ret,exp',par,loc)
  | _ -> instr 

let sym_exec instr (prop:prop) =
  let instr' = instr_normalize instr prop
  in
    Sil.d_instr_list [instr'];
    proplist2propset (_sym_exec instr' prop)

let rec prune_polarity positive (condition : exp) (pset : propset) = match condition with
  | Var _ | Lvar _ ->
      prune_polarity true (BinOp ((if positive then Cil.Ne else Cil.Eq), condition, Const_int 0)) pset
  | Const_int 0 ->
      propset_empty
  | Const_fun _ -> assert false
  | Const_int _ | Sizeof _ ->
      pset
  | Cast (_,condition') ->
      prune_polarity positive condition' pset
  | UnOp (Cil.LNot,condition') ->
      prune_polarity (not positive) condition' pset
  | UnOp _ ->
      assert false
  | BinOp (Cil.Eq, e1, e2) ->
      (* Hongseok's comment: there are possibly redundant consistency
	 checks. *)
      let f pset_cur prop = 
	let is_inconsistent = 
          if positive then check_disequal prop e1 e2
	  else check_equal prop e1 e2 
	in if is_inconsistent then pset_cur else 
	    let new_prop = 
              if positive then conjoin_eq ~footprint:(!Config.footprint) e1 e2 prop 
	      else conjoin_neq  ~footprint:(!Config.footprint) e1 e2 prop
	    in if check_inconsistency new_prop then pset_cur
	      else propset_add new_prop pset_cur
      in propset_fold f propset_empty pset 
  | BinOp (Cil.Ne, e1, e2) ->
      (* Hongseok's comment: there are possibly redundant consistency
	 checks. *)
      let f pset_cur prop = 
	let is_inconsistent = 
	  if positive then check_equal prop e1 e2 
	  else check_disequal prop e1 e2
	in if is_inconsistent then pset_cur else 
	    let new_prop = 
              if positive then conjoin_neq ~footprint:(!Config.footprint) e1 e2 prop
	      else conjoin_eq ~footprint:(!Config.footprint) e1 e2 prop
	    in if check_inconsistency new_prop then pset_cur
	      else propset_add new_prop pset_cur
      in propset_fold f propset_empty pset
  | BinOp (Cil.Ge, e1, e2) | BinOp (Cil.Le, e2, e1) ->
      (* Hongseok's comment: implements a very weak check. Use the fact that e1 < e2 => e1!=e2 *)
      let f pset_cur prop = 
	let is_inconsistent = (not positive) && (check_equal prop e1 e2) in 
        if is_inconsistent then pset_cur 
        else 
          let new_prop = 
            if positive then prop else conjoin_neq ~footprint:(!Config.footprint) e1 e2 prop in 
	  propset_add new_prop pset_cur 
      in
      propset_fold f propset_empty pset
  | BinOp (Cil.Gt, e1, e2) | BinOp (Cil.Lt, e2, e1) ->
      (* Hongseok's comment: implements a very weak check. Use the fact that e1 > e2 => e1!=e2 *)
      let f pset_cur prop = 
	let is_inconsistent = positive && (check_equal prop e1 e2) in 
        if is_inconsistent then pset_cur 
        else 
          let new_prop = 
            if not positive then prop else conjoin_neq ~footprint:(!Config.footprint) e1 e2 prop in 
	  propset_add new_prop pset_cur 
      in
      propset_fold f propset_empty pset
  | BinOp (Cil.LAnd, condition1, condition2) ->
      let pset1 = prune_polarity positive condition1 pset in
      let pset2 = prune_polarity positive condition2 pset
      in (if positive then propset_inter else propset_union) pset1 pset2
  | BinOp (Cil.LOr, condition1, condition2) ->
      let pset1 = prune_polarity positive condition1 pset in
      let pset2 = prune_polarity positive condition1 pset
      in (if positive then propset_union else propset_inter) pset1 pset2
  | BinOp _ ->
      pset
  | Lfield _ | Lindex _ ->
      pset

let prune condition pset = 
  let set_true = ref Propset.propset_empty in
  let set_unknown = ref Propset.propset_empty in
  let f p = 
    match Prop.exp_normalize_prop p condition with
    | Const_int 0 -> ()
    | Const_int _ -> set_true := Propset.propset_add p !set_true
    | _ -> set_unknown := Propset.propset_add p !set_unknown in
  Propset.propset_iter f pset;
  Propset.propset_union 
    !set_true   
    (prune_polarity true condition !set_unknown)

(** {2 Lifted Abstract Transfer Functions} *)

let lifted_exist_quantify ids pset =
  propset_map (exist_quantify ids) pset 

let lifted_sym_exec pset instr =
  let f pset1 p = propset_union (sym_exec instr p) pset1
  in propset_fold f propset_empty pset


