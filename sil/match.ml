(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

(** Functions for "Smart" Pattern Matching *)

open Ident
open Sil
open Prop

module F = Format
module E = Error.MyErr (struct let mode = Error.DEFAULT end)


let mem_idlist i l =
  List.exists (fun id -> ident_equal i id) l


(** Type for a hpred pattern. flag=false means that the implication 
    between hpreds is not considered, and flag=true means that it is 
    considered during pattern matching *)
type hpred_pat = {hpred : hpred; flag : bool}

let pp_hpat f hpat = 
  F.fprintf f "%a" pp_hpred hpat.hpred

let rec pp_hpat_list f = function
  | [] -> ()
  | [hpat] -> 
      F.fprintf f "%a" pp_hpat hpat
  | hpat::hpats -> 
      F.fprintf f "%a * %a" pp_hpat hpat pp_hpat_list hpats

(** Checks e1 = e2[sub ++ sub'] for some sub' with dom(sub') subseteq vars.
    Returns (sub++sub', vars-dom(sub')). *)
let rec exp_match e1 sub vars e2 : (subst * ident list) option = 
  let check_equal sub vars e1 e2 = 
    let e2_inst = exp_sub sub e2 
    in if (exp_equal e1 e2_inst) then Some(sub, vars) else None 
  in match e1,e2 with
    | _, Var id2 when (ident_is_primed id2 && mem_idlist id2 vars) ->
	let vars_new = List.filter (fun id -> not (ident_equal id id2)) vars in
	let sub_new = match (extend_sub sub id2 e1) with
	  | None -> assert false (* happens when vars contains the same variable twice. *)
	  | Some sub_new -> sub_new  
	in Some (sub_new, vars_new)
    | _, Var _ -> 
        check_equal sub vars e1 e2 
    | Var _, _ -> 
        None 
    | Const_int _, _ | _, Const_int _ -> 
        check_equal sub vars e1 e2
    | Const_fun _, _ | _, Const_fun _ -> 
        check_equal sub vars e1 e2
    | Sizeof _, _ | _, Sizeof _ ->
	check_equal sub vars e1 e2
    | Cast (t1,e1'), Cast (t2,e2') -> (* we are currently ignoring cast *) 
	exp_match e1' sub vars e2'
    | Cast _, _ | _, Cast _ ->
	None 
    | UnOp(o1,e1'), UnOp(o2,e2') when unop_equal o1 o2 -> 
        exp_match e1' sub vars e2'
    | UnOp _, _ | _, UnOp _ -> 
        None  (* Naive *)
    | BinOp(b1,e1',e1''),BinOp(b2,e2',e2'') when binop_equal b1 b2 ->
	(match exp_match e1' sub vars e2' with
	  | None -> None
	  | Some (sub', vars') -> exp_match e1'' sub' vars' e2'')
    | BinOp _, _ | _, BinOp _ ->
        None (* Naive *)
    | Lvar _,_ | _, Lvar _ -> 
        check_equal sub vars e1 e2
    | Lfield(e1',fld1),Lfield(e2',fld2) when (fld_equal fld1 fld2) ->
	exp_match e1' sub vars e2'
    | Lfield _, _ | _, Lfield _ -> 
        None
    | Lindex(base1,idx1), Lindex(base2,idx2) ->
	(match exp_match base1 sub vars base2 with
	  | None -> None
	  | Some (sub',vars') -> exp_match idx1 sub' vars' idx2)

let exp_list_match es1 sub vars es2 =
  let f res_acc (e1, e2) = match res_acc with
    | None -> None
    | Some (sub_acc, vars_leftover) -> exp_match e1 sub_acc vars_leftover e2 in
  let es_combined = try List.combine es1 es2 with Invalid_argument _ -> assert false in
  let es_match_res = List.fold_left f (Some (sub, vars)) es_combined 
  in es_match_res 

(** Checks sexp1 = sexp2[sub ++ sub'] for some sub' with dom(sub') subseteq vars.
    Returns (sub++sub', vars-dom(sub')). *)
(* Hongseok's comment: This function does not consider the fact that
 * the analyzer sometimes forgets fields of hpred. It can possibly cause
 * a problem. *)
let rec strexp_match sexp1 sub vars sexp2 : (subst * ident list) option = 
  match sexp1,sexp2 with
    | Eexp exp1, Eexp exp2 ->
	exp_match exp1 sub vars exp2
    | Eexp _, _ | _, Eexp _ -> 
        None
    | Estruct fel1, Estruct fel2 -> (* assume sorted w.r.t. fields *)
	fld_exp_list_match fel1 sub vars fel2
    | Estruct _, _ | _, Estruct _ -> 
        None
    | Earray (n1,iel1), Earray (n2,iel2) ->
	if n1=n2 
        then idx_exp_list_match iel1 sub vars iel2
	else None

(** Checks fel1 = fel2[sub ++ sub'] for some sub' with dom(sub') subseteq vars.
    Returns (sub++sub', vars-dom(sub')). *)
and fld_exp_list_match fel1 sub vars fel2 = 
  match fel1,fel2 with
    | [],[] -> 
	Some (sub, vars)
    | [], _ ->
        None
    | _, [] ->
	if (!Config.abs_struct > 0) then 
          Some (sub,vars) 
          (* Hongseok: This can lead to great information loss *)
        else
          None
    | (fld1,strexp1') :: fel1', (fld2,strexp2') :: fel2' ->
        let n = fld_compare fld1 fld2 in
	if (n = 0) then
          (match strexp_match strexp1' sub vars strexp2' with
	  | None -> None
	  | Some (sub',vars') -> fld_exp_list_match fel1' sub' vars' fel2')             
        else if (n < 0 && !Config.abs_struct > 0) then
          fld_exp_list_match fel1' sub vars fel2 
          (* Hongseok: This can lead to great information loss *)
        else 
          None 

(** Checks iel1 = iel2[sub ++ sub'] for some sub' with dom(sub') subseteq vars.
    Returns (sub++sub', vars-dom(sub')). *)
and idx_exp_list_match iel1 sub vars iel2 = 
  match iel1,iel2 with
    | [],[] -> 
        Some (sub, vars)
    | [],_ | _,[] ->
	None
    | (idx1,strexp1') :: iel1', (idx2,strexp2') :: iel2' -> 
	let idx2 = exp_sub sub idx2 in
	let sanity_check = not (List.exists (fun id -> ident_in_exp id idx2) vars) in 
        if not sanity_check then 
          begin
          E.err "@[.... Sanity Check Failure while Matching Index-Strexps ....@.";
          E.err "@[<4>    IDX1: %a, STREXP1: %a@." pp_exp idx1 pp_sexp strexp1';
          E.err "@[<4>    IDX2: %a, STREXP2: %a@\n@." pp_exp idx2 pp_sexp strexp2';
          assert false
          end
        else if not (exp_equal idx1 idx2) then 
          None
        else 
          (match strexp_match strexp1' sub vars strexp2' with
	  | None -> None
	  | Some (sub',vars') -> idx_exp_list_match iel1' sub' vars' iel2')


(* ddino: extends substitution sub by creating a new substitution for vars *)
let sub_extend_with_ren (sub:subst) vars = (* assume that dom(sub) cap vars = emptyset *)
  let f id = (id, Var (create_fresh_primed_ident (ident_name id))) in
  let renaming_for_vars = sub_of_list (List.map f vars) 
  in sub_join sub renaming_for_vars
    

type sidecondition = prop -> subst -> bool

let rec execute_with_backtracking = function
  | [] -> None
  | [f] -> f ()
  | f::fs -> 
      let res_f = f () 
      in match res_f with
	| None -> execute_with_backtracking fs
	| Some _ -> res_f

let rec instantiate_to_emp p condition sub vars = function
  | [] -> if condition p sub then Some(sub, p) else None 
  | hpat::hpats -> 
      if not hpat.flag then None 
      else match hpat.hpred with
	| Hpointsto _ | Hlseg (Lseg_NE,_,_,_,_) | Hdllseg (Lseg_NE,_,_,_,_,_,_) -> None
	| Hlseg (k,_,e1,e2,_) ->
	    let fully_instantiated = not (List.exists (fun id -> ident_in_exp id e1) vars) 
	    in if (not fully_instantiated) then None else 
		let e1' = exp_sub sub e1
		in begin
		  match exp_match e1' sub vars e2 with
		    | None -> None  
		    | Some (sub_new, vars_leftover) -> 
			instantiate_to_emp p condition sub_new vars_leftover hpats 
		end
	| Hdllseg (k,_,iF,oB,oF,iB,_) ->
	    let fully_instantiated = 
	      not (List.exists (fun id -> ident_in_exp id iF || ident_in_exp id oB) vars) 
	    in if (not fully_instantiated) then None else 
		let iF' = exp_sub sub iF in
		let oB' = exp_sub sub oB 
		in match exp_list_match [iF';oB'] sub vars [oF;iB] with
		  | None -> None  
		  | Some (sub_new, vars_leftover) -> 
		      instantiate_to_emp p condition sub_new vars_leftover hpats 


(* Hongseok's comment: This function has to be changed in order to
 * implement the idea "All lsegs outside are NE, and all lsegs inside
 * are PE" *)
let rec iter_match_with_impl iter condition sub vars hpat hpats =

  (*
  E.log "@[.... iter_match_with_impl ....@.";
  E.log "@[<4>  sub: %a@\n@." pp_sub sub;
  E.log "@[<4>  PROP: %a@\n@." pp_prop (prop_iter_to_prop iter);
  E.log "@[<4>  hpred: %a@\n@." pp_hpat hpat;
  E.log "@[<4>  hpred_rest: %a@\n@." pp_hpat_list hpats;
  *)

  let do_next iter_cur _ = match prop_iter_next iter_cur with 
    | None -> None
    | Some iter_next -> iter_match_with_impl iter_next condition sub vars hpat hpats 
  in
  let do_empty_hpats iter_cur _ = 
    let (sub_new, vars_leftover) = match prop_iter_current iter_cur with 
      | _, None -> assert false 
      | _, Some (sub_new, vars_leftover) -> (sub_new, vars_leftover) in
    let sub_res = sub_extend_with_ren sub_new vars_leftover in
    let p_leftover = prop_iter_remove_curr_then_to_prop iter_cur in 
    (*
    E.log "@[.... iter_match_with_impl (final condtion check) ....@\n@.";
    E.log "@[<4>  sub_res : %a@\n@." pp_sub sub_res;
    E.log "@[<4>  p_leftover : %a@\n@." pp_prop p_leftover;
    *)
    if condition p_leftover sub_res then Some (sub_res, p_leftover) else None 
  in
  let do_nonempty_hpats iter_cur _ = 
    let (sub_new, vars_leftover) = match prop_iter_current iter_cur with
      | _, None -> assert false 
      | _, Some (sub_new, vars_leftover) -> (sub_new, vars_leftover) in
    let (hpat_next, hpats_rest) = match hpats with
      | [] -> assert false
      | hpat_next :: hpats_rest -> (hpat_next, hpats_rest) in
    let p_rest = prop_iter_remove_curr_then_to_prop iter_cur  
    in prop_match_with_impl_sub p_rest condition sub_new vars_leftover hpat_next hpats_rest 
  in 
  let gen_filter_pointsto lexp2 strexp2 te2 = function
    | Hpointsto (lexp1,strexp1,te1) when exp_equal te1 te2 ->
	(match (exp_match lexp1 sub vars lexp2) with
	  | None -> None 
	  | Some (sub', vars_leftover) -> strexp_match strexp1 sub' vars_leftover strexp2)
    | _ -> None 
  in
  let gen_filter_lseg k2 para2 e_start2 e_end2 es_shared2 = function
    | Hpointsto _ -> None
    | Hlseg (k1,para1,e_start1,e_end1,es_shared1) ->
        let do_kinds_match = match k1, k2 with
	  | Lseg_NE, Lseg_NE | Lseg_NE, Lseg_PE | Lseg_PE, Lseg_PE -> true
	  | Lseg_PE, Lseg_NE -> false in
        (* let do_paras_match = hpara_match_with_impl hpat.flag para1 para2 *)
        let do_paras_match = hpara_match_with_impl true para1 para2 
	in if not (do_kinds_match && do_paras_match) then None 
	  else 
	    let es1 = [e_start1;e_end1]@es_shared1 in
	    let es2 = [e_start2;e_end2]@es_shared2
	    in exp_list_match es1 sub vars es2 
    | Hdllseg _ -> None
  in 
  let gen_filter_dllseg k2 para2 iF2 oB2 oF2 iB2 es_shared2 = function
    | Hpointsto _ | Hlseg _ -> None
    | Hdllseg (k1,para1,iF1,oB1,oF1,iB1,es_shared1) ->
        let do_kinds_match = match k1, k2 with
	  | Lseg_NE, Lseg_NE | Lseg_NE, Lseg_PE | Lseg_PE, Lseg_PE -> true
	  | Lseg_PE, Lseg_NE -> false in
        (* let do_paras_match = hpara_dll_match_with_impl hpat.flag para1 para2 *)
        let do_paras_match = hpara_dll_match_with_impl true para1 para2 
	in if not (do_kinds_match && do_paras_match) then None
	  else 
 	    let es1 = [iF1;oB1;oF1;iB1]@es_shared1 in
	    let es2 = [iF2;oB2;oF2;iB2]@es_shared2
 	    in exp_list_match es1 sub vars es2 	
	      
  in match hpat.hpred with
    | Hpointsto (lexp2,strexp2,te2) ->
	let filter = gen_filter_pointsto lexp2 strexp2 te2 
	in begin match (prop_iter_find iter filter), hpats with
	  | (None, _) -> None
	  | (Some iter_cur, []) -> 
	      do_empty_hpats iter_cur ()
	  | (Some iter_cur, _) -> 
	      execute_with_backtracking [do_nonempty_hpats iter_cur; do_next iter_cur]
	end
    | Hlseg (k2,para2,e_start2,e_end2,es_shared2) -> 
	let filter = gen_filter_lseg k2 para2 e_start2 e_end2 es_shared2 in
	let do_emp_lseg _ =
	  let fully_instantiated_start2 = not (List.exists (fun id -> ident_in_exp id e_start2) vars) in 
          if (not fully_instantiated_start2) then None 
          else 
	    let e_start2' = exp_sub sub e_start2 in 
            match (exp_match e_start2' sub vars e_end2, hpats) with
	    | None, _ -> 
                (*
                E.log "@.... iter_match_with_impl (empty_case, fail) ....@\n@."; 
                E.log "@[<4>  sub: %a@\n@." pp_sub sub;
                E.log "@[<4>  e_start2': %a@\n@." pp_exp e_start2';
                E.log "@[<4>  e_end2: %a@\n@." pp_exp e_end2;
                *)
                None  
	    | Some (sub_new, vars_leftover), [] -> 
	        let sub_res = sub_extend_with_ren sub_new vars_leftover in
	        let p_leftover = prop_iter_to_prop iter in 
                if condition p_leftover sub_res then Some(sub_res, p_leftover) else None 
            | Some (sub_new, vars_leftover), hpat_next::hpats_rest -> 
	        let p = prop_iter_to_prop iter in 
                prop_match_with_impl_sub p condition sub_new vars_leftover hpat_next hpats_rest in
	let do_para_lseg _ =
	  let (para2_exist_vars,para2_inst) = hpara_instantiate para2 e_start2 e_end2 es_shared2 in
 	  (* let allow_impl hpred = {hpred=hpred; flag=hpat.flag} in *)
 	  let allow_impl hpred = {hpred=hpred; flag=true} in 
	  let (para2_hpat, para2_hpats) = match List.map allow_impl para2_inst with
	    | [] -> assert false (* the body of a parameter should contain at least one * conjunct *)
	    | para2_pat :: para2_pats -> (para2_pat, para2_pats) in
	  let new_vars = para2_exist_vars @ vars in
	  let new_hpats = para2_hpats @ hpats 
	  in match (iter_match_with_impl iter condition sub new_vars para2_hpat new_hpats) with
	    | None -> None
	    | Some (sub_res, p_leftover) when condition p_leftover sub_res ->
		let not_in_para2_exist_vars id = 
		  not (List.exists (fun id' -> ident_equal id id') para2_exist_vars) in
		let sub_res' = sub_filter not_in_para2_exist_vars sub_res
		in Some (sub_res', p_leftover) 
	    | Some _ -> None
	in begin match ((prop_iter_find iter filter), hpats) with
	  | (None, _) when not hpat.flag -> 
              (* E.log "@[.... iter_match_with_impl (lseg not-matched) ....@\n@."; *)
              None
	  | (None, _) when lseg_kind_equal k2 Lseg_NE -> 
              (* E.log "@[.... iter_match_with_impl (lseg not-matched) ....@\n@."; *)
              do_para_lseg ()
	  | (None, _) -> 
              (* E.log "@[.... iter_match_with_impl (lseg not-matched) ....@\n@."; *)
              execute_with_backtracking [do_emp_lseg; do_para_lseg]
	  | (Some iter_cur, []) -> 
              (* E.log "@[.... iter_match_with_impl (lseg matched) ....@\n@."; *)
              do_empty_hpats iter_cur ()
	  | (Some iter_cur, _) -> 
              (* E.log "@[.... iter_match_with_impl (lseg matched) ....@\n@."; *)
              execute_with_backtracking [do_nonempty_hpats iter_cur; do_next iter_cur]
	end
    | Hdllseg (k2,para2,iF2,oB2,oF2,iB2,es_shared2) -> 
	let filter = gen_filter_dllseg k2 para2 iF2 oB2 oF2 iB2 es_shared2 in
	let do_emp_dllseg _ =
	  let fully_instantiated_iFoB2 = 
            not (List.exists (fun id -> ident_in_exp id iF2 || ident_in_exp id oB2) vars) 
	  in if (not fully_instantiated_iFoB2) then None else 
	      let iF2' = exp_sub sub iF2 in
	      let oB2' = exp_sub sub oB2 
	      in match (exp_list_match [iF2';oB2'] sub vars [oF2;iB2], hpats) with
		| None, _ -> None  
		| Some (sub_new, vars_leftover), [] -> 
		    let sub_res = sub_extend_with_ren sub_new vars_leftover in
		    let p_leftover = prop_iter_to_prop iter 
		    in if condition p_leftover sub_res then Some(sub_res, p_leftover) else None 
		| Some (sub_new, vars_leftover), hpat_next::hpats_rest -> 
		    let p = prop_iter_to_prop iter 
		    in prop_match_with_impl_sub p condition sub_new vars_leftover hpat_next hpats_rest in
	let do_para_dllseg _ =
	  let fully_instantiated_iF2 = not (List.exists (fun id -> ident_in_exp id iF2) vars) 
	  in if (not fully_instantiated_iF2) then None else 
	      let iF2' = exp_sub sub iF2
	      in match exp_match iF2' sub vars iB2 with
		| None -> None
		| Some (sub_new, vars_leftover) ->
		    let (para2_exist_vars,para2_inst) = hpara_dll_instantiate para2 iF2 oB2 oF2 es_shared2 in
		    (* let allow_impl hpred = {hpred=hpred; flag=hpat.flag} in *)
		    let allow_impl hpred = {hpred=hpred; flag=true} in 
		    let (para2_hpat, para2_hpats) = match List.map allow_impl para2_inst with
		      | [] -> assert false (* the body of a parameter should contain at least one * conjunct *)
		      | para2_pat :: para2_pats -> (para2_pat, para2_pats) in
		    let new_vars = para2_exist_vars @ vars_leftover in
		    let new_hpats = para2_hpats @ hpats 
		    in match (iter_match_with_impl iter condition sub_new new_vars para2_hpat new_hpats) with
		      | None -> None
		      | Some (sub_res, p_leftover) when condition p_leftover sub_res ->
			  let not_in_para2_exist_vars id = 
			    not (List.exists (fun id' -> ident_equal id id') para2_exist_vars) in
			  let sub_res' = sub_filter not_in_para2_exist_vars sub_res
			  in Some (sub_res', p_leftover) 
		      | Some _ -> None
	in begin match ((prop_iter_find iter filter), hpats) with
	  | (None, _) when not hpat.flag -> None
	  | (None, _) when lseg_kind_equal k2 Lseg_NE -> do_para_dllseg ()
	  | (None, _) -> execute_with_backtracking [do_emp_dllseg; do_para_dllseg]
	  | (Some iter_cur, []) -> do_empty_hpats iter_cur ()
	  | (Some iter_cur, _) -> execute_with_backtracking [do_nonempty_hpats iter_cur; do_next iter_cur]
	end 

and prop_match_with_impl_sub p condition sub vars hpat hpats  = 

  (*
  E.log "@[.... prop_match_with_impl_sub ....@.";
  E.log "@[<4>  sub: %a@\n@." pp_sub sub;
  E.log "@[<4>  PROP: %a@\n@." pp_prop p;
  E.log "@[<4>  hpat: %a@\n@." pp_hpat hpat;
  E.log "@[<4>  hpred_rest: %a@\n@." pp_hpat_list hpats;
  *)

  match prop_iter_create p with
  | None ->
      instantiate_to_emp p condition sub vars (hpat::hpats)
  | Some iter -> 
      iter_match_with_impl iter condition sub vars hpat hpats

and hpara_common_match_with_impl impl_ok ids1 sigma1 eids2 ids2 sigma2 =
  try 
    let sub_ids = 
      let ren_ids = List.combine ids2 ids1 in
      let f (id2,id1) = (id2, Var id1) 
      in List.map f ren_ids in
    let (sub_eids, eids_fresh) = 
      let f id = (id, create_fresh_primed_ident (ident_name id)) in
      let ren_eids = List.map f eids2 in
      let eids_fresh = List.map snd ren_eids in
      let sub_eids = List.map (fun (id2,id1) -> (id2,Var id1)) ren_eids
      in (sub_eids, eids_fresh) in
    let sub = sub_of_list (sub_ids @ sub_eids) in
    let (hpred2_ren, sigma2_ren) = match sigma2 with
      | [] -> assert false (* currently, we assume that para2 is not emp *)
      | hpred2 :: sigma2 -> (hpred_sub sub hpred2, sigma_sub sub sigma2) in
    let (hpat2, hpats2) = 
      let allow_impl hpred = {hpred=hpred; flag=impl_ok}
      in (allow_impl hpred2_ren, List.map allow_impl sigma2_ren) in 
    let condition _ _ = true in
    let p1 = prop_sigma_star prop_emp sigma1 in 
    begin
      match (prop_match_with_impl_sub p1 condition sub_empty eids_fresh hpat2 hpats2) with
      | None -> false
      | Some (_, p1') when Prop.prop_is_emp p1' -> true
      | _ -> false
    end

  with Invalid_argument _ -> false

and hpara_match_with_impl impl_ok para1 para2 : bool = 

  (*
  E.log "@[.... hpara_match_with_impl_sub ....@.";
  E.log "@[<4>  HPARA1: %a@\n@." pp_hpara para1;
  E.log "@[<4>  HPARA2: %a@\n@." pp_hpara para2;
  *)

  let ids1 = para1.root :: para1.next :: para1.svars in
  let ids2 = para2.root :: para2.next :: para2.svars in
  let eids2 = para2.evars
  in hpara_common_match_with_impl impl_ok ids1 para1.body eids2 ids2 para2.body 

and hpara_dll_match_with_impl impl_ok para1 para2 : bool = 

  (*
  E.log "@[.... hpara_dll_match_with_impl_sub ....@.";
  E.log "@[<4>  HPARA1: %a@\n@." pp_dll_hpara para1;
  E.log "@[<4>  HPARA2: %a@\n@." pp_dll_hpara para2;
  *)

  let ids1 = para1.cell :: para1.blink :: para1.flink :: para1.svars_dll in
  let ids2 = para2.cell :: para2.blink :: para2.flink :: para2.svars_dll in
  let eids2 = para2.evars_dll
  in hpara_common_match_with_impl impl_ok ids1 para1.body_dll eids2 ids2 para2.body_dll

(** [prop_match_with_impl p condition vars hpat hpats]
    returns [(subst,p_leftover)] such that 
    1) [dom(subst) = vars]
    2) [p |- (hpat.hpred * hpats.hpred)[subst] * p_leftover].
    Using the flag [field], we can control the strength of |-. *) 
let prop_match_with_impl p condition vars hpat hpats =
  prop_match_with_impl_sub p condition sub_empty vars hpat hpats 
  (*
  E.log "@[.... Match (Starting Point) ....@.";
  E.log "@[<4>  PROP: %a@\n@." pp_prop p;
  E.log "@[<4>  hpat: %a@\n@." pp_hpat hpat;
  E.log "@[<4>  hpats: %a@\n@." pp_hpat_list hpats;
  let res = prop_match_with_impl_sub p condition sub_empty vars hpat hpats in
  match res with
  | None ->
      E.log "@[.... Match (RES: FAIL) ....@\n@."; 
      res 
  | Some _ -> 
      E.log "@[.... Match (RES: SUCCESS) ....@\n@."; 
      res 
  *)





