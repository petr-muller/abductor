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

open Cfg_new
open Ident
open Sil
open Prop
open Propset
open Prover
open Match

module F = Format
module Exn = Exceptions
module E = Error.MyErr (struct let mode = Error.DEFAULT end)


(** {2 Abstraction} *)

type rule = 
    {r_vars: ident list;
     r_root: hpred_pat; 
     r_sigma: hpred_pat list; (* sigma should be in a specific order *)
     r_new_sigma: hpred list;
     r_new_pi: prop -> prop -> subst -> atom list;
     r_condition: prop -> subst -> bool}

let sigma_rewrite p r = 
  match (prop_match_with_impl p r.r_condition r.r_vars r.r_root r.r_sigma) with
  | None -> None 
  | Some(sub, p_leftover) ->
      if not (r.r_condition p_leftover sub) then None
(*
        let res_pi = r.r_new_pi p p_leftover sub in
        let res_sigma = sigma_sub sub r.r_new_sigma in
	let p_with_res_pi = List.fold_left prop_atom_and p_leftover res_pi in
	let p_new = prop_sigma_star p_with_res_pi res_sigma in 
        begin
          E.log "@[.... abstraction (condition failure) ....@.";
          E.log "@[<4>  SIGMA: %a@\n@." pp_sigma res_sigma;
          E.log "@[<4>  OTHER: %a@\n@." pp_prop p_leftover;
          E.log "@[<4>  RES: %a@\n@." pp_prop p_new;
          None
        end
*)
      else
        let res_pi = r.r_new_pi p p_leftover sub in
        let res_sigma = sigma_sub sub r.r_new_sigma in
	let p_with_res_pi = List.fold_left prop_atom_and p_leftover res_pi in
	let p_new = prop_sigma_star p_with_res_pi res_sigma in 
        Some p_new

let name_rule = name_siltmp

let list_intersect compare l1 l2 =
  let l1_sorted = List.sort compare l1 in
  let l2_sorted = List.sort compare l2 in
  let rec f l1 l2 = match l1, l2 with
    | ([],_) | (_,[]) -> false
    | (x1::l1', x2::l2') -> 
	let x_comparison = compare x1 x2
	in if x_comparison = 0 then true
	  else if x_comparison < 0 then f l1' l2
	  else f l1 l2'
  in f l1_sorted l2_sorted

let list_is_empty = function
  | [] -> true
  | _ -> false

let exp_fav_list e =
  fav_to_list (exp_fav e)

let sigma_fav_list sigma =
  fav_to_list (sigma_fav sigma)

let sigma_fav_in_pvars =
  fav_imperative_to_functional sigma_fav_in_pvars_add

let sigma_fav_in_pvars_list sigma =
  fav_to_list (sigma_fav_in_pvars sigma)




(* ================ Start of SLL abstraction rules  ================ *)

let create_fresh_primed_idents_ls para =
  let id_base = create_fresh_primed_ident name_rule in
  let id_next = create_fresh_primed_ident name_rule in
  let id_end = create_fresh_primed_ident name_rule in
  let ids_shared =
    let svars = para.svars in
    let f id = create_fresh_primed_ident (ident_name id) 
    in List.map f svars in
  let ids_tuple = (id_base,id_next,id_end,ids_shared) in
  let exp_base = Var id_base in
  let exp_next = Var id_next in
  let exp_end = Var id_end in 
  let exps_shared = List.map (fun id -> Var id) ids_shared in
  let exps_tuple = (exp_base,exp_next,exp_end,exps_shared) 
  in (ids_tuple, exps_tuple)

let create_condition_ls ids_private id_base p_leftover (inst:subst) =
  let (insts_of_private_ids, insts_of_public_ids, inst_of_base) =
    let f id' = List.exists (fun id'' -> ident_equal id' id'') ids_private in
    let (inst_private,inst_public) = sub_domain_partition f inst in
    let insts_of_public_ids = sub_range inst_public in
    let inst_of_base = try sub_find (ident_equal id_base) inst_public with _ -> assert false in
    let insts_of_private_ids = sub_range inst_private 
    in (insts_of_private_ids, insts_of_public_ids, inst_of_base) in
  let fav_insts_of_public_ids = List.flatten (List.map exp_fav_list insts_of_public_ids) in
  let fav_insts_of_private_ids = List.flatten (List.map exp_fav_list insts_of_private_ids) in
  let (fav_p_leftover,fav_in_pvars) = 
    let sigma = prop_get_sigma p_leftover 
    in (sigma_fav_list sigma, sigma_fav_in_pvars_list sigma) in
  let fpv_inst_of_base = exp_fpv inst_of_base in
  let fpv_insts_of_private_ids = List.flatten (List.map exp_fpv insts_of_private_ids) in 
(*
  let fav_inst_of_base = exp_fav_list inst_of_base in
  E.log "@[.... application of condition ....@\n@.";    
  E.log "@[<4>  private ids : %a@\n@." pp_exp_list insts_of_private_ids;
  E.log "@[<4>  public ids : %a@\n@." pp_exp_list insts_of_public_ids;
*)
  (* (not (list_intersect ident_compare fav_inst_of_base fav_in_pvars)) && *)
  (list_is_empty fpv_inst_of_base) &&
  (list_is_empty fpv_insts_of_private_ids) && 
  (not (List.exists Ident.ident_is_normal fav_insts_of_private_ids)) && 
  (not (list_intersect ident_compare fav_insts_of_private_ids fav_p_leftover)) && 
  (not (list_intersect ident_compare fav_insts_of_private_ids fav_insts_of_public_ids)) 

let mk_rule_ptspts_ls impl_ok1 impl_ok2 (para: hpara) = 
  let (ids_tuple, exps_tuple) = create_fresh_primed_idents_ls para in
  let (id_base, id_next, id_end, ids_shared) = ids_tuple in
  let (exp_base, exp_next, exp_end, exps_shared) = exps_tuple in
  let (ids_exist_fst, para_fst) = hpara_instantiate para exp_base exp_next exps_shared in
  let (para_fst_start, para_fst_rest) = 
    let mark_impl_flag hpred = {hpred=hpred; flag=impl_ok1} in  
      match para_fst with
	| [] -> E.err "@.@.ERROR (Empty Para): %a @.@." pp_hpara para; assert false
	| hpred :: hpreds ->
	    let hpat = mark_impl_flag hpred in
	    let hpats = List.map mark_impl_flag hpreds
	    in (hpat, hpats) in
  let (ids_exist_snd, para_snd) =  
    let mark_impl_flag hpred = {hpred=hpred; flag=impl_ok2} in
    let (ids, para_body) = hpara_instantiate para exp_next exp_end exps_shared in
    let para_body_hpats = List.map mark_impl_flag para_body 
    in (ids, para_body_hpats) in 
  let lseg_res = mk_lseg Lseg_NE para exp_base exp_end exps_shared in 
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition = 
    let ids_private = id_next :: (ids_exist_fst @ ids_exist_snd) 
    in create_condition_ls ids_private id_base 
  in 
    {r_vars = id_base :: id_next :: id_end :: ids_shared @ ids_exist_fst @ ids_exist_snd;
     r_root = para_fst_start;
     r_sigma = para_fst_rest @ para_snd;
     r_new_sigma = [lseg_res];
     r_new_pi = gen_pi_res;
     r_condition = condition}
    
let mk_rule_ptsls_ls k2 impl_ok1 impl_ok2 para =   
  let (ids_tuple, exps_tuple) = create_fresh_primed_idents_ls para in
  let (id_base, id_next, id_end, ids_shared) = ids_tuple in
  let (exp_base, exp_next, exp_end, exps_shared) = exps_tuple in
  let (ids_exist, para_inst) = hpara_instantiate para exp_base exp_next exps_shared in  
  let (para_inst_start, para_inst_rest) = 
    match para_inst with
      | [] -> E.err "@.@.ERROR (Empty Para): %a @.@." pp_hpara para; assert false
      | hpred :: hpreds -> 
	  let allow_impl hpred = {hpred=hpred; flag=impl_ok1} 
          in (allow_impl hpred, List.map allow_impl hpreds) in 
  let lseg_pat = {hpred = mk_lseg k2 para exp_next exp_end exps_shared; flag = impl_ok2} in
  let lseg_res = mk_lseg Lseg_NE para exp_base exp_end exps_shared in 
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition =
    let ids_private = id_next :: ids_exist 
    in create_condition_ls ids_private id_base 
  in 
    {r_vars = id_base :: id_next :: id_end :: ids_shared @ ids_exist;
     r_root = para_inst_start;
     r_sigma = para_inst_rest @ [lseg_pat];
     r_new_pi = gen_pi_res;
     r_new_sigma = [lseg_res];
     r_condition = condition}

let mk_rule_lspts_ls k1 impl_ok1 impl_ok2 para =
  let (ids_tuple, exps_tuple) = create_fresh_primed_idents_ls para in
  let (id_base, id_next, id_end, ids_shared) = ids_tuple in
  let (exp_base, exp_next, exp_end, exps_shared) = exps_tuple in
  let lseg_pat = {hpred=mk_lseg k1 para exp_base exp_next exps_shared; flag=impl_ok1} in
  let (ids_exist, para_inst_pat) = 
    let (ids, para_body) = hpara_instantiate para exp_next exp_end exps_shared in
    let allow_impl hpred = {hpred=hpred; flag=impl_ok2} in
    let para_body_pat = List.map allow_impl para_body
    in (ids, para_body_pat) in
  let lseg_res = mk_lseg Lseg_NE para exp_base exp_end exps_shared in  
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition =
    let ids_private = id_next :: ids_exist 
    in create_condition_ls ids_private id_base 
  in 
    {r_vars = id_base :: id_next :: id_end :: ids_shared @ ids_exist;
     r_root = lseg_pat;
     r_sigma = para_inst_pat;
     r_new_sigma = [lseg_res];
     r_new_pi = gen_pi_res;
     r_condition = condition}

let lseg_kind_add k1 k2 = match k1, k2 with 
  | Lseg_NE, Lseg_NE | Lseg_NE, Lseg_PE | Lseg_PE, Lseg_NE -> Lseg_NE
  | Lseg_PE, Lseg_PE -> Lseg_PE

let mk_rule_lsls_ls k1 k2 impl_ok1 impl_ok2 para = 
  let (ids_tuple, exps_tuple) = create_fresh_primed_idents_ls para in
  let (id_base, id_next, id_end, ids_shared) = ids_tuple in
  let (exp_base, exp_next, exp_end, exps_shared) = exps_tuple in
  let lseg_fst_pat = 
    {hpred = mk_lseg k1 para exp_base exp_next exps_shared; flag = impl_ok1} in
  let lseg_snd_pat = 
    {hpred = mk_lseg k2 para exp_next exp_end exps_shared; flag = impl_ok2} in
  let k_res = lseg_kind_add k1 k2 in
  let lseg_res = mk_lseg k_res para exp_base exp_end exps_shared in
  let gen_pi_res p_start p_leftover (inst:subst) = []
  (*
    let inst_base,inst_next,inst_end =
      let find x = sub_find (ident_equal x) inst 
      in try
	  (find id_base, find id_next, find id_end)
	with Not_found -> assert false in
    let spooky_case _ = 
      (lseg_kind_equal Lseg_PE k_res)
      && (check_allocatedness p_leftover inst_end)
      && ((check_disequal p_start inst_base inst_next) 
	   || (check_disequal p_start inst_next inst_end)) in
    let obvious_case _ = 
      check_disequal p_start inst_base inst_end &&
      not (check_disequal p_leftover inst_base inst_end)
    in if not (spooky_case () ||  obvious_case ()) then [] 
      else [Aneq(inst_base,inst_end)] 
  *)
  in
  let condition =
    let ids_private = [id_next] 
    in create_condition_ls ids_private id_base  
  in 
    {r_vars =id_base :: id_next :: id_end :: ids_shared ;
     r_root = lseg_fst_pat;
     r_sigma = [lseg_snd_pat];
     r_new_sigma = [lseg_res];
     r_new_pi = gen_pi_res;
     r_condition = condition}

let mk_rules_for_sll (para : hpara) : rule list = 
  if not !Config.nelseg then
  begin
    let pts_pts = mk_rule_ptspts_ls true true para in
    let pts_pels = mk_rule_ptsls_ls Lseg_PE true false para in
    let pels_pts = mk_rule_lspts_ls Lseg_PE false true para in 
    let pels_nels = mk_rule_lsls_ls Lseg_PE Lseg_NE false false para in
    let nels_pels = mk_rule_lsls_ls Lseg_NE Lseg_PE false false para in
    let pels_pels = mk_rule_lsls_ls Lseg_PE Lseg_PE false false para in 
    [pts_pts;pts_pels;pels_pts;pels_nels;nels_pels;pels_pels]
  end
  else 
  begin
    let pts_pts = mk_rule_ptspts_ls true true para in
    let pts_nels = mk_rule_ptsls_ls Lseg_NE true false para in
    let nels_pts = mk_rule_lspts_ls Lseg_NE false true para in 
    let nels_nels = mk_rule_lsls_ls Lseg_NE Lseg_NE false false para in 
    [pts_pts;pts_nels;nels_pts;nels_nels]
  end

(* =================  End of SLL abstraction rules  ================= *)




(* =================  Start of DLL abstraction rules  ================= *)

let name_dll_rule = name_siltmp

let create_condition_dll = create_condition_ls

let mk_rule_ptspts_dll impl_ok1 impl_ok2 para = 
  let id_iF = create_fresh_primed_ident name_dll_rule in
  let id_iF' = create_fresh_primed_ident name_dll_rule in
  let id_oB = create_fresh_primed_ident name_dll_rule in
  let id_oF = create_fresh_primed_ident name_dll_rule in
  let ids_shared =
    let svars = para.svars_dll in
    let f id = create_fresh_primed_ident (ident_name id) 
    in List.map f svars in
  let exp_iF = Var id_iF in
  let exp_iF' = Var id_iF' in
  let exp_oB = Var id_oB in 
  let exp_oF = Var id_oF in
  let exps_shared = List.map (fun id -> Var id) ids_shared in
  let (ids_exist_fst, para_fst) = hpara_dll_instantiate para exp_iF exp_oB exp_iF' exps_shared in  
  let (para_fst_start, para_fst_rest) = 
    let mark_impl_flag hpred = {hpred=hpred; flag=impl_ok1} 
    in match para_fst with
      | [] -> E.err "@.@.ERROR (Empty DLL para): %a@.@." pp_dll_hpara para; assert false
      | hpred :: hpreds ->
	  let hpat = mark_impl_flag hpred in
	  let hpats = List.map mark_impl_flag hpreds
	  in (hpat, hpats) in
  let (ids_exist_snd, para_snd) =  
    let mark_impl_flag hpred = {hpred=hpred; flag=impl_ok2} in
    let (ids, para_body) = hpara_dll_instantiate para exp_iF' exp_iF exp_oF  exps_shared in
    let para_body_hpats = List.map mark_impl_flag para_body 
    in (ids, para_body_hpats) in 
  let dllseg_res = mk_dllseg Lseg_NE para exp_iF exp_oB exp_oF exp_iF' exps_shared in 
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition = 
    (* ddino: for the case of ptspts since iF'=iB therefore iF' cannot be private*)
    let ids_private = ids_exist_fst @ ids_exist_snd 
    in create_condition_dll ids_private id_iF 
  in 
    (*
      E.log "r_root/para_fst_start=%a @.@." pp_hpat para_fst_start;
      E.log "para_fst_rest=%a @.@." pp_hpat_list para_fst_rest;
      E.log "para_snd=%a @.@." pp_hpat_list para_snd;
      E.log "dllseg_res=%a @.@." pp_hpred dllseg_res;
    *)  
    {r_vars = id_iF :: id_oB :: id_iF'::id_oF :: ids_shared @ ids_exist_fst @ ids_exist_snd;
     r_root = para_fst_start;
     r_sigma = para_fst_rest @ para_snd;
     r_new_sigma = [dllseg_res];
     r_new_pi = gen_pi_res;
     r_condition = condition}


let mk_rule_ptsdll_dll k2 impl_ok1 impl_ok2 para =   
  let id_iF = create_fresh_primed_ident name_dll_rule in
  let id_iF' = create_fresh_primed_ident name_dll_rule in
  let id_oB = create_fresh_primed_ident name_dll_rule in
  let id_oF = create_fresh_primed_ident name_dll_rule in
  let id_iB = create_fresh_primed_ident name_dll_rule in
  let ids_shared =
    let svars = para.svars_dll in
    let f id = create_fresh_primed_ident (ident_name id) 
    in List.map f svars in
  let exp_iF = Var id_iF in
  let exp_iF' = Var id_iF' in
  let exp_oB = Var id_oB in 
  let exp_oF = Var id_oF in
  let exp_iB = Var id_iB in
  let exps_shared = List.map (fun id -> Var id) ids_shared in
  let (ids_exist, para_inst) = hpara_dll_instantiate para exp_iF exp_oB exp_iF' exps_shared in  
  let (para_inst_start, para_inst_rest) = 
    match para_inst with
      | [] -> assert false
      | hpred :: hpreds -> 
	  let allow_impl hpred = {hpred=hpred; flag=impl_ok1} 
          in (allow_impl hpred, List.map allow_impl hpreds) in 
  let dllseg_pat = {hpred = mk_dllseg k2 para exp_iF' exp_iF exp_oF exp_iB exps_shared; flag = impl_ok2} in
  let dllseg_res = mk_dllseg Lseg_NE para exp_iF exp_oB exp_oF exp_iB exps_shared in 
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition = 
    let ids_private = id_iF':: ids_exist  
    in create_condition_dll ids_private id_iF  
  in 
    {r_vars = id_iF :: id_oB :: id_iF'::id_oF::id_iB:: ids_shared @ ids_exist; 
     r_root = para_inst_start;
     r_sigma = para_inst_rest @ [dllseg_pat];
     r_new_pi = gen_pi_res;
     r_new_sigma = [dllseg_res];
     r_condition = condition}



let mk_rule_dllpts_dll k1 impl_ok1 impl_ok2 para = 
  let id_iF = create_fresh_primed_ident name_dll_rule in
  let id_iF' = create_fresh_primed_ident name_dll_rule in
  let id_oB = create_fresh_primed_ident name_dll_rule in
  let id_oB' = create_fresh_primed_ident name_dll_rule in
  let id_oF = create_fresh_primed_ident name_dll_rule in
  let ids_shared =
    let svars = para.svars_dll in
    let f id = create_fresh_primed_ident (ident_name id) 
    in List.map f svars in
  let exp_iF = Var id_iF in
  let exp_iF' = Var id_iF' in
  let exp_oB = Var id_oB in 
  let exp_oB' = Var id_oB' in 
  let exp_oF = Var id_oF in
  let exps_shared = List.map (fun id -> Var id) ids_shared in
  let (ids_exist, para_inst) = hpara_dll_instantiate para exp_iF' exp_oB' exp_oF exps_shared in  
  let para_inst_pat=
    let allow_impl hpred = {hpred=hpred; flag=impl_ok2} 
    in List.map allow_impl para_inst in 
  let dllseg_pat = {hpred = mk_dllseg k1 para exp_iF exp_oB exp_iF' exp_oB' exps_shared; flag = impl_ok1} in
  let dllseg_res = mk_dllseg Lseg_NE para exp_iF exp_oB exp_oF exp_iF' exps_shared in 
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition = 
    let ids_private = id_oB':: ids_exist  
    in create_condition_dll ids_private id_iF 
  in 
    {r_vars = id_iF :: id_oB :: id_iF'::id_oB'::id_oF:: ids_shared @ ids_exist; 
     r_root = dllseg_pat;
     r_sigma = para_inst_pat;
     r_new_pi = gen_pi_res;
     r_new_sigma = [dllseg_res];
     r_condition = condition}


let mk_rule_dlldll_dll k1 k2 impl_ok1 impl_ok2 para  = 
  let id_iF = create_fresh_primed_ident name_dll_rule in
  let id_iF' = create_fresh_primed_ident name_dll_rule in
  let id_oB = create_fresh_primed_ident name_dll_rule in
  let id_oB' = create_fresh_primed_ident name_dll_rule in
  let id_oF = create_fresh_primed_ident name_dll_rule in
  let id_iB = create_fresh_primed_ident name_dll_rule in
  let ids_shared =
    let svars = para.svars_dll in
    let f id = create_fresh_primed_ident (ident_name id) 
    in List.map f svars in
  let exp_iF = Var id_iF in
  let exp_iF' = Var id_iF' in
  let exp_oB = Var id_oB in 
  let exp_oB' = Var id_oB' in 
  let exp_oF = Var id_oF in
  let exp_iB = Var id_iB in
  let exps_shared = List.map (fun id -> Var id) ids_shared in
  let lseg_fst_pat = {hpred = mk_dllseg k1 para exp_iF exp_oB exp_iF' exp_oB' exps_shared; flag = impl_ok1} in
  let lseg_snd_pat = {hpred = mk_dllseg k2 para exp_iF' exp_oB' exp_oF exp_iB exps_shared; flag = impl_ok2} in
  let k_res = lseg_kind_add k1 k2 in
  let lseg_res = mk_dllseg k_res para exp_iF exp_oB exp_oF exp_iB exps_shared in
  let gen_pi_res p_start p_leftover (inst:subst) = [] in
  let condition = 
    let ids_private = [id_iF';id_oB']  
    in create_condition_dll ids_private id_iF 
  in 
    {r_vars =id_iF :: id_iF' :: id_oB::id_oB' ::id_oF::id_iB:: ids_shared ;
     r_root = lseg_fst_pat;
     r_sigma = [lseg_snd_pat];
     r_new_sigma = [lseg_res];
     r_new_pi = gen_pi_res;
     r_condition = condition}


let mk_rules_for_dll (para : hpara_dll) : rule list = 
  if not !Config.nelseg then 
  begin
    let pts_pts = mk_rule_ptspts_dll true true para in
    let pts_pedll = mk_rule_ptsdll_dll Lseg_PE true false para in
    let pedll_pts = mk_rule_dllpts_dll Lseg_PE false true para in 
    let pedll_nedll = mk_rule_dlldll_dll Lseg_PE Lseg_NE false false para in
    let nedll_pedll = mk_rule_dlldll_dll Lseg_NE Lseg_PE false false para in
    let pedll_pedll = mk_rule_dlldll_dll Lseg_PE Lseg_PE false false para in 
    [pts_pts;pts_pedll;pedll_pts;pedll_nedll;nedll_pedll;pedll_pedll]
  end
  else 
  begin
    let ptspts_dll = mk_rule_ptspts_dll true true para in
    let ptsdll_dll = mk_rule_ptsdll_dll Lseg_NE true false para in
    let dllpts_dll = mk_rule_dllpts_dll Lseg_NE false true para in
    let dlldll_dll = mk_rule_dlldll_dll Lseg_NE Lseg_NE false false para in 
    [ptspts_dll; ptsdll_dll; dllpts_dll; dlldll_dll]
  end

(* ================  End of DLL abstraction rules  ================ *)





(* ================  Start of Predicate Discovery  ================ *)

let typ_get_recursive_flds te =
  let filter (_,t) = 
    match t with 
    | Tvar _ | Tint | Tfloat | Tvoid | Tfun -> false
    | Tptr (Tvar tname') -> 
	let typ' = match tenv_lookup tname' with
	  | None -> E.err "@[ERROR: Undefined Type %a@." Ident.pp_name tname'; assert false 
	  | Some typ' -> typ' in 
        exp_equal te (Sizeof typ')
    | Tptr _ | Tstruct _ | Tarray _ -> 
	false
  in
    match te with
      | Sizeof typ ->
	  (match typ with
	    | Tvar _ -> assert false (* there should be no indirection *)
	    | Tint | Tvoid | Tfun | Tptr _ | Tfloat -> []
	    | Tstruct fld_typ_list -> List.map fst (List.filter filter fld_typ_list)
	    | Tarray _ -> [])
      | Var _ -> [] (* type of |-> not known yet *)
      | Const_int _ -> []
      | _ ->
	  E.stderr "@.typ_recursive_flds: unexpected type expr: %a@." pp_exp te;
	  assert false


let prop_remove_hpred prop e =
  let filter = function
    | Hpointsto (root,_,_) | Hlseg (Lseg_PE,_,root,_,_) 
    | Hlseg (Lseg_NE,_,root,_,_) 
    | Hdllseg (Lseg_NE,_,root,_,_,_,_) 
    | Hdllseg (Lseg_PE,_,root,_,_,_,_) -> 
        if (check_equal prop root e) then Some () else None 
  in match prop_iter_create prop with
    | None -> (None, prop)
    | Some iter ->
	(match prop_iter_find iter filter with
	  | None -> (None, prop)
	  | Some iter_cur ->
	      let (hpred, _) = prop_iter_current iter_cur in
	      let p_leftover = prop_iter_remove_curr_then_to_prop iter_cur 
              in (Some hpred, p_leftover))  
    

let rec generate_todos_from_strexp todos sexp1 sexp2 =  
  match sexp1,sexp2 with
    | Eexp exp1, Eexp exp2 -> 
	let new_todos = (exp1,exp2) :: todos 
	in Some (List.rev new_todos)
    | Eexp _, _ -> 
        None
    | Estruct fel1, Estruct fel2 -> (* assume sorted w.r.t. fields *)
	generate_todos_from_fel todos fel1 fel2
    | Estruct _, _ -> 
        None
    | Earray (n1,iel1), Earray (n2,iel2) ->
	if n1=n2 
        then generate_todos_from_iel todos iel1 iel2
	else None
    | Earray _, _ -> 
        None

and generate_todos_from_fel todos fel1 fel2 = 
  match fel1,fel2 with
    | [],[] ->
	Some (List.rev todos)
    | (fld1,strexp1) :: fel1', (fld2,strexp2) :: fel2' ->
	if not (fld_equal fld1 fld2) then None
	else begin
	  match generate_todos_from_strexp todos strexp1 strexp2 with
	    | None -> None
	    | Some todos' -> generate_todos_from_fel todos' fel1' fel2'
	end 
    | _ -> 
	None 
	  
and generate_todos_from_iel todos iel1 iel2 = 
  match iel1,iel2 with
    | [],[] -> 
	Some (List.rev todos)
    | (idx1,strexp1) :: iel1', (idx2,strexp2) :: iel2' -> 
	begin
	  match generate_todos_from_strexp todos strexp1 strexp2 with
	    | None -> None
	    | Some todos' ->
		let new_todos = (idx1,idx2) :: todos' 
		in generate_todos_from_iel new_todos iel1' iel2'
	end 
    | _ ->
	None


(** add (e1,e2) at the front of corres, if necessary. *)
let corres_extend_front e1 e2 corres = 
  let filter (e1',e2') = (exp_equal e1 e1') || (exp_equal e2 e2') in
  let checker e1' e2' = (exp_equal e1 e1') && (exp_equal e2 e2')
  in match (List.filter filter corres) with 
    | [] -> Some ((e1,e2) :: corres)
    | [(e1',e2')] when checker e1' e2' -> Some corres
    | _ -> None

let corres_extensible corres e1 e2 = 
  let predicate (e1',e2') = (exp_equal e1 e1') || (exp_equal e2 e2') 
  in not (List.exists predicate corres) && not (exp_equal e1 e2)

let corres_related corres e1 e2 = 
  let filter (e1',e2') = (exp_equal e1 e1') || (exp_equal e2 e2') in
  let checker e1' e2' = (exp_equal e1 e1') && (exp_equal e2 e2')
  in match (List.filter filter corres) with 
    | [] -> exp_equal e1 e2
    | [(e1',e2')] when checker e1' e2' -> true
    | _ -> false

(* TO DO. Perhaps OK. Need to implemenet a better isomorphism check later.*)
let hpara_iso para1 para2 =
  hpara_match_with_impl false para1 para2 && hpara_match_with_impl false para2 para1


let hpara_dll_iso para1 para2 =
  hpara_dll_match_with_impl false para1 para2 && hpara_dll_match_with_impl false para2 para1



(** hpara_discover : prop -> (exp * exp) list
                          -> hpred list 
                          -> (exp * exp) list 
                          -> ((exp * exp) list * hpred list) option.
    The order of "updating" corres and sigma is important.
    Uses DFT. *)
let rec construct_partial_iso_dft p corres sigma = function
  | [] -> Some (List.rev corres, List.rev sigma)
  | (e1,e2) :: todos when corres_related corres e1 e2 ->
      let new_corres = match corres_extend_front e1 e2 corres with
	| None -> assert false
	| Some new_corres -> new_corres 
      in construct_partial_iso_dft p new_corres sigma todos
  | (e1,e2) :: todos when corres_extensible corres e1 e2 ->
      let (hpredo1,p_no_e1) = prop_remove_hpred p e1 in
      let (hpredo2,p_no_e12) = prop_remove_hpred p_no_e1 e2 
      in begin match(hpredo1, hpredo2) with
        | (None, None) ->
            let new_corres = match corres_extend_front e1 e2 corres with
   	      | None -> assert false
	      | Some new_corres -> new_corres 
            in construct_partial_iso_dft p new_corres sigma todos
	| (None, _) | (_, None) -> 
            None
	| (Some (Hpointsto (_, _, te1)), Some (Hpointsto (_, _, te2))) when not (exp_equal te1 te2) -> 
            None
	| (Some (Hpointsto (_,se1,_) as hpred1), Some (Hpointsto (_,se2,_))) ->
	    begin 
              match generate_todos_from_strexp [] se1 se2 with
		| None -> None
		| Some (todos') ->
		    let new_corres = match corres_extend_front e1 e2 corres with
		      | None -> assert false 
		      | Some new_corres -> new_corres in
		    let new_sigma = hpred1 :: sigma in
		    let new_todos = todos' @ todos 
		    in construct_partial_iso_dft p_no_e12 new_corres new_sigma new_todos
	    end  
	| (Some (Hlseg (k1,para1,root1,next1,shared1)), Some (Hlseg (k2,para2,root2,next2,shared2))) ->
	    if k1!=k2 || not (hpara_iso para1 para2) then None
	    else
	      (try
		  let new_corres = match corres_extend_front e1 e2 corres with
		    | None -> assert false
		    | Some new_corres -> new_corres in
		  let new_sigma = (Hlseg (Lseg_PE,para1,root1,next1,shared1)) :: sigma in 
		  let shared12 = List.combine shared1 shared2 in
		  let new_todos = (root1, root2) :: (next1, next2) :: shared12 @ todos
		  in construct_partial_iso_dft p_no_e12 new_corres new_sigma new_todos
		with Invalid_argument _ -> None)
	| (Some (Hdllseg(k1,para1,iF1,oB1,oF1,iB1,shared1)), Some (Hdllseg(k2,para2,iF2,oB2,oF2,iB2,shared2))) ->
	    if k1!=k2 || not (hpara_dll_iso para1 para2) then None
	    else
	      (try
		  let new_corres = match corres_extend_front e1 e2 corres with
		    | None -> assert false
		    | Some new_corres -> new_corres in
		  let new_sigma = (Hdllseg(Lseg_PE,para1,iF1,oB1,oF1,iB1,shared1)) :: sigma in 
		  let shared12 = List.combine shared1 shared2 in
		  let new_todos = (iF1,iF2)::(oB1,oB2)::(oF1,oF2)::(iB1,iB2)::shared12@todos
		  in construct_partial_iso_dft p_no_e12 new_corres new_sigma new_todos
		with Invalid_argument _ -> None)
	| _ -> None
      end
  | _ -> None

let already_visited= ref []

let in_already_visited (e1,e2) =
  let a=List.filter (fun (e1',e2') -> exp_equal e1 e1' && exp_equal e2 e2') !already_visited in
  List.length a>0

let rec construct_partial_iso_dft_dll p corres sigma1 sigma2 = function
  | [] -> Some (List.rev corres, List.rev sigma1, List.rev sigma2)
  | (e1,e2) :: todos when corres_related corres e1 e2 && not (in_already_visited (e1,e2)) ->
      already_visited:=(e1,e2)::!already_visited;
      let new_corres = match corres_extend_front e1 e2 corres with
  	| None -> assert false
	| Some new_corres -> new_corres 
      in construct_partial_iso_dft_dll p new_corres sigma1 sigma2 todos
  | (e1,e2) :: todos when corres_extensible corres e1 e2 &&  not (in_already_visited (e1,e2)) ->
      already_visited:=(e1,e2)::!already_visited;
      let (hpredo1,p_no_e1) = prop_remove_hpred p e1 in
      let (hpredo2,p_no_e12) = prop_remove_hpred p_no_e1 e2 
      in begin match(hpredo1, hpredo2) with
      | (None, None) ->
          let new_corres = match corres_extend_front e1 e2 corres with
   	    | None -> assert false
	    | Some new_corres -> new_corres 
          in (*print_list_edges new_corres; *)
	  construct_partial_iso_dft_dll p new_corres sigma1 sigma2 todos
      | (None, _) | (_, None) -> None
      | (Some (Hpointsto (_, _, te1)), Some (Hpointsto (_, _, te2))) when not (exp_equal te1 te2) -> 
          None
      | (Some (Hpointsto (_,se1,_) as hpred1), Some (Hpointsto (_,se2,_) as hpred2)) ->
 	  begin 
            match generate_todos_from_strexp [] se1 se2 with
	    | None -> None
	    | Some (todos') ->
		let new_corres = match corres_extend_front e1 e2 corres with
		  | None -> assert false 
		  | Some new_corres -> new_corres in
		let new_sigma1 = hpred1 :: sigma1 in
		let new_sigma2 = hpred2 :: sigma2 in
		let new_todos = todos' @ todos 
		in 
		construct_partial_iso_dft_dll p_no_e12 new_corres new_sigma1 new_sigma2 new_todos
	  end  
      | (Some (Hlseg (k1,para1,root1,next1,shared1) as hpred1), Some (Hlseg (k2,para2,root2,next2,shared2) as hpred2)) ->
	  if k1!=k2 || not (hpara_iso para1 para2) then None
	  else
	    (try
	       let new_corres = match corres_extend_front e1 e2 corres with
		 | None -> assert false
		 | Some new_corres -> new_corres in
	       let new_sigma1 = hpred1 :: sigma1 in
	       let new_sigma2 = hpred2 :: sigma2 in
	       let shared12 = List.combine shared1 shared2 in
	       let skip_nil_ending=exp_equal next1 (Const_int 0) && exp_equal next2 (Const_int 0) in
	       let new_todos = if skip_nil_ending then
		 (root1, root2) :: shared12 @ todos
	       else (root1, root2) :: (next1, next2) :: shared12 @ todos
	       in 
	       construct_partial_iso_dft_dll p_no_e12 new_corres new_sigma1 new_sigma2 new_todos
	     with Invalid_argument _ ->  None)
      | _ -> None
      end
  | (e1,e2)::todos  when  (in_already_visited (e1,e2)) -> 
      if (List.length todos=0 && (List.length sigma1 =0 || List.length sigma2=0)) then None 
      else ( 
	let new_corres = match corres_extend_front e1 e2 corres with 
	  | None -> 
	      if (exp_equal (Const_int 0) e1 && exp_equal (Const_int 0) e2) then 
		(e1,e2)::corres (* ddino: if (Nil,Nil) cannot be added I force it *)
	      else assert false
	  | Some new_corres -> new_corres in
	construct_partial_iso_dft_dll p new_corres sigma1 sigma2 todos)

  | (e1,e2)::_ -> 
      already_visited:=(e1,e2)::!already_visited; (* this instruction can be skipped *)
      None



let name_dscv = name_siltmp
       

let discover_para_roots p root1 next1 root2 next2 : hpara option = 
  let eq_arg1 = exp_equal root1 next1 in
  let eq_arg2 = exp_equal root2 next2 in
  let precondition_check = (not eq_arg1 && not eq_arg2) in 
  if not precondition_check then None 
  else
    let corres = [(next1,next2)] in
    let todos = [(root1,root2)] in 
    match construct_partial_iso_dft p corres [] todos with
    | None -> None
    | Some (new_corres, new_sigma) ->
        let new_corres' = 
          List.filter (function 
            | (Const_int n, Const_int m) -> n <> m 
            | _ -> true) new_corres in
        let add_fresh_id pair = (pair, create_fresh_primed_ident name_dscv) in
        let corres_ids = List.map add_fresh_id new_corres' in
        let get_id1 e1 = 
          try 
            let is_equal_to_e1 ((e1',_),_) = exp_equal e1 e1' in
            let (_,id) = List.find is_equal_to_e1 corres_ids in 
            id
          with Not_found -> assert false in
        let id_root = get_id1 root1 in
        let id_next = get_id1 next1 in
        let (ids_shared,ids_exists) =
          let neq_root_nor_next1 ((e1,_),_) = 
            not (exp_equal root1 e1 || exp_equal next1 e1) in 
	  let corres_ids_no_root_next = List.filter neq_root_nor_next1 corres_ids in  
          let should_be_shared ((e1,e2),_) = exp_equal e1 e2 in
	  let (shared, exists) = List.partition should_be_shared corres_ids_no_root_next in 
          (List.map snd shared, List.map snd exists) in
        let body = 
          let replacement = List.map (fun ((e1,_),id) -> (e1, Var id)) corres_ids in 
          sigma_replace_exp replacement new_sigma in 
        Some {root=id_root;next=id_next;svars=ids_shared;evars=ids_exists;body=body}

let discover_para_dll_roots p root1 blink1 flink1 root2 blink2 flink2 : hpara_dll option =
  let eq_arg1  = exp_equal root1 blink1 in
  let eq_arg1' = exp_equal root1 flink1 in
  let eq_arg2  = exp_equal root2 blink2 in
  let eq_arg2' = exp_equal root2 flink2 in
  let precondition_check = not (eq_arg1 || eq_arg1' || eq_arg2 || eq_arg2') in 
  if not precondition_check then None 
  else
    let corres = [(blink1,blink2);(flink1,flink2)] in
    let todos = [(root1,root2)] in 
    match (construct_partial_iso_dft p corres [] todos) with
    | None -> None
    | Some (new_corres, new_sigma) ->
        let new_corres' = 
          List.filter (function 
            | (Const_int n, Const_int m) -> n <> m 
            | _ -> true) new_corres in
        let add_fresh_id pair = (pair, create_fresh_primed_ident name_dscv) in
        let corres_ids = List.map add_fresh_id new_corres' in
        let get_id1 e1 = 
          try 
            let is_equal_to_e1 ((e1',_),_) = exp_equal e1 e1' in
	     let (_,id) = List.find is_equal_to_e1 corres_ids in 
             id
	  with Not_found -> assert false in
        let id_root = get_id1 root1 in
        let id_blink = get_id1 blink1 in
        let id_flink = get_id1 flink1 in
        let (ids_shared,ids_exists) =
          let neq_root_blink_flink ((e1,_),_) = 
            not (exp_equal root1 e1 || exp_equal blink1 e1 || exp_equal flink1 e1) in 
          let corres_ids_no_root_blink_flink = List.filter neq_root_blink_flink corres_ids in  
          let should_be_shared ((e1,e2),_) = exp_equal e1 e2 in
          let (shared, exists) = List.partition should_be_shared corres_ids_no_root_blink_flink in 
          (List.map snd shared, List.map snd exists) in
        let body = 
          let replacement = List.map (fun ((e1,_),id) -> (e1, Var id)) corres_ids in 
          sigma_replace_exp replacement new_sigma in 
        Some {cell=id_root; blink=id_blink; flink=id_flink; svars_dll=ids_shared; evars_dll=ids_exists;body_dll=body}

(*
let discover_para_dll_roots p root1 blink1 flink1 root2 blink2 flink2 : hpara_dll option=
  already_visited:=[];

  let eq_arg1 = exp_equal root1 flink1 in
  let eq_arg2 = exp_equal root2 flink2 in
  let precondition_check = (not eq_arg1 && not eq_arg2) 
  in if not precondition_check then None else
      let corres = [(flink1,flink2)] in
      let todos = [(root1,root2)] 
      in match construct_partial_iso_dft_dll p corres [] [] todos with
	| None -> None
	| Some _ when exp_equal blink1 (Const_int 0) && exp_equal flink2 (Const_int 0) -> None
	| Some (new_corres, new_sigma1, new_sigma2) ->
	    let add_fresh_id pair = 
	      (pair, create_fresh_primed_ident name_dscv) in
	    let corres_ids = List.map add_fresh_id new_corres in
	    let get_id1 e1 = 
	      try 
		let is_equal_to_e1 ((e1',_),_) = exp_equal e1 e1' in
		let (_,id) = List.find is_equal_to_e1 corres_ids 
		in id
	      with Not_found -> assert false in
	    let get_id2 e2 = 
	      try 
		let is_equal_to_e2 ((_,e2'),_) = exp_equal e2 e2' in
 		let (_,id) = List.find is_equal_to_e2 corres_ids 
		in id
	      with Not_found -> assert false in
	    let (id_root,id_flink,id_blink,new_sigma)= if exp_equal blink1 (Const_int 0) then   
	      (get_id2 root2, get_id2 flink2, get_id2 blink2,new_sigma2) 
	    else 
	      (get_id1 root1, get_id1 flink1, get_id1 blink1,new_sigma1) 
	    in
	    let (ids_shared,ids_exists) =
	      let neq_root_nor_next_nor_prev1 ((e1,_),_) = 
                 not (exp_equal root1 e1 || exp_equal flink1 e1 || exp_equal blink1 e1) in 
	      let neq_root_nor_next_nor_prev2 ((_,e1),_) = 
                 not (exp_equal root2 e1 || exp_equal flink2 e1 || exp_equal blink1 e1) in 
	      let corres_ids_no_root_next = 
		if exp_equal blink1 (Const_int 0) then
		  List.filter neq_root_nor_next_nor_prev2 corres_ids 
		else List.filter neq_root_nor_next_nor_prev1 corres_ids in  
              let should_be_shared ((e1,e2),_) = exp_equal e1 e2 in
	      let (shared, exists) = List.partition should_be_shared corres_ids_no_root_next
	      in (List.map snd shared, List.map snd exists) in
	    let body = 
              let replacement = 
		if exp_equal blink1 (Const_int 0) then
		  List.map (fun ((_,e1),id) -> (e1, Var id)) corres_ids 
		else List.map (fun ((e1,_),id) -> (e1, Var id)) corres_ids 
	      in sigma_replace_exp replacement new_sigma 
	    in Some {cell=id_root; blink=id_blink; flink=id_flink; svars_dll=ids_shared; evars_dll=ids_exists;body_dll=body}
*) 

let discover_para_candidates p =
  let edges = ref [] in
  let add_edge edg =
    edges := edg :: !edges in
  let rec get_edges = function 
    | [] -> 
        ()
    | Hlseg _ :: sigma_rest | Hdllseg _ :: sigma_rest -> 
        get_edges sigma_rest
    | Hpointsto (root, se, te) :: sigma_rest ->
        (match (se, typ_get_recursive_flds te) with
	  | Eexp _, _ | Earray _, _ -> 
	      get_edges sigma_rest
	  | Estruct fsel, flds ->
	      let fsel_filtered =
		let filter (fld,_) = List.exists (fld_equal fld) flds
		in List.filter filter fsel in
	      let process_nxt (_,nextse) =
		    let next = match nextse with 
		      | Eexp next -> next
		      | _ -> assert false
		    in add_edge (root,next)
	      in
		List.iter process_nxt fsel_filtered;
		get_edges sigma_rest) in
  let rec find_all_consecutive_edges found edges_seen = function
    | [] -> List.rev found
    | (e1,e2) :: edges_notseen ->
	let edges_others = (List.rev edges_seen) @ edges_notseen in
	let edges_matched = List.filter (fun (e1',_) -> exp_equal e2 e1') edges_others in
	let new_found = 
	  let f found_acc (_,e3) = (e1,e2,e3) :: found_acc
	  in List.fold_left f found edges_matched in
	let new_edges_seen = (e1,e2) :: edges_seen 
	in find_all_consecutive_edges new_found new_edges_seen edges_notseen in
  let sigma = prop_get_sigma p in
  let () = get_edges sigma
  in find_all_consecutive_edges [] [] !edges

let discover_para_dll_candidates p = 
  let edges = ref [] in
  let add_edge edg =
    edges := edg :: !edges in
  let rec get_edges = function 
    | [] -> 
        ()
    | Hlseg _ :: sigma_rest -> 
        get_edges sigma_rest
    | Hdllseg _ :: sigma_rest -> 
        get_edges sigma_rest
    | Hpointsto (root, se, te) :: sigma_rest ->
        (match (se, typ_get_recursive_flds te) with
	  | Eexp _, _ | Earray _, _ -> 
	      get_edges sigma_rest
	  | Estruct fsel, flds -> 
              let fb_links =
		let filter fld = List.exists (fld_equal fld) flds in
		let strexp_to_exp = function
		  | Eexp e -> e
		  | _ -> assert false in
		let fsel_filtered = List.filter (fun (fld', _) -> filter fld') fsel
                in List.map strexp_to_exp (snd (List.split fsel_filtered)) in
	      let process_blink_flink (blink,flink) =
		add_edge (root,blink,flink) in
	      let rec iter_pairs f = function
		| [] -> ()
		| x::l ->
		    List.iter (fun y -> f (x,y)) l;
		    iter_pairs f l
	      in
		iter_pairs process_blink_flink fb_links;
		get_edges sigma_rest) in
  let rec find_all_consecutive_edges found edges_seen = function
    | [] -> List.rev found
    | (iF,blink,flink) :: edges_notseen ->
	let edges_others = (List.rev edges_seen) @ edges_notseen in
 	let edges_matched = List.filter (fun (e1',_,_) -> exp_equal flink e1') edges_others in
	let new_found = 
          let f found_acc (_,_,flink2) = (iF,blink,flink,flink2) :: found_acc
	  in List.fold_left f found edges_matched in
	let new_edges_seen = (iF,blink,flink) :: edges_seen 
	in find_all_consecutive_edges new_found new_edges_seen edges_notseen in
  let sigma = prop_get_sigma p in
  let () = get_edges sigma
  in find_all_consecutive_edges [] [] !edges 





let discover_para p = 
  let candidates = discover_para_candidates p in
  let already_defined para paras =
      List.exists (fun para' -> hpara_iso para para') paras in
  let f paras (root,next,out) =
    match (discover_para_roots p root next next out) with
      | None -> paras
      | Some para -> if already_defined para paras then paras else para :: paras
  in List.fold_left f [] candidates

let discover_para_dll p = 
  (*
  E.log "@[.... Called discover_dll para ...@.";
  E.log "@[<4>  PROP : %a@\n@." pp_prop p; 
  *)
  let candidates = discover_para_dll_candidates p in
  let already_defined para paras =
      List.exists (fun para' -> hpara_dll_iso para para') paras in
  let f paras (iF,oB,iF',oF) =
    match (discover_para_dll_roots p iF oB iF' iF' iF oF) with
      | None -> paras
      | Some para -> if already_defined para paras then paras else para :: paras
  in List.fold_left f [] candidates

(* ================  Start of Predicate Discovery  ================ *)





(* ================ Start of the ADT abs_rules ================ *)

type para_ty = SLL of hpara | DLL of hpara_dll

type rule_set = para_ty * rule list

type abs_rules = { mutable ar_default : rule_set list }

let rec pp_hparas f = function
  | [] -> ()
  | [para] -> F.fprintf f "PRED: %a" pp_hpara para
  | para::paras -> F.fprintf f "PRED: %a@\n@\n%a" pp_hpara para pp_hparas paras


let rec pp_dll_hparas f = function
  | [] -> ()
  | [para] -> F.fprintf f "PRED: %a" pp_dll_hpara para
  | para::paras -> F.fprintf f "PRED: %a@\n@\n%a" pp_dll_hpara para pp_dll_hparas paras


let eqs_sub subst eqs =
  List.map (fun (e1,e2) -> (exp_sub subst e1, exp_sub subst e2)) eqs

let eqs_solve ids_in eqs_in =
  let rec solve (sub:subst) (eqs:(exp*exp) list) : subst option = 
    let do_default id e eqs_rest =
      if not (List.exists (fun id' -> ident_equal id id') ids_in) then None
      else
	let sub' = match extend_sub sub id e with
	  | None -> E.err "@.@.ERROR : Buggy Implementation.@.@."; assert false 
	  | Some sub' -> sub' in
	let eqs_rest' = eqs_sub sub' eqs_rest
	in solve sub' eqs_rest'
    in match eqs with
      | [] -> Some sub
      | (e1, e2) :: eqs_rest when exp_equal e1 e2 ->
          solve sub eqs_rest
      | (Var id1, (Const_int _ as e2)) :: eqs_rest -> 
	  do_default id1 e2 eqs_rest
      | ((Const_int _ as e1), (Var _ as e2)) :: eqs_rest -> 
	  solve sub ((e2,e1)::eqs_rest)
      | ((Var id1 as e1), (Var id2 as e2)) :: eqs_rest ->
	  let n = ident_compare id1 id2
	  in begin
	    if n = 0 then solve sub eqs_rest
	    else if n > 0 then solve sub ((e2,e1)::eqs_rest)
	    else do_default id1 e2 eqs_rest 
	  end
      | _ :: _ -> None in
  let compute_ids sub = 
    let sub_list = sub_to_list sub in
    let sub_dom = List.map fst sub_list in
    let filter id = 
      not (List.exists (fun id' -> ident_equal id id') sub_dom) 
    in List.filter filter ids_in
  in 
    match solve sub_empty eqs_in with
      | None -> None
      | Some sub -> Some (compute_ids sub, sub)
	  

let sigma_special_cases_eqs sigma = 
  let rec f ids_acc eqs_acc sigma_acc = function
    | [] -> 
	[(List.rev ids_acc, List.rev eqs_acc, List.rev sigma_acc)]
    | Hpointsto _ as hpred :: sigma_rest -> 
	f ids_acc eqs_acc (hpred::sigma_acc) sigma_rest
    | Hlseg(k,para,e1,e2,es) as hpred :: sigma_rest ->
	let empty_case = 
	  f ids_acc ((e1,e2)::eqs_acc) sigma_acc sigma_rest in
	let pointsto_case =  
	  let (eids,para_inst) = hpara_instantiate para e1 e2 es 
	  in f (eids@ids_acc) eqs_acc sigma_acc (para_inst@sigma_rest) in
	let general_case = 
	  f ids_acc eqs_acc (hpred::sigma_acc) sigma_rest 
	in empty_case @ pointsto_case @ general_case
    | Hdllseg(k,para,e1,e2,e3,e4,es) as hpred :: sigma_rest ->
	let empty_case = 
	  f ids_acc ((e1,e3)::(e2,e4)::eqs_acc) sigma_acc sigma_rest in
	let pointsto_case =  
	  let (eids,para_inst) = hpara_dll_instantiate para e1 e2 e3 es 
	  in f (eids@ids_acc) eqs_acc sigma_acc (para_inst@sigma_rest) in
	let general_case = 
 	  f ids_acc eqs_acc (hpred::sigma_acc) sigma_rest 
	in empty_case @ pointsto_case @ general_case
  in f [] [] [] sigma

let sigma_special_cases ids sigma : (ident list * hpred list) list =
  let special_cases_eqs = sigma_special_cases_eqs sigma in
  let special_cases_rev =
    let f acc (eids_cur,eqs_cur,sigma_cur) =
      let ids_all = ids @ eids_cur 
      in match (eqs_solve ids_all eqs_cur) with
	| None -> acc
	| Some (ids_res, sub) -> 
            (ids_res, List.map (hpred_sub sub) sigma_cur) :: acc
    in List.fold_left f [] special_cases_eqs
  in List.rev special_cases_rev

let rec hpara_special_cases hpara : hpara list = 
  let update_para (evars',body') = { hpara with evars=evars'; body=body'} in
  let special_cases = sigma_special_cases hpara.evars hpara.body 
  in List.map update_para special_cases 

let rec hpara_special_cases_dll hpara : hpara_dll list = 
  let update_para (evars',body') = { hpara with evars_dll=evars'; body_dll=body'} in
  let special_cases = sigma_special_cases hpara.evars_dll hpara.body_dll 
  in List.map update_para special_cases 


let abs_rules : abs_rules = { ar_default = [] }

let abs_rules_reset () =
  abs_rules.ar_default <- []

let abs_rules_add rule_set : unit = 
(*
  let _ = match (fst rule_set) with
    | SLL hpara -> E.err "@.@....Added Para: %a@.@." pp_hpara hpara
    | DLL _ -> ()
  in 
*)
    abs_rules.ar_default <- abs_rules.ar_default@[rule_set]


let abs_rules_add_sll (para:hpara) : unit = 
  let rules = mk_rules_for_sll para in
  let rule_set = (SLL para, rules)
  in abs_rules_add rule_set

let abs_rules_add_dll (para:hpara_dll) : unit = 
  let rules = mk_rules_for_dll para in
  let rule_set = (DLL para, rules)
  in abs_rules_add rule_set

let abs_rules_apply_rsets (rsets:rule_set list) (p_in:prop) : prop =
  let apply_rule (changed,p) r = 
    match (sigma_rewrite p r) with
      | None -> (changed, p)
      | Some p' -> 
(*
         E.log "@[.... abstraction (rewritten in abs_rules) ....@.";
         E.log "@[<4>  PROP:%a@\n@." pp_prop p'; 
*)
         (true, p') in
  let rec apply_rule_set p rset =
    let (_,rules) = rset in
    let (changed,p') = List.fold_left apply_rule (false,p) rules
    in if changed then apply_rule_set p' rset else p' 
  in List.fold_left apply_rule_set p_in rsets

let abs_rules_apply (p_in:prop) : prop = 
  let new_rsets = ref [] in
  let def_rsets = abs_rules.ar_default in
  let rec discover_then_abstract p = 
    let (closed_paras_sll, closed_paras_dll) = 
      let paras_sll = discover_para p in
      let paras_dll = discover_para_dll p in
      let closed_paras_sll = List.flatten (List.map hpara_special_cases paras_sll) in
      let closed_paras_dll = List.flatten (List.map hpara_special_cases_dll paras_dll) in 
      begin
        (*
        if List.length closed_paras_sll >= 1 then
          begin
  	    E.log "@.... discovered predicates ....@.";
            E.log "@[<4>  pred : %a@\n@." pp_hparas closed_paras_sll;
          end
        if List.length closed_paras_dll >= 1 then
          begin
	    E.log "@.... discovered predicates ....@.";
            E.log "@[<4>  pred : %a@\n@." pp_dll_hparas closed_paras_dll;
          end
        *)
        (closed_paras_sll, closed_paras_dll)
      end in
    let (todo_paras_sll, todo_paras_dll) = 
      let eq_sll para = function (SLL para', _) -> hpara_iso para para' | _ -> false in
      let eq_dll para = function (DLL para', _) -> hpara_dll_iso para para' | _ -> false in
      let filter_sll para = 
	not (List.exists (eq_sll para) def_rsets) && not (List.exists (eq_sll para) !new_rsets) in
      let filter_dll para = 
	not (List.exists (eq_dll para) def_rsets) && not (List.exists (eq_dll para) !new_rsets) in
      let todo_paras_sll = List.filter filter_sll closed_paras_sll in
      let todo_paras_dll = List.filter filter_dll closed_paras_dll
      in (todo_paras_sll, todo_paras_dll) in 
    let f_recurse _ = 
      let todo_rsets_sll = List.map (fun para -> (SLL para, mk_rules_for_sll para)) todo_paras_sll in
      let todo_rsets_dll = List.map (fun para -> (DLL para, mk_rules_for_dll para)) todo_paras_dll in
      let _ = new_rsets := !new_rsets @ todo_rsets_sll @ todo_rsets_dll in
      let p' = abs_rules_apply_rsets todo_rsets_sll p in
      let p'' = abs_rules_apply_rsets todo_rsets_dll p' 
      in discover_then_abstract p'' 
    in match todo_paras_sll, todo_paras_dll with
      | [], [] -> p
      | _ -> f_recurse () in
  let p1 = abs_rules_apply_rsets def_rsets p_in in
  let p2 = if !Config.on_the_fly then discover_then_abstract p1 else p1
  in
    abs_rules.ar_default <- (def_rsets@(!new_rsets));
    p2

(* ================ End of the ADT abs_rules ================ *)




(* ================ Start of fns that add rules during preprocessing =============== *)	  

let name_para = name_siltmp

let is_simply_recursive tname =
  let typ = match tenv_lookup tname with
    | None -> assert false 
    | Some typ -> typ in
  let filter (_,t) = match t with 
    | Tvar _ | Tint | Tfloat | Tvoid | Tfun -> 
        false
    | Tptr (Tvar tname') -> 
        name_equal tname tname'
    | Tptr _ | Tstruct _ |Tarray _ -> 
        false
  in match typ with
    | Tvar _ -> 
        assert false (* there should be no indirection *)
    | Tint | Tfloat | Tvoid | Tfun | Tptr _ ->
        None 
    | Tstruct fld_typ_list -> 
	begin
          match (List.filter filter fld_typ_list) with
	    | [(fld,_)] -> Some fld
	    | _ -> None
	end 
    | Tarray _ ->
        None

let create_hpara_from_tname_flds tname nfld sflds eflds =
  let typ = match tenv_lookup tname with
    | Some typ -> typ 
    | None -> assert false in
  let id_base = create_fresh_primed_ident name_para in
  let id_next = create_fresh_primed_ident name_para in
  let ids_shared = List.map (fun _ -> create_fresh_primed_ident name_para) sflds in
  let ids_exist = List.map (fun _ -> create_fresh_primed_ident name_para) eflds in
  let exp_base = Var id_base in
  let fld_sexps = 
    let ids = id_next :: (ids_shared @ ids_exist) in
    let flds = nfld :: (sflds @ eflds) in
    let f fld id = (fld, Eexp (Var id)) 
    in try List.map2 f flds ids with Invalid_argument _ -> assert false in
  let strexp_para = Estruct fld_sexps in
  let ptsto_para = mk_ptsto exp_base strexp_para (Sizeof typ)
  in mk_hpara id_base id_next ids_shared ids_exist [ptsto_para] 


let create_dll_hpara_from_tname_flds tname flink blink sflds eflds =
  let typ = match tenv_lookup tname with
    | Some typ -> typ 
    | None -> assert false in
  let id_iF = create_fresh_primed_ident name_para in
  let id_oB = create_fresh_primed_ident name_para in
  let id_oF = create_fresh_primed_ident name_para in
  let ids_shared = List.map (fun _ -> create_fresh_primed_ident name_para) sflds in
  let ids_exist = List.map (fun _ -> create_fresh_primed_ident name_para) eflds in
  let exp_iF = Var id_iF in
  let fld_sexps = 
    let ids = id_oF::id_oB :: (ids_shared @ ids_exist) in
    let flds = flink::blink::(sflds @ eflds) in
    let f fld id = (fld, Eexp (Var id)) 
    in try List.map2 f flds ids with Invalid_argument _ -> assert false in
  let strexp_para = Estruct fld_sexps in
  let ptsto_para = mk_ptsto exp_iF strexp_para (Sizeof typ)
  in mk_dll_hpara id_iF id_oB id_oF  ids_shared ids_exist [ptsto_para]


let create_hpara_two_ptsto tname1 nfld1 dfld tname2 nfld2 =
  let typ1 = match tenv_lookup tname1 with
    | Some typ -> typ 
    | None -> assert false in
  let typ2 = match tenv_lookup tname2 with
    | Some typ -> typ 
    | None -> assert false in
  let id_base = create_fresh_primed_ident name_para in
  let id_next = create_fresh_primed_ident name_para in
  let id_exist = create_fresh_primed_ident name_para in
  let exp_base = Var id_base in
  let exp_exist = Var id_exist in
  let fld_sexps1 = 
    let ids = [id_next; id_exist] in
    let flds = [nfld1; dfld] in
    let f fld id = (fld, Eexp (Var id)) 
    in try List.map2 f flds ids with Invalid_argument _ -> assert false in
  let fld_sexps2 = 
    [(nfld2, Eexp (Const_int 0))] in
  let strexp_para1 = Estruct fld_sexps1 in
  let strexp_para2 = Estruct fld_sexps2 in
  let ptsto_para1 = mk_ptsto exp_base strexp_para1 (Sizeof typ1) in
  let ptsto_para2 = mk_ptsto exp_exist strexp_para2 (Sizeof typ2) 
  in mk_hpara id_base id_next [] [id_exist] [ptsto_para1;ptsto_para2] 


let create_hpara_dll_two_ptsto tname1 flink_fld1 blink_fld1 dfld tname2 nfld2 =
  let typ1 = match tenv_lookup tname1 with
    | Some typ -> typ 
    | None -> assert false in
  let typ2 = match tenv_lookup tname2 with
    | Some typ -> typ 
    | None -> assert false in
  let id_cell = create_fresh_primed_ident name_para in
  let id_blink = create_fresh_primed_ident name_para in
  let id_flink = create_fresh_primed_ident name_para in
  let id_exist = create_fresh_primed_ident name_para in
  let exp_cell = Var id_cell in
  let exp_exist = Var id_exist in
  let fld_sexps1 = 
    let ids = [ id_blink; id_flink; id_exist] in
    let flds = [ blink_fld1; flink_fld1; dfld] in
    let f fld id = (fld, Eexp (Var id)) 
    in try List.map2 f flds ids with Invalid_argument _ -> assert false in
  let fld_sexps2 = 
    [(nfld2, Eexp (Const_int 0))] in
  let strexp_para1 = Estruct fld_sexps1 in
  let strexp_para2 = Estruct fld_sexps2 in
  let ptsto_para1 = mk_ptsto exp_cell strexp_para1 (Sizeof typ1) in
  let ptsto_para2 = mk_ptsto exp_exist strexp_para2 (Sizeof typ2) 
  in mk_dll_hpara id_cell id_blink id_flink [] [id_exist] [ptsto_para1;ptsto_para2] 


let create_hpara_from_tname_twoflds_hpara tname fld_next fld_down para =
  let typ = match tenv_lookup tname with
    | Some typ -> typ 
    | None -> assert false in
  let id_base = create_fresh_primed_ident name_para in
  let id_next = create_fresh_primed_ident name_para in
  let id_down = create_fresh_primed_ident name_para in
  let exp_base = Var id_base in
  let exp_next = Var id_next in
  let exp_down = Var id_down in
  let exp_null = Const_int 0 in
  let strexp = Estruct [(fld_next, Eexp exp_next);(fld_down, Eexp exp_down)] in
  let ptsto = mk_ptsto exp_base strexp (Sizeof typ) in
  let lseg = mk_lseg Lseg_PE para exp_down exp_null [] in
  let body = [ptsto;lseg]
  in mk_hpara id_base id_next [] [id_down] body


let create_hpara_dll_from_tname_twoflds_hpara tname fld_flink fld_blink fld_down para =
  let typ = match tenv_lookup tname with
    | Some typ -> typ 
    | None -> assert false in
  let id_cell = create_fresh_primed_ident name_para in
  let id_blink = create_fresh_primed_ident name_para in
  let id_flink = create_fresh_primed_ident name_para in
  let id_down = create_fresh_primed_ident name_para in
  let exp_cell = Var id_cell in
  let exp_blink = Var id_blink in
  let exp_flink = Var id_flink in
  let exp_down = Var id_down in
  let exp_null = Const_int 0 in
  let strexp = Estruct [(fld_blink, Eexp exp_blink); (fld_flink, Eexp exp_flink);(fld_down, Eexp exp_down)] in
  let ptsto = mk_ptsto exp_cell strexp (Sizeof typ) in
  let lseg = mk_lseg Lseg_PE para exp_down exp_null [] in
  let body = [ptsto;lseg]
  in mk_dll_hpara id_cell id_blink id_flink [] [id_down] body

let name_list = string_to_name "list"
let name_down = string_to_name "down"
let name_HSlist2 = string_to_name "HSlist2"
let name_next = string_to_name "next"

let name_dllist= string_to_name "dllist"
let name_Flink = string_to_name "Flink"
let name_Blink = string_to_name "Blink"
let name_HOdllist= string_to_name "HOdllist" 

let create_absrules_from_tdecl tname =
  if (not (!Config.on_the_fly)) && name_equal tname name_HSlist2 then 
    (* E.log "@[.... Adding Abstraction Rules for Nested Lists ....@\n@."; *)
    let para1 = create_hpara_from_tname_flds name_list name_down [] [] in
    let para2 = create_hpara_from_tname_flds name_HSlist2 name_next [name_down] [] in
    let para_nested = create_hpara_from_tname_twoflds_hpara name_HSlist2 name_next name_down para1 in
    let para_nested_base = create_hpara_two_ptsto name_HSlist2 name_next name_down name_list name_down 
    in List.iter abs_rules_add_sll [para_nested_base;para2;para_nested]
  else if (not (!Config.on_the_fly)) && name_equal tname name_dllist then  
    (* E.log "@[.... Adding Abstraction Rules for Doubly-linked Lists ....@\n@."; *)
    let para = create_dll_hpara_from_tname_flds name_dllist name_Flink name_Blink [] [] 
    in abs_rules_add_dll para
  else if (not (!Config.on_the_fly)) && name_equal tname name_HOdllist then  
    (* E.log "@[.... Adding Abstraction Rules for High-Order Doubly-linked Lists ....@\n@."; *) 
    let para1 = create_hpara_from_tname_flds name_list name_down [] [] in
    let para2 = create_dll_hpara_from_tname_flds name_HOdllist name_Flink name_Blink [name_down] [] in
    let para_nested = create_hpara_dll_from_tname_twoflds_hpara name_HOdllist name_Flink name_Blink name_down para1 in
    let para_nested_base = create_hpara_dll_two_ptsto name_HOdllist name_Flink name_Blink name_down name_list name_down 
    in List.iter abs_rules_add_dll [para_nested_base;para2;para_nested]
  else if (not (!Config.on_the_fly)) then
    match is_simply_recursive tname with
      | None -> ()
      | Some (fld) -> 
	  (* E.log "@[.... Adding Abstraction Rules ....@\n@."; *)
	  let para = create_hpara_from_tname_flds tname fld [] [] 
	  in abs_rules_add_sll para
  else ()

(* ================ End of fns that add rules during preprocessing =============== *)	 




(* ================ Start of Main Abstraction Functions =============== *)

let abstract_pure_part p =
(*
  prop_replace_pi [] p
*)
  let fav_sigma = Prop.sigma_fav (Prop.prop_get_sigma p) in
  let occur_sigma name = Sil.fav_mem fav_sigma name in
  let pi = Prop.prop_get_pi p in
  let new_pi = 
    List.fold_left (fun pi' a ->
      match a with
      | Aneq(Var name,_) when !Config.footprint_analysis -> a::pi'
      | Aneq(Var name,Const_int 0) | Aneq(Const_int 0, Var name) ->
          if (occur_sigma name) then a::pi' else pi'
      | _ -> pi') [] pi in 
  let new_pi' = List.rev new_pi
  in prop_replace_pi new_pi' p 

(* Collect symbolic garbage from pi and sigma *)
let abstract_gc p = 
  let pi = prop_get_pi p in
  let p_without_pi = prop_replace_pi [] p in
  let fav_p_without_pi = prop_fav p_without_pi in
  (* let weak_filter atom =
       let fav_atom = atom_fav atom 
       in list_intersect ident_compare fav_p_without_pi fav_atom in *)
  let strong_filter = function 
    | Aeq(e1,e2) | Aneq(e1,e2) ->
	let fav_e1 = exp_fav e1 in
	let fav_e2 = exp_fav e2 in
	let intersect_e1 _ = list_intersect ident_compare (fav_to_list fav_e1) (fav_to_list fav_p_without_pi) in
	let intersect_e2 _ = list_intersect ident_compare (fav_to_list fav_e2) (fav_to_list fav_p_without_pi) in
	let no_fav_e1 = fav_is_empty fav_e1 in
	let no_fav_e2 = fav_is_empty fav_e2 
        in (no_fav_e1 || intersect_e1 ()) && (no_fav_e2 || intersect_e2 ()) in
  let new_pi = List.filter strong_filter pi in
  let prop = prop_replace_pi new_pi p 
  in match prop_iter_create prop with
    | None -> prop
    | Some iter -> prop_iter_to_prop (prop_iter_gc_fields iter)

let leak_counter = ref 0

let pp_dotty_leak p garb_p  hp=
  leak_counter:=!leak_counter+1;
  let outc = open_out (!Config.curr_filename^(string_of_int(!leak_counter))^".dot") in
  let fmt = F.formatter_of_out_channel outc in
(*  let () = F.fprintf fmt "#### Dotty version:  ####@.%a@.@." pp_speclist_dotty spec_list*)
  Dotty.reset_proposition_counter ();
  Dotty.reset_dotty_spec_counter ();
  F.fprintf fmt "\n\n\ndigraph main { \nnode [shape=box]; \n";
  F.fprintf fmt "\n compound = true; \n";
(*  F.fprintf f "\n size=\"12,7\"; ratio=fill; \n"; *)
  Dotty.pp_dotty_one_spec fmt p (garb_p::[Prop.prop_of_sigma [hp]]);
  F.fprintf fmt  "\n}" ;
  close_out outc




(* implements the junk rule of space invader paper without adding a
 * junk predicate.  So it is unsound. It gets rid of Hlseg, Hdllseg and
 * Hpointsto that are garbage. *)
let abstract_junk prop =
  let prop_before_abstraction=prop in
  let rec iter_junk iter = 
    let (hpred,_) = prop_iter_current iter in 
    let entries = match hpred with
      | Hpointsto (e,_,_) -> [e]
      | Hlseg (_,_,e,_,_) -> [e] 
      | Hdllseg (_,_,e1,_,_,e2,_) -> [e1;e2] in 
    let p_rest = prop_iter_remove_curr_then_to_prop iter in
    let fav_p_rest = prop_live_fav p_rest (* prop_fav p_rest *) in 
    let predicate = function 
      | Var id -> 
          (ident_is_primed id || ident_is_footprint id) 
          && not (fav_mem fav_p_rest id)
      | _ -> false in
    let should_remove_hpred = List.for_all predicate entries 
    in 
    if should_remove_hpred && not (!Config.allowleak)
    then begin 
      E.err "@[\n.... Prop with garbage ....@.";
      E.err "@[<4>  PROP: %a@\n@." pp_prop prop;
      E.err "@[<4>  PREDICATE: %a@\n@." pp_hpred hpred;
      pp_dotty_leak prop_before_abstraction prop hpred;
      raise (Exn.Leak (prop_before_abstraction,prop,hpred))
    end
    else if should_remove_hpred && (!Config.allowleak) 
    then begin
      match prop_iter_remove_curr_then_next iter with
      | None -> p_rest
      | Some iter' -> iter_junk iter'
    end
    else begin
      match prop_iter_next iter with
      | None -> prop_iter_to_prop iter
      | Some iter' -> iter_junk iter'
    end

  in 
  match prop_iter_create prop with 
  | None -> prop
  | Some iter -> iter_junk iter


let abstract_prop ~(rename_primed:bool) p =
  (*
    if !Config.footprint_mode then prop_rename_primed_footprint_vars p
    else
  *)
  let pure_abs_p = abstract_pure_part p in
  let abs_p = abs_rules_apply pure_abs_p in
  (* E.log "@[<2>.... abstraction after core rules ....@\n"; *)
  (* E.log "%a@\n@." pp_prop abs_p; *)
  let abs_p = abstract_gc abs_p in (** abstraction might enable more gc *)
  (* E.log "@[<2>.... abstraction after gc ....@\n"; *)
  (* E.log "%a@\n@." pp_prop abs_p; *)
  let abs_p = abstract_junk abs_p in 
  let ren_abs_p =
    if rename_primed then prop_rename_primed_footprint_vars abs_p
    else abs_p in

  if !Config.footprint_analysis then prop_abs_pi_footprint_vars ren_abs_p
  else ren_abs_p


(** Abstract the footprint of prop *)
let abstract_footprint prop =
  let (p, added_local_vars) = prop_extract_footprint_for_abs prop in 
(*  let p = prop_extract_footprint prop in *)
  let p_abs = abstract_prop ~rename_primed:false p in
  let prop' = prop_set_footprint_for_abs prop p_abs added_local_vars 
(*  let prop' = prop_set_footprint prop p_abs *)
  in prop'

let abstract p =
  let p' = if !Config.footprint then abstract_footprint p else p
  in abstract_prop ~rename_primed:true p'

let lifted_abstract pset =
  let f p =
    if check_inconsistency p then None
    else Some (abstract p) in
  let abstracted_pset = propset_map_option f pset 
  in abstracted_pset

(* ================ End of Main Abstraction Functions =============== *)
