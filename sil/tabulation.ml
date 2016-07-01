(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)


(** Interprocedural footprint analysis *)

open Ident
open Cil
open Sil
open Cfg_new
open Prop
open Fork
module Exn = Exceptions

module E = Error.MyErr (struct let mode = Error.DEFAULT end)
(*
let () = E.set_mode Error.ALWAYS
let () = E.set_colour Error.red
*)

type splitting =
    {sub: subst;
     frame: hpred list;
     missing_pi: atom list;
     missing_sigma: hpred list;
     frame_fld : hpred list;
     missing_fld : hpred list}

(* Result of (bi)-abduction *)
type abduction_res =
  | Consistent_res of Sil.atom list * Prop.prop list 
  | Inconsistent_res of Prop.prop * (splitting option)

(* ================== printing functions ======================== *)
let print_splitting s split =
  E.log "@.@. %s" s; 
  E.log "@.------------------------------------------------------------@.";
  E.log "SUB = @. [ %a ] @." pp_sub split.sub; 
  E.log "FRAME = @. [ %a ] @." pp_sigma split.frame; 
  E.log "MISSING = @. [ %a*%a ] @." pp_pi split.missing_pi pp_sigma split.missing_sigma;
  E.log "FRAME FLD = @. [ %a ] @." pp_sigma split.frame_fld;
  E.log "MISSING FLD = @. [ %a ] @." pp_sigma split.missing_fld;
  E.log "------------------------------------------------------------@."

let print_results results =
  E.log "@.@. ***** RESULTS FUNCTION CALL *******"; 
  List.iter (fun p -> E.log "@.@.%a" pp_prop p) results;
  E.log "@.@. ***** END RESULTS FUNCTION CALL *******@.@."
(* ============================================================== *)

(** Rename the variables in the spec. *)
let spec_rename_vars spec =
  let prop_add_callee_suffix p =
    let f = function
      | Lvar pv ->
	  Lvar (pvar_add_suffix pv Config.callee_suffix)
      | e -> e
    in prop_expmap f p in
  let jprop_add_callee_suffix = function
    | Dom.Prop p -> Dom.Prop (prop_add_callee_suffix p)
    | Dom.Joined (p,jp1,jp2) -> Dom.Joined (prop_add_callee_suffix p,jp1,jp2) in
  let fav = fav_new () in
    Dom.jprop_fav_add fav spec.pre;
    List.iter (prop_fav_add fav) spec.post;
    let ids = fav_to_list fav in
    let ids' = List.map (fun i -> (i,create_fresh_primed_ident (ident_name i))) ids in
    let ren_sub = sub_of_list (List.map (fun (i,i') -> (i, Var i')) ids') in
    let pre' = Dom.jprop_apply_renaming_no_normalize ren_sub spec.pre in
    let post' = List.map (prop_apply_renaming_no_normalize ren_sub) spec.post in
    let pre'' = jprop_add_callee_suffix pre' in
    let post'' = List.map prop_add_callee_suffix post'
    in {pre=pre'';post=post''}

(** Find and number the specs for [proc_name], after renaming their vars *)
let spec_find_rename (proc_name : string) : (int * spec) list =
  let find_specs proc_name =
    let specs = get_specs proc_name
    in if specs==[] then raise Exn.No_specs
      else specs
  in
    try
      let count = ref 0 in
      let f spec =
	incr count; (!count, spec_rename_vars spec)
      in List.map f (find_specs proc_name)
    with Not_found -> begin
      E.err "@.@. ERROR: found no entry for procedure %s. Give up...@.@." proc_name;
      raise Exn.No_specs
    end

let get_formal_params proc_name =
  let proc_desc = proc_name_to_proc_desc proc_name in
  let fun_dec = proc_desc_get_fundec proc_desc in
  let formal_names = List.map (fun v -> v.vname) (proc_desc_get_formals proc_desc) in
  let list_formal =
    List.map (fun x -> Sil.mk_pvar (string_to_name x) fun_dec Config.callee_suffix) formal_names
  in list_formal

(** Process a splitting coming straight from a call to the prover:
    change the instantiating substitution so that it returns primed vars,
    except for vars occurring in the missing part, where it returns
    footprint vars. *)
let process_splitting actual_pre sub1 sub2 frame missing_pi missing_sigma frame_fld missing_fld =
  let sub = sub_join sub1 sub2 in

  let sub1_inverse =
    let sub1_list = sub_to_list sub1 in
    let sub1_list' = List.filter (function (_,Var _) -> true | _ -> false) sub1_list in
    let sub1_inverse_list = List.map (function (id,Var id') -> (id', Var id) | _ -> assert false) sub1_list'
    in sub_of_list sub1_inverse_list
  in

  let fav_actual_pre =
    let fav_sub2 = (* vars which represent expansions of fields *)
      let fav = fav_new () in
      let () = List.iter (exp_fav_add fav) (sub_range sub2) in
      let filter id = ident_get_stamp id = -1 in
      let () = fav_filter_ident fav filter
      in fav in
    let fav_pre = prop_fav actual_pre in
    let () = ident_list_fav_add (fav_to_list fav_sub2) fav_pre
    in fav_pre in
  let fav_missing = sigma_fav (sigma_sub sub missing_sigma) in
  let () = pi_fav_add fav_missing (pi_sub sub missing_pi) in
  let fav_missing_primed =
    let filter id = ident_is_primed id && not (fav_mem fav_actual_pre id)
    in fav_copy_filter_ident fav_missing filter in
  let fav_missing_fld = sigma_fav (sigma_sub sub missing_fld) in

  let map_var_to_pre_var_or_fresh id =
    match exp_sub sub1_inverse (Var id) with
      | Var id' ->
	  if fav_mem fav_actual_pre id'
	  then Var id'
	  else Var (create_fresh_primed_ident (ident_name id))
      | _ -> assert false
  in

  let sub_list = sub_to_list sub in
  let fav_sub_list = 
    let fav_sub = fav_new () in
    let () = List.iter (fun (_,e) -> exp_fav_add fav_sub e) sub_list
    in fav_to_list fav_sub in
  let sub1 =
    let f id =
      if fav_mem fav_actual_pre id
      then (id, Var id)
      else if ident_is_normal id
      then (id, map_var_to_pre_var_or_fresh id)
      else if fav_mem fav_missing_fld id then (id,Var id)
      else
	(E.err "@.@.Don't know about id: %a@." pp_ident id;
	 assert false)
    in sub_of_list (List.map f fav_sub_list) in
  let sub2_list =
    let f id = (id, Var (create_fresh_footprint_ident (ident_name id)))
    in List.map f (fav_to_list fav_missing_primed) in
  let sub_list' =
    List.map (fun (id,e) -> (id, exp_sub sub1 e)) sub_list in
  let sub' = sub_of_list (sub2_list @ sub_list')
  in
    {sub=sub';frame=frame;missing_pi=missing_pi;missing_sigma=missing_sigma;frame_fld=frame_fld;missing_fld=missing_fld}

let compute_splitting spec_pre actual_pre : splitting option =
  match Prover.check_implication_for_footprint actual_pre (Dom.jprop_to_prop spec_pre) with
    | Some (sub1,sub2,frame,missing_pi,missing_sigma,frame_fld,missing_fld) ->
	let split = process_splitting actual_pre sub1 sub2 frame missing_pi missing_sigma frame_fld missing_fld
	in Some split
    | None ->
	None

(* checks if actual_pre*missing_footprint |- false 
   in that case we flag a possible memory fault.
*)
let consistent_actualpre_missing r =
  match r with 
  |Inconsistent_res (prop, Some split) ->
     let new_footprint_pi = pi_sub split.sub split.missing_pi in
     let new_footprint_sigma = sigma_sub split.sub split.missing_sigma in
     let prop'= prop_sigma_star prop new_footprint_sigma in
     let prop''= List.fold_left prop_atom_and prop' new_footprint_pi in
     Prover.check_inconsistency prop'' 
  |Inconsistent_res (prop, None) -> false
  | _ -> assert false

let post_process_post_sigma sigma =
  let rec process_hpred hpred = match hpred with
    | Hpointsto(Lfield(e,fld),se,te) ->
	let te' = match te with
	  | Sizeof _t ->
	      Sizeof (Tstruct [(fld,_t)])
	  | _ -> raise (Failure "sigma_imply: Unexpected non-sizeof type") in
	let hpred' = Hpointsto(e, Estruct [(fld,se)], te')
	in process_hpred hpred'
    | _ -> hpred
  in List.map process_hpred sigma

(** Post process the instantiated post after the function call so that
  x.f |-> se   becomes  x|->{f:se}  *)
let post_process_post (p:prop) =
  prop_replace_sigma (post_process_post_sigma (prop_get_sigma p)) p

let combine (post:prop list) prop split name_proc =
  let new_footprint_pi = pi_sub split.sub split.missing_pi in
  let new_footprint_sigma = sigma_sub split.sub split.missing_sigma in
  let new_frame_fld = sigma_sub split.sub split.frame_fld in
  let new_missing_fld =
    let sigma = sigma_sub split.sub split.missing_fld in
    let filter = function
      | Hpointsto(Var id,_,_) -> ident_is_footprint id
      | hpred ->
	  E.err "@.WARNING: Missing fields in complex pred: %a@.@." pp_hpred hpred;
	  false
    in List.filter filter sigma in
  let instantiated_frame = sigma_sub split.sub split.frame in
  let instantiated_post = List.map (fun p -> post_process_post (prop_sub split.sub p)) post in
  let () = E.log "@. New footprint:@.%a*%a@." pp_pi new_footprint_pi pp_sigma new_footprint_sigma in
  let () = E.log "@. Frame fld:@.%a@." pp_sigma new_frame_fld in
  let () = E.log "@. Missing fld:@.%a@." pp_sigma new_missing_fld in
  let () = E.log "@. Instantiated frame:@.%a@." pp_sigma instantiated_frame in
  let () = E.log "@. Instantiated post:@.%a@." Propset.pp_proplist instantiated_post in
  let compute_result post_p =
    let post_p' =
      let post_sigma = sigma_star_fld (prop_get_sigma post_p) new_frame_fld
      in prop_replace_sigma post_sigma post_p in
    let post_p1 = prop_sigma_star (prop_copy_footprint_pure prop post_p') instantiated_frame in
    let post_p2 = List.fold_left prop_atom_and post_p1 new_footprint_pi in
    let post_p3 =
      if !Config.footprint
      then
	prop_footprint_add_pi_sigma_starfld_sigma post_p2 new_footprint_pi new_footprint_sigma new_missing_fld
      else Some post_p2
    in post_p3 in
  let results =
    let map_option f l =
      let lo = List.filter (function | Some _ -> true | None -> false) (List.map f l)
      in List.map (function Some p -> p | None -> assert false) lo
    in map_option compute_result instantiated_post in
  let () = print_results results
  in results

(** Construct the actual precondition: add to the current state a copy
    of the (callee's) formal parameters instantiated with the actual
    parameters. *)
let mk_actual_precondition prop actual_params formal_params =
  let formals_actuals =
    let rec comb fpars apars = match fpars,apars with
      | f::fpars', a::apars' -> (f,a) :: comb fpars' apars'
      | [], _ ->
	  if apars != [] then
	    E.err "WARNING: more actual pars than formal pars in fun call (%d vs %d)" (List.length actual_params) (List.length formal_params);
	  []
      | _::_,[] -> raise Exn.Wrong_argument_number
    in comb formal_params actual_params in
  let mk_instantiation (formal_var,(actual_e,actual_t)) = mk_ptsto (Lvar formal_var) (Eexp actual_e) (Sizeof actual_t) in
  let instantiated_formals = List.map mk_instantiation formals_actuals in
  let actual_pre = prop_sigma_star prop instantiated_formals
  in actual_pre

let exe_spec (n,nspecs) name_proc prop spec actual_params formal_params : abduction_res  =
  let check_missing actual_pre split =
    if !Config.footprint then Some []
    else if split.missing_sigma != [] then None
    else Some (pi_sub split.sub split.missing_pi) in
  let actual_pre = mk_actual_precondition prop actual_params formal_params in
  let () = E.log "@.@. EXECUTING SPEC %d/%d@." n nspecs in
  let () = E.log "@[<v> ACTUAL PRECONDITION =@, %a@ " pp_prop actual_pre in
  let () = E.log "@ SPEC =@ %a@ " pp_spec spec
  in match compute_splitting spec.pre actual_pre with
    | None -> Inconsistent_res(actual_pre,None)
    | Some split ->
	print_splitting "Actual splitting" split;
	(match check_missing actual_pre split with
	  | None ->
	      E.log "@.Implication error: missing not empty in re-execution@.";
	      Inconsistent_res(actual_pre,Some split)
	  | Some missing_pi ->
	      let results = combine spec.post actual_pre split name_proc in
	      let _,results' = List.partition Prover.check_inconsistency results
	      in if results' == [] then Inconsistent_res(actual_pre, Some split)
       		else Consistent_res (missing_pi,results')) 

(** Execute the function call and return the list of results with return value *)
let exe_function_call proc_name actual_params prop =
  let process_results results =
    let results,inco_res = List.partition (fun r -> match r with | Inconsistent_res _ -> false | Consistent_res _ -> true ) results in
    let results = List.map (function Consistent_res (r1,r2) -> (r1,r2) | Inconsistent_res _  -> assert false) results in
    let () =
      if (results == []) && !Config.footprint && List.exists consistent_actualpre_missing inco_res
      then raise (Exn.Memory_fault_Inconsistent_CallingState_MissingFP prop)
      else () in
    let res_miss_pi,res' = List.partition (fun (missing_pi,posts) -> missing_pi != []) results
    in
      if !Config.footprint then List.map prop_strengthen_footprint (List.flatten (List.map snd results))
      else if res'==[]
      then
	let print_pi pi = E.log "pi: %a@." pp_pi pi in
	  if res_miss_pi != [] then
	    (E.err "@.@. Missing pure facts for the function call:@.";
	     List.iter print_pi (List.map fst res_miss_pi);
	     match Prover.find_minimum_pure_cover res_miss_pi with
	       | None -> raise Exn.Re_exe_funcall
	       | Some cover ->
		   E.log "@.Found minimum cover!!@.";
		   List.iter print_pi (List.map fst cover);
		   List.flatten (List.map snd cover))
	  else []
      else List.flatten (List.map snd res') in
  let spec_list = spec_find_rename proc_name in
  let formal_params = get_formal_params proc_name in
  let nspecs = List.length spec_list in
  let () = E.log "@.@. $$$$ Found %i specs for function %s" nspecs proc_name in
  let () = E.log "@.@.+++++ START EXECUTING SPECS FOR %s from state @.%a @.@." proc_name pp_prop prop in
  let exe_one_spec (n,s) = exe_spec (n,nspecs) proc_name prop s actual_params formal_params in
  let results = List.map exe_one_spec spec_list
  in process_results results
