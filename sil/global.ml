(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 *  
 * All rights reserved.
 *)

open Cil
open Cfg_new

module S = Sil
module E = Error.MyErr (struct let mode = Error.DEFAULT end)

let reserved_vnames = ["nondet"]

module WorkList = struct
  module S = Set.Make (struct
    type t = string 
    let compare = Pervasives.compare 
  end)

  let worklist = ref S.empty

  let reset _ = worklist := S.empty
  let add pname = worklist := S.add pname !worklist
  let pick _ =
    let min = S.min_elt !worklist in
    worklist := S.remove min !worklist;
    min
end

module Vset = Set.Make 
  (struct
    type t = S.pvar
    let compare = S.pvar_compare
  end)

module Gtbl = struct
  module Pset = Set.Make (struct
    type t = string
    let compare = Pervasives.compare
  end)

  let gvars_tbl : (string,Vset.t) Hashtbl.t = Hashtbl.create 1024

  let preds_tbl : (string,Pset.t) Hashtbl.t = Hashtbl.create 1024

  let add_gvar pname vinfo = 
    let v_n = Ident.string_to_name vinfo.vname in
    let v = S.mk_pvar_global v_n in
    try
      let gvars = Hashtbl.find gvars_tbl pname in
      Hashtbl.replace gvars_tbl pname (Vset.add v gvars)
    with Not_found ->
      Hashtbl.replace gvars_tbl pname (Vset.singleton v)

  let get_gvars pname = 
    try Vset.elements (Hashtbl.find gvars_tbl pname) 
    with Not_found -> []

  let get_gvar_set pname =
    try
      Hashtbl.find gvars_tbl pname 
    with Not_found ->
      Hashtbl.replace gvars_tbl pname Vset.empty;
      Vset.empty

  let set_gvar_set pname set =
    Hashtbl.replace gvars_tbl pname set

  let add_pred pname pred =
    try 
      let preds = Hashtbl.find preds_tbl pname in
      Hashtbl.replace preds_tbl pname (Pset.add pred preds)
    with Not_found ->
      Hashtbl.replace preds_tbl pname (Pset.singleton pred)

  let get_preds pname = 
    try Pset.elements (Hashtbl.find preds_tbl pname) 
    with Not_found -> []
end

class getGlobalVarsVisitor pname = object
  inherit nopCilVisitor

  method vvrbl vinfo = 
    if (not vinfo.vglob) || (List.mem vinfo.vname reserved_vnames) then 
      ()
    else begin
      match vinfo.vtype with
      | Cil.TVoid _ | Cil.TFun _ | Cil.TBuiltin_va_list _ -> 
          ()
      | Cil.TInt _ | Cil.TFloat _ | Cil.TPtr _ 
      | Cil.TArray _ | Cil.TNamed _ | Cil.TComp _ | Cil.TEnum _ -> 
         (Gtbl.add_gvar pname vinfo;
          WorkList.add pname)
    end;
    DoChildren
end

let initialize_gvars pname pdesc =
  let fd = proc_desc_get_fundec pdesc in
  let visitor = new getGlobalVarsVisitor pname in
  Cil.visitCilFunction visitor fd 

let initialize_preds pname pdesc = 
  let nodes = proc_desc_get_nodes pdesc in
  List.iter (fun node ->
    match (node_get_kind node) with
    | Call_node (callee,_,_) -> 
        let callee_n = proc_desc_to_proc_name callee in
        Gtbl.add_pred callee_n pname
    | _ -> ()) nodes
   
let initialize pname pdesc = 
  let _ = initialize_gvars pname pdesc
  in initialize_preds pname pdesc

let compute () =
  try
    while true do
      let curr = WorkList.pick () in
      let curr_gset = Gtbl.get_gvar_set curr in
      let preds = Gtbl.get_preds curr in
      List.iter (fun pred ->
        let pred_gset = Gtbl.get_gvar_set pred in
        if not (Vset.subset curr_gset pred_gset) 
        then
          let gset' = Vset.union pred_gset curr_gset in
          WorkList.add pred;
          Gtbl.set_gvar_set pred gset'
        else ()) preds   
    done
  with Not_found -> () 

let annotate pname pdesc = 
  let gvars = Gtbl.get_gvars pname in
  E.log "@[  PROCEDURE %s@." pname;
  E.log "@[<6>    Globals : %a@." Sil.pp_pvar_list gvars;
  proc_desc_set_globals pdesc gvars

let time = ref 0.0

let doit () = 
  let init = Stats.get_current_time() in
  E.log "@[@\n#### Computing accessed globals for each procedure ####@.";
  WorkList.reset ();
  proc_desc_iter initialize;
  compute ();
  proc_desc_iter annotate; 
  time := !time +. (Stats.get_current_time() -. init)

let gettime () = !time
