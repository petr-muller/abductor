(*
 *
 * Copyright (c) 2006-2008,callg
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

open Pretty
open Cil
module F = Format
module E = Error.MyErr (struct let mode = Error.DEFAULT end)

let debug = false

(* reserved function names for which we do symbolic execution *)
let reserved_functions = ref []

(** Add reserved function names which we handle in symbolic execution *)
let add_reserved_functions fun_names =
  reserved_functions := fun_names @ !reserved_functions

(* special function for which the code does not exist. 
   They are mapped in a dummy node and skipped *)
let special_functions = ref []

(* known issues:
 * -sucessors of if somehow end up with two edges each 
 *)


(* ============== START of functions for stmts ============== *)

(* Number of stmts in the CFG that has been constructed until now. *)
let num_stmts = ref 0 

let rec print_list printer = function
  | [] -> ()
  | [x] -> printer x
  | x1::x2::xs -> 
      printer x1; 
      E.log ", "; 
      printer x2; 
      print_list printer xs

let rec forallStmts (todo) (fd : fundec) = 
  begin
    fasBlock todo fd.sbody;
  end

and fasBlock (todo) (b : block) =
  List.iter (fasStmt todo) b.bstmts

and fasStmt (todo) (s : stmt) =
  begin
    ignore(todo s);
    match s.skind with
      | Block b -> fasBlock todo b
      | If (_, tb, fb, _) -> (fasBlock todo tb; fasBlock todo fb)
      | Switch (_, b, _, _) -> fasBlock todo b
      | Loop (b, _, _, _) -> fasBlock todo b
      | (Return _ | Break _ | Continue _ | Goto _ | Instr _) -> ()
      | TryExcept _ | TryFinally _ -> 
            E.err "try/except/finally"; 
            assert false
  end

(* ============== END of functions for stmts ============== *)





(* ============== START of ADT node and proc_desc ============== *)

type nodekind = 
  | Start_node of proc_desc
  | Exit_node of proc_desc
  | Stmt_node of Sil.instr list
  | Join_node 
  | Prune_node of Sil.instr list * Sil.exp
  | Call_node of proc_desc * Sil.instr list * (Sil.exp * Sil.typ) list
  | Return_Site_node of Sil.instr list
  | Skip_node of string

and node = {
  mutable nd_id : int;
  mutable nd_kind : nodekind;
  mutable nd_succs : node list;
  mutable nd_preds : node list;
  mutable nd_proc : proc_desc option;
  mutable nd_dead : Ident.ident list;
  mutable nd_dead_pvar : Sil.pvar list;
  mutable nd_loc : location
}
and proc_desc = {
  pd_fd : fundec;
  mutable pd_globals : Sil.pvar list; (* list of accessed global variables *)
  mutable pd_nodes : node list; (* list of nodes of the procedure *)
  mutable pd_start_node : node; 
  mutable pd_exit_node : node;
}

let dummy_node = {
  nd_id = -1;
  nd_kind = Skip_node "dummy";
  nd_succs = []; nd_preds = [];
  nd_proc = None;
  nd_dead = [];
  nd_dead_pvar = [];
  nd_loc = locUnknown
}

type id_node_hashtbl = (int, node) Hashtbl.t

let node_id = ref 0

let node_id_set i = node_id := i
let node_id_gen _ = let v = !node_id in incr node_id; v
 
let id_node_map : id_node_hashtbl = Hashtbl.create 1000

let id_node_map_add id node = 
  Hashtbl.add id_node_map id node

let id_node_map_find key =
  Hashtbl.find id_node_map key
    
let node_list : node list ref = ref []

let get_all_nodes _ = !node_list

(* assume that stmt.sid is set beforehand *)

let node_create loc kind succ_nodes pred_nodes proc_desc_opt dead =
  let node_id = node_id_gen () in
  let node =
    { nd_id = node_id;
      nd_kind = kind; 
      nd_succs = succ_nodes; 
      nd_preds = pred_nodes; 
      nd_proc = proc_desc_opt; 
      nd_dead = dead;
      nd_dead_pvar = [];
      nd_loc = loc;
    } in 
    node_list := node :: !node_list;
    (match proc_desc_opt with
      | None -> ()
      | Some pd -> pd.pd_nodes <- node :: pd.pd_nodes);
    node

let register_stmt_node stmt node = id_node_map_add stmt.sid node

let node_create_base loc kind =
  node_create loc kind [] [] None []

let node_create_base' loc kind pdesc dead =
  node_create loc kind [] [] (Some pdesc) dead

let stmt_node_find_or_create stmt =
  try
    Hashtbl.find id_node_map stmt.sid
  with Not_found ->
    let node = node_create_base (get_stmtLoc stmt.skind) (Skip_node "") in
    register_stmt_node stmt node;
    node

let node_to_sid node = node.nd_id

let node_get_succs node =
  node.nd_succs

let node_get_preds node =
  node.nd_preds

let node_get_kind node =
  node.nd_kind

let node_set_kind node kind =
  node.nd_kind <- kind

let instr_get_loc = function
  | Sil.Letderef (_,_,_,loc) -> loc
  | Sil.Set (_,_,_,loc) -> loc
  | Sil.Nullify _ -> assert false (** should not exist yet *)
  | Sil.Call (_,_,_,loc) -> loc

let block_get_first_loc block = 
  let rec f = function
    | [] -> locUnknown
    | stmt::stmts ->
	Cil.get_stmtLoc stmt.skind
  in f block.bstmts

let block_get_last_loc block =
  block_get_first_loc {block with bstmts = List.rev block.bstmts}

let node_get_loc n = n.nd_loc

let node_set_proc_desc pdesc node =
  node.nd_proc <- Some pdesc

let node_get_proc_desc node =
  let proc_desc = match node.nd_proc with
    | None -> 
	E.err "node_get_proc_desc: at node %d@." node.nd_id;
        assert false
    | Some(proc_desc) -> proc_desc
  in proc_desc

let node_get_sil node =
  match node.nd_kind with
  | Stmt_node sil | Return_Site_node sil 
  | Prune_node (sil,_) | Call_node (_,sil,_) -> sil
  | _ -> assert false

let node_set_dead node dead =
  node.nd_dead <- dead

let node_get_dead node =
  node.nd_dead

let node_set_dead_pvar node dead =
  node.nd_dead_pvar <- dead

let node_get_dead_pvar node =
  node.nd_dead_pvar

let node_compare node1 node2 =
  Ident.int_compare node2.nd_id node1.nd_id

let node_equal node1 node2 = 
  (node_compare node1 node2 = 0)

let pp_node f node = 
  F.fprintf f "%n" node.nd_id 

let rec pp_node_list f = function
  | [] -> ()
  | [node] -> pp_node f node
  | node::nodes -> 
      F.fprintf f "%a, %a" pp_node node pp_node_list nodes

let node_print node = 
  E.log "%i" node.nd_id

let node_list_print nodes = 
  print_list node_print nodes


type pdesc_tbl_t = (string, proc_desc) Hashtbl.t 

let pdesc_tbl : pdesc_tbl_t = Hashtbl.create 1000

let pdesc_tbl_add proc_name proc_desc = 
  Hashtbl.add pdesc_tbl proc_name proc_desc

let pdesc_tbl_find proc_name =
  Hashtbl.find pdesc_tbl proc_name

let proc_desc_iter f =
  Hashtbl.iter f pdesc_tbl

let proc_desc_create fd start_node exit_node = 
  { pd_fd=fd;
    pd_globals=[];
    pd_nodes=[];
    pd_start_node=start_node;
    pd_exit_node=exit_node;
  }

let proc_desc_create_base fd =
  let pdesc = proc_desc_create fd dummy_node dummy_node in
  let start_node = node_create (block_get_first_loc fd.sbody) (Start_node pdesc) [] [] (Some pdesc) [] in
  let exit_node = node_create (block_get_last_loc fd.sbody) (Exit_node pdesc) [] [] (Some pdesc) [] in
  pdesc.pd_start_node <- start_node;
  pdesc.pd_exit_node <- exit_node;
  pdesc_tbl_add fd.svar.vname pdesc;
  pdesc

let proc_desc_to_proc_name proc_desc =
  proc_desc.pd_fd.svar.vname 

let proc_name_to_proc_desc proc_name =
  pdesc_tbl_find proc_name

let proc_desc_get_globals proc_desc =
  proc_desc.pd_globals

let proc_desc_set_globals proc_desc globals =
  proc_desc.pd_globals <- globals

let proc_desc_get_fundec proc_desc =
  proc_desc.pd_fd

let proc_desc_get_formals proc_desc =
  proc_desc.pd_fd.sformals

let proc_desc_get_locals proc_desc = 
  proc_desc.pd_fd.slocals

let proc_desc_get_start_node proc_desc =
  proc_desc.pd_start_node

let proc_desc_get_exit_node proc_desc =
  proc_desc.pd_exit_node

(*
let proc_desc_get_call_edges proc_desc =
  List.map (fun x -> x, proc_desc.pd_start_node) proc_desc.pd_callers

let proc_desc_get_ret_edges proc_desc =
  List.map (fun x -> proc_desc.pd_exit_node, x) proc_desc.pd_ret_sites
*)

let proc_desc_get_cil_ret_type proc_desc = 
  match proc_desc.pd_fd.svar.vtype with
    | TFun (typ,_,_,_) -> typ
    | _ -> assert false

let proc_desc_get_cil_ret_var proc_desc : Sil.pvar =
  let ret_var = "retn_"^proc_desc_to_proc_name proc_desc
  in Sil.mk_pvar (Ident.string_to_name ret_var) (proc_desc_get_fundec proc_desc) ""


let proc_desc_get_nodes proc_desc =
  proc_desc.pd_nodes

(** Print extended instructions for the node *)
let pp_node_instr ~sub_instrs fmt node =
  (match node_get_kind node with
    | Stmt_node sil ->
	Sil.pp_instr_list fmt sil
    | Return_Site_node sil ->
	if sub_instrs then Sil.pp_instr_list fmt sil;
	F.fprintf fmt "return;"
    | Prune_node (sil,exp) ->
	if sub_instrs then Sil.pp_instr_list fmt sil;
	F.fprintf fmt "assume %a;" Sil.pp_exp exp
    | Call_node (pdesc,sil,elist) ->
	if sub_instrs then Sil.pp_instr_list fmt sil;
	F.fprintf fmt "%s(@[%a@]);" (proc_desc_to_proc_name pdesc) Sil.pp_exp_list (List.map fst elist)
    | Exit_node _ ->
	F.fprintf fmt "exit;"
    | Skip_node s ->
	F.fprintf fmt "skip (%s);" s
    | Start_node _ ->
	F.fprintf fmt "start;"
    | Join_node ->
	F.fprintf fmt "join;"
  );
  F.fprintf fmt " %a@," Sil.pp_loc node.nd_loc

(** Dump extended instructions for the node *)
let d_node_instrs  ~(sub_instrs:bool) (node:node) =
  Error.add_print_action (Error.PTnode_instrs, Obj.repr (sub_instrs,node))

(** Return a description of the cfg node *)
let get_node_description node = match node_get_kind node with
    | Stmt_node sil ->
	"Instructions"
    | Return_Site_node sil ->
	"Return"
    | Prune_node (sil,exp) ->
	"Conditional"
    | Call_node (pdesc,sil,elist) ->
	"Function call"
    | Exit_node _ ->
	"Exit"
    | Skip_node s ->
	"Skip" 
    | Start_node _ ->
	"Start"
    | Join_node ->
	"Join"

(* =============== END of ADT node and proc_desc =============== *)


(* =============== START of module CallGraph =============== *)
module StringSet =
  Set.Make(struct
    type t = string
    let compare (n1:string) (n2:string) = Pervasives.compare n1 n2
  end)

let pp_nodeset fmt set =
  let f node= F.fprintf fmt "%s@ " node
  in StringSet.iter f set

module CallGraph : sig
  type node = string
  val reset : unit -> unit
  val add_edge : node -> node -> unit
  val add_node : node -> unit
  val get_weight : node -> int
  val get_dependents: node -> StringSet.t
  val get_nonrecursive_dependents: node -> StringSet.t
  val get_recursive_dependents: node -> StringSet.t
  val get_nodes_and_dependents : unit -> (node * StringSet.t) list
  val node_defined : node -> bool
  val delete_node : node -> (node*int) list
  val get_weighted_nodes : unit -> (node*int) list
  val pp_graph_dotty : F.formatter -> unit
end = struct

type node = string

type node_info =
    {mutable parents: StringSet.t;
     mutable children: StringSet.t;
     mutable ancestors : StringSet.t}

type node_tbl = (node,node_info) Hashtbl.t

let global_graph : node_tbl = Hashtbl.create 17

let reset () =
  Hashtbl.clear global_graph

let add_node n =
  try
    ignore (Hashtbl.find global_graph n)
  with Not_found ->
    let info = {parents=StringSet.empty;children=StringSet.empty;ancestors=StringSet.empty}
    in Hashtbl.add global_graph n info

let node_defined n =
  try
    let _ = Hashtbl.find global_graph n
    in true
  with Not_found -> false

let update_ancestors () =
  let node_get_ancestors node =
    (Hashtbl.find global_graph node).ancestors in
  let changed = ref true
  in
    while !changed do
      changed := false;
      Hashtbl.iter (fun n info ->
	let new_ancestors = StringSet.fold (fun n ns -> StringSet.union (node_get_ancestors n) ns) info.ancestors info.ancestors in
	  if not (StringSet.equal info.ancestors new_ancestors)
	  then
	    (changed := true;
	     info.ancestors <- new_ancestors)) global_graph
    done

let add_edge nfrom nto =
  if node_defined nto then
    begin
      add_node nfrom;
      add_node nto;
      let info_from = Hashtbl.find global_graph nfrom in
      let info_to = Hashtbl.find global_graph nto
      in
(*
	if StringSet.mem nto info_from.ancestors || nfrom=nto then
	  E.err "WARNING: ignoring recursive edge %s->%s in call graph@." nfrom nto
	else
*)
	  try
	    info_from.children <- StringSet.add nto info_from.children;
	    info_to.parents <- StringSet.add nfrom info_to.parents;
	    info_to.ancestors <- StringSet.add nfrom info_to.ancestors;
	    update_ancestors ()
	  with
	      Not_found -> assert false
    end

let delete_node n =
  let new_leaves = ref [] in
    try
      let info = Hashtbl.find global_graph n in
      let remove_from_children parent =
	let info = Hashtbl.find global_graph parent
	in
	  info.children <- StringSet.remove n info.children;
	  if StringSet.is_empty info.children then new_leaves := (parent,StringSet.cardinal info.ancestors) :: !new_leaves
      in
	(if not (StringSet.is_empty info.children) then assert false);
	StringSet.iter remove_from_children info.parents;
	Hashtbl.remove global_graph n;
	!new_leaves
    with
      | Not_found -> assert false

let get_nodes () =
  let nodes = ref StringSet.empty in
  let f node info =
    nodes := StringSet.add node !nodes
  in
    Hashtbl.iter f global_graph;
    !nodes

let map_option f l =
  let lo = List.filter (function | Some _ -> true | None -> false) (List.map f l)
  in List.map (function Some p -> p | None -> assert false) lo

let get_weight node =
  let info = Hashtbl.find global_graph node
  in if StringSet.is_empty info.children then StringSet.cardinal info.ancestors
    else 0

let get_weighted_nodes () =
  let nodes = StringSet.elements (get_nodes ())
  in List.map (fun node -> (node, get_weight node)) nodes

let node_get_weight n =
  let info = Hashtbl.find global_graph n
  in (n,StringSet.cardinal info.ancestors)

let get_edges () : ((node*int)*(node*int)) list =
  let edges = ref [] in
  let f node info =
    StringSet.iter (fun nto -> edges := (node_get_weight node,node_get_weight nto)::!edges) info.children
  in
    Hashtbl.iter f global_graph;
    !edges

(* Return the children of [n] *)
let get_children n =
  (Hashtbl.find global_graph n).children

(* Return the ancestors of [n] *)
let get_ancestors n =
  (Hashtbl.find global_graph n).ancestors

(* Return true if [n] is recursive *)
let is_recursive n =
  StringSet.mem n (get_ancestors n)

(* Return the children of [n] which are not heirs of [n] *)
let get_nonrecursive_dependents n =
  let is_not_recursive pn = not (StringSet.mem pn (get_ancestors n)) in
  let res = StringSet.filter is_not_recursive (get_children n)
(*  in let () = E.stderr "Nonrecursive dependents of %s: %a@\n" n pp_nodeset res *)
  in res

(* Return the ancestors of [n] which are also heirs of [n] *)
let get_recursive_dependents n =
  let reached_from_n pn = StringSet.mem n (get_ancestors pn) in
  let res = StringSet.filter reached_from_n (get_ancestors n)
(*  in let () = E.stderr "Recursive dependents of %s: %a@\n" n pp_nodeset res *)
  in res

(* Return the dependents of [n] *)
let get_dependents n =
  StringSet.union (get_nonrecursive_dependents n) (get_recursive_dependents n)

(* Return the list of nodes with respective dependents *)
let get_nodes_and_dependents () =
  let nodes = ref StringSet.empty in
  let () = Hashtbl.iter (fun n info -> nodes := StringSet.add n !nodes) global_graph in
  let nodes_list = StringSet.elements !nodes
  in List.map (fun n -> (n,get_dependents n)) nodes_list

let pp_graph_dotty fmt =
  F.fprintf fmt "digraph {\nsize=\"12,7\"; ratio=fill;\n";
  List.iter (fun ((s,ws),(d,wd)) -> F.fprintf fmt "\"%s(weight=%d)\" -> \"%s(weight=%d)\"\n" s ws d wd) (get_edges ());
  F.fprintf fmt "}@."
end
(* =============== END of module CallGraph =============== *)




(* ============== START of icfg_create_proc_descs ============== *)

(** table to store the formals of declared (not defined) procs *)
let procs_formals = Hashtbl.create 1

let add_proc_formals proc_name formals =
  Hashtbl.add procs_formals proc_name formals

let get_proc_formals proc_name =
  try
    Hashtbl.find procs_formals proc_name
  with Not_found -> []

let icfg_create_proc_descs (f: Cil.file) : unit = 
  E.log "@[Creating proc_descs for all procedures@.";
  let create = function 
    | GFun(fd, loc) ->
	if !Config.footprint_analysis then CallGraph.add_node fd.svar.vname;
	if !Config.curr_filename = "" then Config.curr_filename := loc.file;
	ignore(proc_desc_create_base fd)
    | GVarDecl ({vname=fname; vtype = TFun (_,Some stal,_,_)},_) ->
	let formals = List.map(fun (s,typ,_) -> makeVarinfo false s typ) stal
	in add_proc_formals fname formals
    | _ -> ()
  in iterGlobals f create

(* =============== END of icfg_create_proc_descs =============== *)


       


(* ============== START of icfg_separate_call_stmts ============== *)

(*
 * This function transforms an entire program such that every function call 
 * instruction (Cil.instr) in the program becomes a statement (Cil.stmt). 
 *
 * Intuitively, 
 *    { x=1; z=1; Foo(); y=1; } 
 * is transformed to
 *    { { x=1; z=1; } 
 *      { Foo(); }
 *      { y=1; } } 
 *)

let rec contains_call = function 
  | [] -> false
  | Call(_) :: tl -> true
  | _ :: tl -> contains_call tl 

let split_instrs_by_call (instrs : instr list) : stmt list = 
  let accumulate stmts = function
    | [] -> stmts
    | rev_instrs ->
	let stmt = mkStmt (Instr (List.rev rev_instrs)) 
	in stmt :: stmts in
  let rec f stmts instrs = function
    | [] -> 
	let stmts_new = accumulate stmts instrs
	in List.rev stmts_new
    | Call(_) as instr_cur :: instrs_rest ->
	let stmt_cur = mkStmtOneInstr instr_cur in
	let stmts' =  accumulate stmts instrs in
	let stmts_new = stmt_cur :: stmts' 
	in f stmts_new [] instrs_rest 
    | instr_cur :: instrs_rest ->
        f stmts (instr_cur::instrs) instrs_rest  	  
  in f [] [] instrs

class callBBVisitor = object
  inherit nopCilVisitor 

  method vstmt s =
    match s.skind with
      |	Instr(il) when contains_call il -> begin
          let stmts = split_instrs_by_call il in
	  let block = mkBlock stmts in
	  let update_and_return_s _ = (s.skind <- Block(block); s) 
          in  ChangeDoChildrenPost(s, update_and_return_s)
	end
      | _ -> DoChildren

  method vvdec _ = SkipChildren
  method vexpr _ = SkipChildren
  method vlval _ = SkipChildren
  method vtype _ = SkipChildren
end 

let icfg_separate_call_stmts f =
  let thisVisitor = new callBBVisitor 
  in
    E.log "@[Transforming the program to have function call at the end of blocks@.";
    visitCilFileSameGlobals thisVisitor f  

(* =============== END of icfg_separate_call_stmts =============== *)





(* =============== START of icfg_build_intra_cfg =============== *)

let icfg_set_unique_sid (f : file) =
  iterGlobals f (fun g ->
    match g with 
    | GFun(fd,_) -> 
	forallStmts (fun s -> incr num_stmts; s.sid <- !num_stmts) fd
    | _ -> ())

let create_undefined_procedure pname =
  let formals = get_proc_formals pname in
  let dummy_fd = Cil.emptyFunction pname in
  let () = Cil.setFormals dummy_fd formals in
  let proc_desc = proc_desc_create_base dummy_fd in 
  let start_node = proc_desc.pd_start_node
  and exit_node = proc_desc.pd_exit_node
  in 
     start_node.nd_succs <- [exit_node];
     exit_node.nd_preds <- [start_node];
     special_functions := pname :: !special_functions;
     proc_desc

let link_node_and_succs node succs =
  node.nd_succs <- succs;
  List.iter (fun n -> n.nd_preds <- node :: n.nd_preds) succs

(* Get the name of the return variable of procedure pdesc. *)
let ret_var_get_name (pdesc : proc_desc) : Sil.pvar =
  let ret_var = "retn_"^ pdesc.pd_fd.svar.vname in
  Sil.mk_pvar (Ident.string_to_name ret_var) (proc_desc_get_fundec pdesc) ""

(* Get the type of the return variable of procedure pdesc. *)
let ret_var_get_type (pdesc : proc_desc) : Sil.typ = 
  let cil_ret_type = proc_desc_get_cil_ret_type pdesc in 
  Trans.trans_typ cil_ret_type

(* Build call graph for parallel analysis *)
let add_edge_for_parallel pdesc_from pdesc_to =
  let from_name = proc_desc_to_proc_name pdesc_from in
  let to_name = proc_desc_to_proc_name pdesc_to
  in CallGraph.add_edge from_name to_name

(* Build the CFG of a procedure.
   Note that the worklist algorithm depends on the order of node creation:
   node created later acquires higher priority.
*)

let build_cfg_body pdesc body start_node exit_node =
  let fundec = pdesc.pd_fd in
  let build_node loc k dead succs = 
    let node = node_create_base' loc k pdesc dead in
    link_node_and_succs node succs;
    node in
  let build_node_for_stmt s k dead succs =
    if s.labels = [] then build_node (get_stmtLoc s.skind) k dead succs else
      try 
	let node = Hashtbl.find id_node_map s.sid in
        node.nd_kind <- k;
        node.nd_dead <- dead;
	node.nd_proc <- Some pdesc;
	node.nd_loc <- get_stmtLoc s.skind;
        link_node_and_succs node succs;
        node
      with Not_found ->
	let node = build_node (get_stmtLoc s.skind) k dead succs in
	register_stmt_node s node;
	node in
  let build_node_or_skip info s succs : node list =
    match s.labels with
    | [] -> succs
    | _ -> [build_node_for_stmt s (Skip_node info) [] succs] in

  let rec cfgStmts nlevel break cont next ss =
    List.fold_left (cfgStmt nlevel break cont) next (List.rev ss)

  and cfgBlock nlevel break cont next blk =
    cfgStmts nlevel break cont next blk.bstmts

  and cfgStmt nlevel break cont next s =
    match s.skind with
    | Break _ ->     
	build_node_or_skip "break" s break
    | Continue _ ->  
	build_node_or_skip "continue" s cont
    | Goto (p, _) -> 
	build_node_or_skip "goto" s [stmt_node_find_or_create !p]
    | Block b ->     
	build_node_or_skip "block" s (cfgBlock nlevel break cont next b)

    | Loop (blk,_,_,_) ->
	let node = build_node_for_stmt s (Skip_node "loop") [] [] in
	let body = cfgBlock (nlevel+1) next [node] [node] blk in
	link_node_and_succs node body;
	(* oukseh: change a loop node to a join node if join_level > 1 *)
	if !Config.join_level >= 2 then node.nd_kind <- Join_node; 
	[node]

    | If (e, blk1, blk2, loc) ->
        (* oukseh: extra join node if join_level >= 3 and some condition is met *)
	let new_next = 
	  if (!Config.join_level >= 4) || (nlevel = 0 && !Config.join_level >= 3) then
	    [build_node loc Join_node [] next] 
	  else 
	    next (*[build_node (Skip_node "if-merge") [] next]*) in
        let make_branch e blk =
	  let (ids, sil), cond = Trans.trans_exp pdesc.pd_fd e loc in
	  build_node loc
	    (Prune_node (sil,cond)) ids
	    (cfgBlock nlevel break cont new_next blk) in
	let not_e = UnOp (LNot, e, intType) in
	build_node_or_skip "if" s [make_branch e blk1; make_branch not_e blk2]

    | Switch(_,blk,l,_) -> 
	let _ = cfgBlock nlevel next cont next blk in
	let cases = List.map stmt_node_find_or_create l in
	let cases' = 
	  if List.exists 
            (fun stmt -> List.exists 
              (function Default _ -> true | _ -> false)
              stmt.labels) l
	  then cases else next @ cases in
	build_node_or_skip "switch" s cases'

    | Instr (Call(retop, Lval(Var(callee),NoOffset), params, loc) :: _)
	when not (List.mem callee.vname !reserved_functions) ->
        let (ids,instrs), args_exp = Trans.trans_explist fundec params loc in
	let args_type = List.map (fun e -> Trans.trans_typ (typeOf e)) params in
	let args = List.combine args_exp args_type in
	let callee_pdesc = 
	  try pdesc_tbl_find callee.vname 
	  with Not_found -> create_undefined_procedure callee.vname in
	let callee_fd = proc_desc_get_fundec callee_pdesc in
	let ret_temp = Locality.aux_vars_get_ret callee_fd in
	let ret_type = ret_var_get_type callee_pdesc in
        let templ, ret_instrs = 
	  match retop with
          | None -> [ret_temp], []
          | Some lval -> 
              let (idl,instrs), e = Trans.trans_lval fundec lval loc in
	      let instr = Sil.Set (e, ret_type, Sil.Var(ret_temp), loc) in
              ret_temp :: idl, instrs @ [instr] in
	let ret_site = 
	  build_node loc (Return_Site_node (ret_instrs)) templ next in
        let call_node =
	  (if !Config.footprint_analysis then add_edge_for_parallel pdesc callee_pdesc);
          build_node loc (Call_node (callee_pdesc,instrs,args)) ids [ret_site] in
	(* oukseh: add Join_node right before Call_node if join_level >= 1 *)
	if !Config.join_level >= 1 then 
	  [build_node_for_stmt s Join_node [] [call_node]]
        else  
	  begin register_stmt_node s call_node; [call_node] end 
(*
    | Instr (Call(retop, Lval(e,NoOffset), params, loc) :: _) when
	  (match e with Var _ -> false | _ -> true) ->
	let lv = Lval(e,NoOffset) in
	let doc =  d_exp () lv in
	let s = sprint ~width:80 doc in
	let () = E.stderr "FUNNAME: %s@." s
	in assert false
*)  
  | Instr il ->     
        let rec f instrs tmpl sil =
          match instrs with
	  | [] -> tmpl, sil
	  | h::t -> 
	      let tmpl', sil' = Trans.trans_instr fundec h in
	      f t (tmpl' @ tmpl) (sil' @ sil) in
	let tmpl, sil = f (List.rev il) [] [] in
	[build_node_for_stmt s (Stmt_node sil) tmpl next]

    | Return (Some e, loc) when proc_desc_to_proc_name pdesc <> "main" ->    
	let ret_name = ret_var_get_name pdesc in
	let (idl1,instrs1), e1 = Trans.trans_exp fundec e loc in
	let ret_type = ret_var_get_type pdesc in
	let instr1 = Sil.Set (Sil.Lvar(ret_name),ret_type,e1,loc) in
	[build_node_for_stmt s (Stmt_node (instrs1 @ [instr1])) idl1 
	   [pdesc.pd_exit_node]]
        
    | Return _ -> 
	build_node_or_skip "return" s [pdesc.pd_exit_node]
  
    | TryExcept _ | TryFinally _ -> 
	E.err "try/except/finally";
	assert false in
  
  exit_node.nd_id <- node_id_gen ();
  let start_node' = cfgBlock 0 [] [] [exit_node] body in
  link_node_and_succs start_node start_node';
  start_node.nd_id <- node_id_gen ()

(* Compute a control flow graph for fd.  Stmts in fd have preds and succs
   filled in *)
let rec icfg_build_intra_cfg (fd : fundec) : unit = 
  E.log "@[Computing intra CFG for %s@." fd.svar.vname;
  let proc_desc = pdesc_tbl_find fd.svar.vname in
  let exit_node = proc_desc.pd_exit_node in
  let start_node = proc_desc.pd_start_node in
  build_cfg_body proc_desc fd.sbody start_node exit_node

(* =============== END of icfg_build_intra_cfg =============== *)

let rec enlarge_node node =
  match node.nd_kind with
  | Stmt_node sil1 ->
      begin
	match node.nd_succs with
	| [] | _::_::_ -> ()
	| [succ] ->
	    if List.length succ.nd_preds = 1 then
	    match succ.nd_kind with
	    | Stmt_node sil2 ->
		node.nd_kind <- Stmt_node (sil1 @ sil2);
		node.nd_dead <- node.nd_dead @ succ.nd_dead;
		node.nd_succs <- succ.nd_succs;
		succ.nd_kind <- Skip_node "dead";
		enlarge_node node;
	    | _ -> ()
      end
  | _ -> ()

let enlarge_nodes _ = List.iter enlarge_node !node_list



(* ======== START of functions about interprocedural CFG ============= *)

let iter_func (f: Cil.file) (func: Cil.fundec -> unit) =
  iterGlobals f (function GFun (fd, _) -> func fd | _ -> ())
 
let iter_stmt_with_func (f: Cil.file) (func: Cil.fundec -> Cil.stmt -> unit) =
  iter_func f (fun fd -> forallStmts (func fd) fd)

module String = struct type t = string let compare = Pervasives.compare end
module Sset = Set.Make (String)
module Smap = Map.Make (String)

let pp_sset f sset =
  let l = Sset.elements sset in
  let rec pp_lst f = function
    | [] -> () 
    | [s] -> F.fprintf f "%s" s
    | s::l -> F.fprintf f "%s,@\ %a" s pp_lst l in
  pp_lst f l 


let get_list_of_fun_names f =
  let fun_names = ref []
  in
    fun_names := [];
    iter_func f (fun fn -> fun_names := fn.svar.vname :: !fun_names);
    !fun_names

(** Get all the fun declarations *)
let get_all_fundecs () =
  let fundecs = ref [] in
  let f name fd = fundecs := (proc_desc_get_fundec fd) :: !fundecs
  in Hashtbl.iter f pdesc_tbl; !fundecs

let get_ordered_fundec_list (f: Cil.file) =

  let fd_map = ref (Smap.empty : Cil.fundec Smap.t) in
  let build_fundec_map (f: Cil.file) =
    iter_func f (fun fd -> fd_map := Smap.add fd.svar.vname fd !fd_map) in

  let build_calling_graph (f: Cil.file) =
    let m_out = ref (Smap.add "main" Sset.empty Smap.empty) in
    let find m s = try Smap.find s !m with Not_found -> Sset.empty in
    let add m s1 s2 = m := Smap.add s1 (Sset.add s2 (find m s1)) !m in
    iter_stmt_with_func f (fun fd s ->
      match s.skind with
      | Instr (Call(_, Lval (Var callee, NoOffset), _, _) :: _) 
	  when Smap.mem callee.vname !fd_map ->
          E.log "@[<4>  EDGE: %s => %s@." fd.svar.vname callee.vname;
          add m_out fd.svar.vname callee.vname 
      | _ -> ());
    !m_out in

  let build_called_graph (f: Cil.file) live_procs =
    let names = if !Config.footprint_analysis then get_list_of_fun_names f else ["main"] in
    let add map s = Smap.add s Sset.empty map in
    let map = List.fold_left add Smap.empty names in
    let m_in = ref map in
    let find m s = try Smap.find s !m with Not_found -> Sset.empty in
    let add m s1 s2 = m := Smap.add s1 (Sset.add s2 (find m s1)) !m in
    iter_stmt_with_func f (fun fd s ->
      match s.skind with
      | Instr (Call(_, Lval (Var callee, NoOffset), _, _) :: _) 
	  when Smap.mem callee.vname !fd_map && (!Config.footprint_analysis || Sset.mem fd.svar.vname live_procs) ->
          E.log "@[<4>  EDGE: %s => %s@." fd.svar.vname callee.vname;
          add m_in callee.vname fd.svar.vname;
      | _ -> ());
    !m_in in

  let gen_live_procs m =
    let update set =
      Smap.fold 
        (fun k s set' -> if Sset.mem k set then Sset.union set' s else set')
        m set in
    let rec loop set = 
      let set' = update set in
      if Sset.equal set set' then set 
      else loop set' in
    loop (Sset.singleton "main") in 

  let gen_ordered_fundec_list m =
    let min m =
      Smap.fold (fun k s ((k', max) as cur) -> 
        let ssize = Sset.cardinal s in
        if ssize <= max then (k, ssize) else cur) 
      m ("", max_int) in
    let remove s m = Smap.map (Sset.remove s) (Smap.remove s m) in
    let rec loop m acc =
      if Smap.is_empty m then 
	List.rev acc
      else
	let k,size = min m in 
        if size <> 0 then
          begin
            E.err "@[@\n.... WARNING: Recursive Program ....@.";
            E.err "@[<4>  PROCEDURE : %s@." k;
            E.err "@[<4>  STRANGE CALLERS : %a@\n@." pp_sset (Smap.find k m);
            if !Config.gc_summaries >= 1 && !Config.footprint_analysis=false then 
              assert false 
            else 
              loop (remove k m) (Smap.find k !fd_map :: acc) 
          end
        else
          begin
            (* E.log "@[<4>  PROCEDURE : %s@." k; *)
	    let fd = try Smap.find k !fd_map
	      with Not_found ->
		E.err "\n ERROR: procedure not found : %s@." k;
		assert false
            in loop (remove k m) (fd::acc) 
          end in
    loop m [] in

  build_fundec_map f;
  let m_out = build_calling_graph f in
  let live_procs = gen_live_procs m_out in
  let m_in = build_called_graph f live_procs in
  (*
  E.log "@[@\n.... Live Procedures ....@.";
  E.log "@[<2>  %a@." pp_sset live_procs;
  E.log "@[@\n.... Adding Live Procs ....@.";
  *)
  gen_ordered_fundec_list m_in 

let ordered_fundec_list = ref []

let compute_icfg (f : Cil.file) = 
  icfg_create_proc_descs f;
  icfg_separate_call_stmts f;
  icfg_set_unique_sid f;
  ordered_fundec_list := get_ordered_fundec_list f;
  List.iter icfg_build_intra_cfg !ordered_fundec_list

let get_ordered_fundec_list () = List.rev !ordered_fundec_list

(* ================== END of functions about interprocedural CFG ================== *)






(* ================== START of Print interprocedural cfgs in dotty format  ================== *)
(* Print control flow graph (in dot form) for fundec to channel. 
   You have to compute an interprocedural cfg first *)

let d_cfgnodename () (n : node) =
  dprintf "%d" n.nd_id

let d_cfgnodelabel () (n : node) =
  let label = 
    match n.nd_kind with
    | Start_node (pdesc) -> "Start "^ proc_desc_to_proc_name pdesc
    | Exit_node (pdesc) -> "Exit "^ proc_desc_to_proc_name pdesc
    | Join_node -> "+"
    | Call_node (pdesc,_,_) -> "Call " ^ proc_desc_to_proc_name pdesc
    | Return_Site_node _ -> "Postcall"
    | Prune_node _ -> "Prune"
    | Stmt_node _ -> "instr"
    | Skip_node s -> "Skip " ^ s in
  dprintf "%d: %s" n.nd_id label

let d_cfgnodeshape () (n: node) =
  match n.nd_kind with
  | Start_node _ | Exit_node _ -> dprintf "shape=\"box\""
  | Call_node _ | Return_Site_node _ -> dprintf "shape=\"box\" style=\"rounded\""
  | Prune_node _ -> dprintf "shape=\"invhouse\""
  | Skip_node _ -> dprintf "color=\"gray\""
  | _ -> dprintf ""

let d_cfgedge (src) () (dest) =
  dprintf "%a -> %a"
    d_cfgnodename src
    d_cfgnodename dest

let d_cfg_call_ret_edge () node =
  match node_get_kind node with
  | Call_node (pdesc,_,_) ->
      if not !Config.footprint_analysis then
	dprintf "%a -> %a [color=\"red\"]\n\t%a -> %a [color=\"green\"]\n"
	  d_cfgnodename node
	  d_cfgnodename pdesc.pd_start_node
	  d_cfgnodename pdesc.pd_exit_node
	  d_cfgnodename (List.hd (node_get_succs node))
      else dprintf ""
  | _ -> dprintf ""

let d_cfgnode () (n: node) =
  dprintf "%a [label=\"%a\" %a]\n\t%a\n\t%a;\n" 
    d_cfgnodename n
    d_cfgnodelabel n
    d_cfgnodeshape n
    (d_list "\n\t" (d_cfgedge n)) n.nd_succs
    d_cfg_call_ret_edge n

(*
(** print control flow graph (in dot form) for fundec to channel *)
let print_cfg_channel (chan : out_channel) (fd : fundec) =
  let pnode (s:stmt) = fprintf chan "%a\n" d_cfgnode s 
  in
    forallStmts pnode fd
   

(** Print control flow graph (in dot form) for fundec to file *)
let print_cfg_filename (filename : string) (fd : fundec) =
  let chan = open_out filename in
    begin
      print_cfg_channel chan fd;
      close_out chan;
    end
*)

(* Print the extra information related to the inteprocedural aspect, ie., special node, and 
   call/return edges 
*)
let print_icfg (chan : out_channel) =
  let print_node node = ignore (fprintf chan "%a\n" d_cfgnode node) in 
  List.iter print_node !node_list

let print_edges chan edges =
  let count = ref 0 in
  let print_edge (n1,n2) =
    incr count;
    ignore(fprintf chan "%a -> %a [color=\"red\" label=\"%d\" fontcolor=\"green\"];" d_cfgnodename n1 d_cfgnodename n2 !count)
  in List.iter print_edge edges

let print_icfg_dotty (extra_edges : (node*node) list) =
  ignore (E.log "@[Printing iCFG as dot file..@.");
  let chan = open_out "icfg.dot" in
(*
  let print_global = function 
    | GFun(fd,_) -> print_cfg_channel chan fd
    | _ -> ()
  in 
*)
  ignore (fprintf chan "digraph iCFG {\n");
(*  iterGlobals f print_global;*)
  print_icfg chan;
  print_edges chan extra_edges;
  ignore(fprintf chan  "}\n");
  close_out chan

(* ================== END of Printing dotty files ================== *)
