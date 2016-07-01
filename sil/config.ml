(*
 *
 * Copyright (c) 2006-2008,
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk>
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 * All rights reserved.
 *)

Format.set_margin 100

let set_minor_heap_size nMb = (* increase the minor heap size to speed up gc *)
  let ctrl = Gc.get () in
  let oneMb = 1048576 in
  let new_size = max ctrl.Gc.minor_heap_size (nMb*oneMb)
  in Gc.set {ctrl with Gc.minor_heap_size=new_size}

let () = set_minor_heap_size 1

let tick = ref false

(** String to append to the proc name when considered a callee during execution of function calls (needed for recursion) *)
let callee_suffix = "|callee"

(** Flag for footprint discovery mode *)
let footprint = ref false

(* Flag set when --dofootprint is used *)
let footprint_analysis = ref false

(* Flag set when we want to keep path information for each state *)
let keep_path_info = ref false

(* Timeout in seconds for each function *)
let timeout_footprint = ref 0
let timeout_re_exe = ref 0
let timeout () = if !footprint then !timeout_footprint else !timeout_re_exe

(* Use incremental analysis which saves specs to directory db *)
let incremental = ref false

(* Re-analyze procedures even if the .spec file can be found in the db *)
let re_analyze = ref false

(* Name of the database directory for incremental mode *)
let db_dir = ref "/tmp/db"
let abd_background = "abductor_background.jpg"

(* Current file name *)
let curr_filename = ref ""

(* Lines of code in original file *)
let loc = ref 0

(* Number of cores to be used for parallel execution *)
let num_cores = ref 1

(* Maximum number of processes to be used for parallel execution *)
let max_num_proc = ref 0

(* Flag set when running in a child process (thus changes to global state will be lost *) 
let in_child_process = ref false

(* Monitor the size of the props, and print every time the current max is exceeded *) 
let monitor_prop_size = ref false

(* If set, filter out the props which seem to be coming from failure of list abstraction *) 
let filtering = ref false


(** Flag for test mode *)
let test = ref false

(** Flag for the on-the-fly predicate discovery *)
let on_the_fly = ref true

(** Flag for turning on the join operator 
    (only for the interprocedural analysis)

    0 = nowhere
    1 = right before function calls
    2 = 1 + at the ends of loops 
    3 = 2 + at the meeting points of the outermost if-then-else branches
    4 = 3 + at the meeting points of all if-then-else branches
**)

let join_level = ref 3

(** Flag for turning on the optimization based on locality 
    0 = no
    1 = based on reachability
**)

let undo_join = ref false

let locality_level = ref 1

(** Flag for turning on the transformation that 
    null is assigned to a program variable when it becomes dead.
**)

let liveness = ref true

(** Flag for using the nonempty lseg only **)

let nelseg = ref false

(** Flag for abstracting fields of structs 
    0 = no
    1 = forget some fields during matching (and so lseg abstraction)
 **)

let abs_struct = ref 1

(** Flag for abstracting numerical values
    0 = no abstraction.
    1 = abstract big integers based on the given bound and evaluate
        all expressions abstractly.
    2 = 1 + abstract constant integer values during join. 
 **)

let abs_val = ref 1

(** Flag for garbage collection of summary data at procedure exit
    0 = no
    1 = remove observers for the procedure and mark summaries as complete
    2 = also remove intermediate states of the procedure from the join tables
    3 = also remove intermediate states of the procedure from todo and visited tables
*)

let gc_summaries = ref 1

(** Flag for ignoring arrays and pointer arithmetic. 
    0 = treats both features soundly. 
    1 = assumes that the size of every array is infinite. 
    2 = assumes that all heap dereferences via array indexing and pointer arithmetic are correct.
*)

let array_level = ref 2

(** Flag for forgetting memory leak 
    false = no
    true  = forget leaked memory cells during abstraction
*)

let allowleak = ref false

(** Bound for integer values to keep *)

let int_bound = ref 10000000

(** Flag to dotty-print structs in full, i.e., with dangling pointers  *)
let condensed_dotty = ref false

(** Flag to turn on automatic skip transformation of extern void functions*)
let automatic_skip = ref false

(** Flag to tune the final information-loss check used by the join 
    0 = use the most aggressive join for preconditions
    1 = use the least aggressive join for preconditions
*)
let join_cond = ref 1 

(** Flag to tune the level of applying the meet operator for 
    preconditions during the footprint analysis.
    0 = do not use the meet.
    1 = use the meet.
*)
let meet_level = ref 0 

(** Flag to tune the strictness of checks for the splitting fields model.
    0 = no checks during re-execution
    1 = re-execution gives memory errors when we access fields which are not there, and malloc allocates all the fields *)
let splitting_fields_level = ref 0

(** Flag to tune the level of abstracting the postconditions of specs discovered
    by the footprint analysis.
    0 = nothing special.
    1 = filter out redundant posts implied by other posts. *)
let spec_abs_level = ref 1 

(* if true prints a dotty file per specs instead of all specs of a procedure in one file *)
let separate_dotty_specs = ref false
