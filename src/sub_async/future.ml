(** Future state machine and continuation store for async computations. *)

open Syntax

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error msg)

(** Continuation type: what to do with a value *)
type continuation = expr -> unit

(** Dependency information for dependent futures *)
type dependency = {
  depends_on: int list;              (* Future IDs this depends on *)
  compute: expr list -> expr;        (* How to combine results *)
  waiters: continuation list;        (* Continuations waiting for this *)
}

(** Future status in the state machine *)
type status =
  | Pending of expr * environment * continuation list
  | Completed of expr * int list  (* value + dependencies for GC *)
  | Dependent of dependency

(** Internal state *)
let table : (int, status) Hashtbl.t = Hashtbl.create 100
let ref_counts : (int, int) Hashtbl.t = Hashtbl.create 100
let next_id = ref 0
let verbose = ref true

(** Forward declaration of eval_cps (will be set by eval.ml) *)
let eval_cps_ref : (environment -> expr -> continuation -> unit) ref = 
  ref (fun _ _ _ -> failwith "eval_cps not initialized")

(** Generate fresh future ID *)
let fresh_id () =
  let id = !next_id in
  incr next_id;
  Hashtbl.add ref_counts id 1;
  id

(** Increment reference count *)
let incr_ref id =
  let count = Hashtbl.find_opt ref_counts id |> Option.value ~default:0 in
  Hashtbl.replace ref_counts id (count + 1);
  if !verbose then
    Printf.eprintf "[gc] Future #%d: refcount++ = %d\n%!" id (count + 1)

(** Decrement reference count and GC if zero *)
let rec decr_ref id =
  match Hashtbl.find_opt ref_counts id with
  | Some count when count > 1 ->
      Hashtbl.replace ref_counts id (count - 1);
      if !verbose then
        Printf.eprintf "[gc] Future #%d: refcount-- = %d\n%!" id (count - 1)
  | Some 1 ->
      (match Hashtbl.find_opt table id with
       | Some (Completed (_, deps)) when deps <> [] ->
           if !verbose then
             Printf.eprintf "[gc] Future #%d: releasing %d dependencies\n%!" id (List.length deps);
           List.iter decr_ref deps
       | _ -> ());
      Hashtbl.remove table id;
      Hashtbl.remove ref_counts id;
      if !verbose then
        Printf.eprintf "[gc] Future #%d: garbage collected\n%!" id
  | _ -> ()

(** Helper: extract int from completed future value *)
let extract_int v = match v with
  | Int n -> n
  | _ -> runtime_error "integer expected in dependency resolution"

(** Check if all dependencies are completed and collect their values *)
let check_dependencies ids =
  let rec loop acc = function
    | [] -> (true, List.rev acc)
    | id :: rest ->
        match Hashtbl.find_opt table id with
        | Some (Completed (v, _)) -> loop (v :: acc) rest
        | _ -> (false, [])
  in
  loop [] ids

(** Forward declaration for mutual recursion *)
let rec check_and_resolve_dependent id =
  match Hashtbl.find_opt table id with
  | Some (Dependent dep) ->
      let all_completed, values = check_dependencies dep.depends_on in
      if all_completed then begin
        let result = dep.compute values in
        Hashtbl.replace table id (Completed (result, dep.depends_on));
        List.iter decr_ref dep.depends_on;
        if !verbose then
          Printf.printf "[dependent] Future #%d resolved\n%!" id;
        List.iter (fun k -> k result) dep.waiters
      end
  | _ -> ()

(** Detect cycles in dependency graph *)
and has_cycle depends_on new_id =
  let rec check_path visited current_id =
    if List.mem current_id visited then
      true
    else
      match Hashtbl.find_opt table current_id with
      | Some (Dependent dep) ->
          List.exists (check_path (current_id :: visited)) dep.depends_on
      | _ -> false
  in
  List.exists (check_path [new_id]) depends_on

(** Register a dependent future to listen for completion of a dependency *)
and register_dependent_listener dep_id listener_id =
  match Hashtbl.find_opt table dep_id with
  | Some (Pending (e, env, ks)) ->
      let notify_k _ = check_and_resolve_dependent listener_id in
      Hashtbl.replace table dep_id (Pending (e, env, notify_k :: ks))
  | Some (Completed _) ->
      check_and_resolve_dependent listener_id
  | Some (Dependent dep) ->
      let notify_k _ = check_and_resolve_dependent listener_id in
      Hashtbl.replace table dep_id (Dependent {
        dep with waiters = notify_k :: dep.waiters
      })
  | None -> runtime_error ("invalid future dependency #" ^ string_of_int dep_id)

(** Create a dependent future that waits for other futures *)
let create_dependent_future depends_on compute =
  let id = fresh_id () in
  List.iter incr_ref depends_on;
  
  if has_cycle depends_on id then
    runtime_error ("circular dependency detected for future #" ^ string_of_int id);
  
  let all_completed, values = check_dependencies depends_on in
  
  if all_completed then begin
    let result = compute values in
    Hashtbl.add table id (Completed (result, depends_on));
    if !verbose then
      Printf.printf "[dependent] Future #%d immediately completed\n%!" id;
    id
  end else begin
    let dep = {
      depends_on = depends_on;
      compute = compute;
      waiters = [];
    } in
    Hashtbl.add table id (Dependent dep);
    List.iter (fun dep_id -> register_dependent_listener dep_id id) depends_on;
    if !verbose then
      Printf.printf "[dependent] Future #%d depends on [%s]\n%!" 
        id (String.concat "; " (List.map string_of_int depends_on));
    id
  end

(** Complete a future and call all waiting continuations *)
let rec complete id v =
  match Hashtbl.find_opt table id with
  | Some (Pending (_, _, ks)) ->
      Hashtbl.replace table id (Completed (v, []));
      if !verbose && ks <> [] then
        Printf.printf "[complete] Future #%d calling %d waiting continuations\n%!" id (List.length ks);
      List.iter (fun k -> k v) ks
  | _ -> ()

(** Create a new future and trigger async evaluation *)
and create e env =
  let id = fresh_id () in
  Hashtbl.add table id (Pending (e, env, []));
  if !verbose then
    Printf.printf "[async] Created future #%d, scheduling evaluation\n%!" id;
  Scheduler.schedule (fun () ->
    if !verbose then
      Printf.printf "[🎲 running] Future #%d starting evaluation\n%!" id;
    !eval_cps_ref env e (fun v ->
      if !verbose then
        Printf.printf "[✓] Future #%d completed with value\n%!" id;
      complete id v));
  id

(** Register a continuation to await a future's result *)
and await id k =
  incr_ref id;
  match Hashtbl.find_opt table id with
  | Some (Completed (v, _)) ->
      if !verbose then
        Printf.printf "[await] Future #%d already completed, calling continuation immediately\n%!" id;
      decr_ref id;
      k v
  | Some (Pending (e, env, ks)) ->
      if !verbose then
        Printf.printf "[await] Future #%d pending, registering continuation\n%!" id;
      let k' v = decr_ref id; k v in
      Hashtbl.replace table id (Pending (e, env, k'::ks))
  | Some (Dependent dep) ->
      if !verbose then
        Printf.printf "[await] Future #%d is dependent, registering waiter\n%!" id;
      let k' v = decr_ref id; k v in
      Hashtbl.replace table id (Dependent {
        dep with waiters = k' :: dep.waiters
      });
      check_and_resolve_dependent id
  | None -> runtime_error ("invalid future #" ^ string_of_int id)
