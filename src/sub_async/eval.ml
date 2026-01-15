(** CPS-style evaluation semantics with continuation-based async. *)

open Syntax

exception Runtime_error of string

(** [runtime_error msg] reports a runtime error by raising [Runtime_error msg] *)
let runtime_error msg = raise (Runtime_error msg)

(** Continuation type: what to do with a value *)
type continuation = Syntax.expr -> unit

(** Work queue for trampoline-based scheduling *)
module Scheduler = struct
  type task = unit -> unit
  
  let queue : task Queue.t = Queue.create ()
  let verbose = ref true
  
  (** Schedule a task for later execution *)
  let schedule task =
    Queue.add task queue
  
  (** Run all scheduled tasks until queue is empty *)
  let run_all () =
    while not (Queue.is_empty queue) do
      let task = Queue.take queue in
      task ()
    done
  
  (** Pick a random task from queue and execute it *)
  let run_one_random () =
    if not (Queue.is_empty queue) then begin
      let len = Queue.length queue in
      let idx = Random.int len in
      (* Convert to list, pick one, put rest back *)
      let tasks = Queue.fold (fun acc t -> t::acc) [] queue in
      Queue.clear queue;
      let rec rebuild i = function
        | [] -> ()
        | t::rest ->
            if i = idx then begin
              if !verbose then
                Printf.printf "[scheduler] Executing randomly selected task\n%!";
              t ()  (* Execute selected task *)
            end else
              Queue.add t queue;
            rebuild (i+1) rest
      in
      rebuild 0 (List.rev tasks)
    end
  
  let reset () =
    Queue.clear queue
end

(** ContinuationStore: stores continuations waiting for async computations *)
module ContinuationStore = struct
  type dependency = {
    depends_on: int list;              (* Future IDs this depends on *)
    compute: expr list -> expr;        (* How to combine results *)
    waiters: continuation list;        (* Continuations waiting for this *)
  }

  type status =
    | Pending of expr * environment * continuation list
    | Completed of expr
    | Dependent of dependency          (* 👈 NEW: Dependent Future *)

  let table : (int, status) Hashtbl.t = Hashtbl.create 100
  let next_id = ref 0
  let verbose = ref true  (* Control logging *)

  (** Generate fresh future ID *)
  let fresh_id () =
    let id = !next_id in
    incr next_id;
    id

  (** Forward declaration of eval_cps *)
  let eval_cps_ref : (environment -> expr -> continuation -> unit) ref = 
    ref (fun _ _ _ -> failwith "eval_cps not initialized")

  (** Helper: extract int from completed future value *)
  let extract_int v = match v with
    | Int n -> n
    | _ -> runtime_error "integer expected in dependency resolution"

  (** Helper: extract bool from completed future value *)
  let extract_bool v = match v with
    | Bool b -> b
    | _ -> runtime_error "boolean expected in dependency resolution"

  (** Check if all dependencies are completed and collect their values *)
  let check_dependencies ids =
    let rec loop acc = function
      | [] -> (true, List.rev acc)
      | id :: rest ->
          match Hashtbl.find_opt table id with
          | Some (Completed v) -> loop (v :: acc) rest
          | _ -> (false, [])
    in
    loop [] ids

  (** Forward declaration for mutual recursion *)
  let rec check_and_resolve_dependent id =
    match Hashtbl.find_opt table id with
    | Some (Dependent dep) ->
        let all_completed, values = check_dependencies dep.depends_on in
        if all_completed then begin
          (* All dependencies ready, compute result *)
          let result = dep.compute values in
          Hashtbl.replace table id (Completed result);
          
          if !verbose then
            Printf.printf "[dependent] Future #%d resolved\n%!" id;
          
          (* Notify all waiters *)
          List.iter (fun k -> k result) dep.waiters
        end
    | _ -> ()

  (** Register a dependent future to listen for completion of a dependency *)
  and register_dependent_listener dep_id listener_id =
    match Hashtbl.find_opt table dep_id with
    | Some (Pending (e, env, ks)) ->
        (* When dep_id completes, check if listener can be resolved *)
        let notify_k _ =
          check_and_resolve_dependent listener_id
        in
        Hashtbl.replace table dep_id (Pending (e, env, notify_k :: ks))
    
    | Some (Completed _) ->
        (* Dependency already completed, check listener immediately *)
        check_and_resolve_dependent listener_id
    
    | Some (Dependent dep) ->
        (* Dependency itself is Dependent, add to its waiters *)
        let notify_k _ = check_and_resolve_dependent listener_id in
        Hashtbl.replace table dep_id (Dependent {
          dep with waiters = notify_k :: dep.waiters
        })
    
    | None -> runtime_error ("invalid future dependency #" ^ string_of_int dep_id)

  (** Create a dependent future that waits for other futures *)
  and create_dependent_future depends_on compute =
    let id = fresh_id () in
    
    (* Check if dependencies are already completed *)
    let all_completed, values = check_dependencies depends_on in
    
    if all_completed then begin
      (* All dependencies ready, compute immediately *)
      let result = compute values in
      Hashtbl.add table id (Completed result);
      if !verbose then
        Printf.printf "[dependent] Future #%d immediately completed\n%!" id;
      id
    end else begin
      (* Some dependencies pending, register as Dependent *)
      let dep = {
        depends_on = depends_on;
        compute = compute;
        waiters = [];
      } in
      Hashtbl.add table id (Dependent dep);
      
      (* Register listener for each dependency *)
      List.iter (fun dep_id ->
        register_dependent_listener dep_id id
      ) depends_on;
      
      if !verbose then
        Printf.printf "[dependent] Future #%d depends on [%s]\n%!" 
          id (String.concat "; " (List.map string_of_int depends_on));
      id
    end

  (** Complete a future and automatically call all waiting continuations *)
  let rec complete id v =
    match Hashtbl.find_opt table id with
    | Some (Pending (_, _, ks)) ->
        Hashtbl.replace table id (Completed v);
        if !verbose && ks <> [] then
          Printf.printf "[complete] Future #%d calling %d waiting continuations\n%!" id (List.length ks);
        List.iter (fun k -> k v) ks  (* 🔥 Auto-call all ks *)
    | _ -> ()

  (** Create a new future and trigger async evaluation *)
  and create e env =
    let id = fresh_id () in
    Hashtbl.add table id (Pending (e, env, []));
    if !verbose then
      Printf.printf "[async] Created future #%d, scheduling evaluation\n%!" id;
    (* Schedule async evaluation instead of running immediately *)
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
    match Hashtbl.find_opt table id with
    | Some (Completed v) ->
        if !verbose then
          Printf.printf "[await] Future #%d already completed, calling continuation immediately\n%!" id;
        k v  (* Already completed, call k immediately *)
    | Some (Pending (e, env, ks)) ->
        if !verbose then
          Printf.printf "[await] Future #%d pending, registering continuation\n%!" id;
        Hashtbl.replace table id (Pending (e, env, k::ks))  (* Store k *)
    | Some (Dependent dep) ->
        (* 👈 NEW: Handle Dependent futures *)
        if !verbose then
          Printf.printf "[await] Future #%d is dependent, registering waiter\n%!" id;
        Hashtbl.replace table id (Dependent {
          dep with waiters = k :: dep.waiters
        });
        (* Try to resolve immediately in case dependencies are ready *)
        check_and_resolve_dependent id
    | None -> runtime_error ("invalid future #" ^ string_of_int id)

  (** Reset state (for testing) *)
  let reset () =
    Hashtbl.clear table;
    next_id := 0
end

(** [lookup_value x env] looks up the value of [x] in environment [env]. *)
let lookup_value x env =
  try List.assoc x env with Not_found -> runtime_error ("unknown variable " ^ x)

(** Helper: extract int from value, awaiting if it's a future *)
let rec value_to_int v k = match v with
  | Int n -> k n
  | Future id -> ContinuationStore.await id (fun v' -> value_to_int v' k)
  | _ -> runtime_error "integer expected"

(** Helper: extract bool from value, awaiting if it's a future *)
let rec value_to_bool v k = match v with
  | Bool b -> k b
  | Future id -> ContinuationStore.await id (fun v' -> value_to_bool v' k)
  | _ -> runtime_error "boolean expected"

(** [eval_cps env e k] evaluates expression [e] in environment [env],
    then calls continuation [k] with the result. *)
let rec eval_cps env e k = match e with
  | Var x ->
      let v = lookup_value x env in
      (* 👇 Changed: Don't auto-await! Let Future values propagate *)
      k v

  | Int _ as e -> k e
  | Bool _ as e -> k e

  | Plus (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          (* 👇 Future computation graph: check if operands are futures *)
          match v1, v2 with
          | Future id1, Future id2 ->
              (* Both are futures: create dependent future *)
              let new_id = ContinuationStore.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> Int (ContinuationStore.extract_int v1 + ContinuationStore.extract_int v2)
                  | _ -> runtime_error "dependency mismatch in Plus")
              in
              k (Future new_id)  (* 👈 Return immediately! *)
          
          | Future id, Int n | Int n, Future id ->
              (* One is future, one is value *)
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Int (ContinuationStore.extract_int v + n)
                  | _ -> runtime_error "dependency mismatch in Plus")
              in
              k (Future new_id)
          
          | Int n1, Int n2 ->
              (* Both are values: compute directly *)
              k (Int (n1 + n2))
          
          | _ -> runtime_error "integers expected in Plus"))

  | Minus (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1, v2 with
          | Future id1, Future id2 ->
              let new_id = ContinuationStore.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> Int (ContinuationStore.extract_int v1 - ContinuationStore.extract_int v2)
                  | _ -> runtime_error "dependency mismatch in Minus")
              in
              k (Future new_id)
          
          | Future id, Int n ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Int (ContinuationStore.extract_int v - n)
                  | _ -> runtime_error "dependency mismatch in Minus")
              in
              k (Future new_id)
          
          | Int n, Future id ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Int (n - ContinuationStore.extract_int v)
                  | _ -> runtime_error "dependency mismatch in Minus")
              in
              k (Future new_id)
          
          | Int n1, Int n2 ->
              k (Int (n1 - n2))
          
          | _ -> runtime_error "integers expected in Minus"))

  | Times (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1, v2 with
          | Future id1, Future id2 ->
              let new_id = ContinuationStore.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> Int (ContinuationStore.extract_int v1 * ContinuationStore.extract_int v2)
                  | _ -> runtime_error "dependency mismatch in Times")
              in
              k (Future new_id)
          
          | Future id, Int n | Int n, Future id ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Int (ContinuationStore.extract_int v * n)
                  | _ -> runtime_error "dependency mismatch in Times")
              in
              k (Future new_id)
          
          | Int n1, Int n2 ->
              k (Int (n1 * n2))
          
          | _ -> runtime_error "integers expected in Times"))

  | Divide (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1, v2 with
          | Future id1, Future id2 ->
              let new_id = ContinuationStore.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> 
                      let n1 = ContinuationStore.extract_int v1 in
                      let n2 = ContinuationStore.extract_int v2 in
                      if n2 = 0 then runtime_error "division by zero"
                      else Int (n1 / n2)
                  | _ -> runtime_error "dependency mismatch in Divide")
              in
              k (Future new_id)
          
          | Future id, Int n ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> 
                      if n = 0 then runtime_error "division by zero"
                      else Int (ContinuationStore.extract_int v / n)
                  | _ -> runtime_error "dependency mismatch in Divide")
              in
              k (Future new_id)
          
          | Int n, Future id ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> 
                      let divisor = ContinuationStore.extract_int v in
                      if divisor = 0 then runtime_error "division by zero"
                      else Int (n / divisor)
                  | _ -> runtime_error "dependency mismatch in Divide")
              in
              k (Future new_id)
          
          | Int n1, Int n2 ->
              if n2 = 0 then runtime_error "division by zero"
              else k (Int (n1 / n2))
          
          | _ -> runtime_error "integers expected in Divide"))

  | Equal (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1, v2 with
          | Future id1, Future id2 ->
              let new_id = ContinuationStore.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> Bool (ContinuationStore.extract_int v1 = ContinuationStore.extract_int v2)
                  | _ -> runtime_error "dependency mismatch in Equal")
              in
              k (Future new_id)
          
          | Future id, Int n | Int n, Future id ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Bool (ContinuationStore.extract_int v = n)
                  | _ -> runtime_error "dependency mismatch in Equal")
              in
              k (Future new_id)
          
          | Int n1, Int n2 ->
              k (Bool (n1 = n2))
          
          | _ -> runtime_error "integers expected in Equal"))

  | Less (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1, v2 with
          | Future id1, Future id2 ->
              let new_id = ContinuationStore.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> Bool (ContinuationStore.extract_int v1 < ContinuationStore.extract_int v2)
                  | _ -> runtime_error "dependency mismatch in Less")
              in
              k (Future new_id)
          
          | Future id, Int n ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Bool (ContinuationStore.extract_int v < n)
                  | _ -> runtime_error "dependency mismatch in Less")
              in
              k (Future new_id)
          
          | Int n, Future id ->
              let new_id = ContinuationStore.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> Bool (n < ContinuationStore.extract_int v)
                  | _ -> runtime_error "dependency mismatch in Less")
              in
              k (Future new_id)
          
          | Int n1, Int n2 ->
              k (Bool (n1 < n2))
          
          | _ -> runtime_error "integers expected in Less"))

  | And (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          value_to_bool v1 (fun b1 ->
            value_to_bool v2 (fun b2 ->
              k (Bool (b1 && b2))))))

  | Or (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          value_to_bool v1 (fun b1 ->
            value_to_bool v2 (fun b2 ->
              k (Bool (b1 || b2))))))

  | Not e1 ->
      eval_cps env e1 (fun v1 ->
        value_to_bool v1 (fun b ->
          k (Bool (not b))))

  | If (e1, e2, e3) ->
      eval_cps env e1 (fun v1 ->
        value_to_bool v1 (fun b ->
          if b then eval_cps env e2 k
          else eval_cps env e3 k))

  | Fun (f, x, _, _, e) ->
      let rec c = Closure ((f,c)::env, x, e) in
      k c

  | Closure _ as e -> k e

  | Let (x, e1, e2) ->
      eval_cps env e1 (fun v1 ->
        (* No scheduling here - just continue *)
        eval_cps ((x, v1)::env) e2 k)

  | App (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1 with
          | Closure (env', x, e) ->
              eval_cps ((x, v2)::env') e k
          | _ -> runtime_error "invalid application"))

  | Record rs ->
      let rec eval_fields fields acc = match fields with
        | [] -> k (Record (List.rev acc))
        | (l, e)::rest ->
            eval_cps env e (fun v ->
              eval_fields rest ((l, v)::acc))
      in
      eval_fields rs []

  | Project (e, l) ->
      eval_cps env e (fun v ->
        match v with
        | Record vs ->
            (match List.assoc_opt l vs with
             | Some v' -> k v'
             | None -> runtime_error ("field " ^ l ^ " not found"))
        | _ -> runtime_error "record expected")

  | Async e' ->
      (* Create future and immediately continue, don't wait *)
      let id = ContinuationStore.create e' env in
      k (Future id)

  | Future _ as e -> k e

(* Initialize the reference to eval_cps *)
let () = ContinuationStore.eval_cps_ref := eval_cps

(** Wrapper for direct-style evaluation (for compatibility) *)
let eval env e =
  let result = ref None in
  let final_k v =
    (* If result is a future, await it before storing *)
    match v with
    | Future id ->
        if !ContinuationStore.verbose then
          Printf.printf "[main] Result is Future #%d, awaiting...\n%!" id;
        ContinuationStore.await id (fun final_v ->
          result := Some final_v;
          if !ContinuationStore.verbose then
            Printf.printf "[main] Final result obtained\n%!")
    | _ ->
        result := Some v;
        if !ContinuationStore.verbose then
          Printf.printf "[main] Final result obtained\n%!"
  in
  eval_cps env e final_k;
  (* Run scheduled tasks with random selection *)
  let max_steps = ref 1000 in
  while !max_steps > 0 && not (Queue.is_empty Scheduler.queue) do
    Scheduler.run_one_random ();
    decr max_steps
  done;
  if !max_steps = 0 then
    runtime_error "evaluation exceeded maximum steps";
  match !result with
  | Some v -> v
  | None -> runtime_error "evaluation did not complete"
