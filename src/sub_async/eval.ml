(** CPS-style evaluation semantics with continuation-based async. *)

open Syntax

(** Re-export for compatibility *)
exception Runtime_error = Future.Runtime_error

let runtime_error = Future.runtime_error

(** [lookup_value x env] looks up the value of [x] in environment [env]. *)
let lookup_value x env =
  try List.assoc x env with Not_found -> runtime_error ("unknown variable " ^ x)

(** Helper: extract int from value, awaiting if it's a future *)
let rec value_to_int v k = match v with
  | Int n -> k n
  | Future id -> Future.await id (fun v' -> value_to_int v' k)
  | _ -> runtime_error "integer expected"

(** Helper: extract bool from value, awaiting if it's a future *)
let rec value_to_bool v k = match v with
  | Bool b -> k b
  | Future id -> Future.await id (fun v' -> value_to_bool v' k)
  | _ -> runtime_error "boolean expected"

(** Maximum evaluation steps to prevent infinite loops *)
let max_eval_steps = 1000

(** Helper: create binary int operation with Future support (commutative) *)
let binary_int_op_commutative op_name int_op v1 v2 k =
  match v1, v2 with
  | Future id1, Future id2 ->
      let new_id = Future.create_dependent_future [id1; id2]
        (fun values -> match values with
          | [v1; v2] -> Int (int_op (Future.extract_int v1) (Future.extract_int v2))
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Future id, Int n | Int n, Future id ->
      let new_id = Future.create_dependent_future [id]
        (fun values -> match values with
          | [v] -> Int (int_op (Future.extract_int v) n)
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Int n1, Int n2 ->
      k (Int (int_op n1 n2))
  | _ -> runtime_error ("integers expected in " ^ op_name)

(** Helper: create binary int operation with Future support (non-commutative) *)
let binary_int_op_ordered op_name int_op v1 v2 k =
  match v1, v2 with
  | Future id1, Future id2 ->
      let new_id = Future.create_dependent_future [id1; id2]
        (fun values -> match values with
          | [v1; v2] -> Int (int_op (Future.extract_int v1) (Future.extract_int v2))
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Future id, Int n ->
      let new_id = Future.create_dependent_future [id]
        (fun values -> match values with
          | [v] -> Int (int_op (Future.extract_int v) n)
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Int n, Future id ->
      let new_id = Future.create_dependent_future [id]
        (fun values -> match values with
          | [v] -> Int (int_op n (Future.extract_int v))
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Int n1, Int n2 ->
      k (Int (int_op n1 n2))
  | _ -> runtime_error ("integers expected in " ^ op_name)

(** Helper: create comparison operation with Future support *)
let binary_cmp_op op_name cmp_op v1 v2 k =
  match v1, v2 with
  | Future id1, Future id2 ->
      let new_id = Future.create_dependent_future [id1; id2]
        (fun values -> match values with
          | [v1; v2] -> Bool (cmp_op (Future.extract_int v1) (Future.extract_int v2))
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Future id, Int n ->
      let new_id = Future.create_dependent_future [id]
        (fun values -> match values with
          | [v] -> Bool (cmp_op (Future.extract_int v) n)
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Int n, Future id ->
      let new_id = Future.create_dependent_future [id]
        (fun values -> match values with
          | [v] -> Bool (cmp_op n (Future.extract_int v))
          | _ -> runtime_error ("dependency mismatch in " ^ op_name))
      in
      k (Future new_id)
  | Int n1, Int n2 ->
      k (Bool (cmp_op n1 n2))
  | _ -> runtime_error ("integers expected in " ^ op_name)

(** [eval_cps env e k] evaluates expression [e] in environment [env],
    then calls continuation [k] with the result. *)
let rec eval_cps env e k = match e with
  | Var x -> k (lookup_value x env)
  | Int _ as e -> k e
  | Bool _ as e -> k e

  | Plus (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          binary_int_op_commutative "Plus" ( + ) v1 v2 k))

  | Minus (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          binary_int_op_ordered "Minus" ( - ) v1 v2 k))

  | Times (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          binary_int_op_commutative "Times" ( * ) v1 v2 k))

  | Divide (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          match v1, v2 with
          | Future id1, Future id2 ->
              let new_id = Future.create_dependent_future [id1; id2]
                (fun values -> match values with
                  | [v1; v2] -> 
                      let n1 = Future.extract_int v1 in
                      let n2 = Future.extract_int v2 in
                      if n2 = 0 then runtime_error "division by zero"
                      else Int (n1 / n2)
                  | _ -> runtime_error "dependency mismatch in Divide")
              in
              k (Future new_id)
          | Future id, Int n ->
              let new_id = Future.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> 
                      if n = 0 then runtime_error "division by zero"
                      else Int (Future.extract_int v / n)
                  | _ -> runtime_error "dependency mismatch in Divide")
              in
              k (Future new_id)
          | Int n, Future id ->
              let new_id = Future.create_dependent_future [id]
                (fun values -> match values with
                  | [v] -> 
                      let divisor = Future.extract_int v in
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
          binary_cmp_op "Equal" ( = ) v1 v2 k))

  | Less (e1, e2) ->
      eval_cps env e1 (fun v1 ->
        eval_cps env e2 (fun v2 ->
          binary_cmp_op "Less" ( < ) v1 v2 k))

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
      let id = Future.create e' env in
      k (Future id)

  | Future _ as e -> k e

(* Initialize the reference to eval_cps in Future module *)
let () = Future.eval_cps_ref := eval_cps

(** Wrapper for direct-style evaluation (for compatibility) *)
let eval env e =
  let result = ref None in
  let final_k v =
    match v with
    | Future id ->
        if !Future.verbose then
          Printf.printf "[main] Result is Future #%d, awaiting...\n%!" id;
        Future.await id (fun final_v ->
          result := Some final_v;
          if !Future.verbose then
            Printf.printf "[main] Final result obtained\n%!");
        Future.decr_ref id
    | _ ->
        result := Some v;
        if !Future.verbose then
          Printf.printf "[main] Final result obtained\n%!"
  in
  eval_cps env e final_k;
  let steps_remaining = ref max_eval_steps in
  while !steps_remaining > 0 && not (Scheduler.is_empty ()) do
    Scheduler.run_one_random ();
    decr steps_remaining
  done;
  if !steps_remaining = 0 then
    runtime_error "evaluation exceeded maximum steps";
  match !result with
  | Some v -> v
  | None -> runtime_error "evaluation did not complete"
