---
title: "Sub_Async: Implementation Walkthrough"
subtitle: "Code-Focused Presentation"
author: "Sub_Async Project"
date: "January 2026"
---

# Outline

1. **Data Structures** — The state machine
2. **Core Algorithm** — Dependency resolution
3. **Operator Polymorphism** — Future-aware operators
4. **Case Study** — Diamond execution trace

---

# Part 1: Data Structures

---

# Future Status (future.ml)

```ocaml
type status =
  | Pending of expr * env * continuation list
  | Completed of value * int list    (* deps for GC *)
  | Dependent of dependency

type dependency = {
  depends_on: int list;
  compute: value list -> value;
  waiters: continuation list;
}
```

**Two sources:** `async` creates Pending, operators create Dependent.

---

# Global State (future.ml)

```ocaml
let table : (int, status) Hashtbl.t = Hashtbl.create 100
let ref_counts : (int, int) Hashtbl.t = Hashtbl.create 100
let next_id = ref 0
```

- `table`: Future ID → Status
- `ref_counts`: Reference counting for GC
- `next_id`: Fresh ID generator

---

# Scheduler (scheduler.ml)

```ocaml
let queue : task Queue.t = Queue.create ()

let schedule task = Queue.add task queue

let run_one_random () =
  if not (Queue.is_empty queue) then begin
    let idx = Random.int (Queue.length queue) in
    (* pick random task, execute it *)
  end
```

**Non-deterministic:** Simulates concurrent execution.

---

# Part 2: Core Algorithm

---

# Creating an Async Future

```ocaml
let create e env =
  let id = fresh_id () in
  Hashtbl.add table id (Pending (e, env, []));
  Scheduler.schedule (fun () ->
    !eval_cps_ref env e (fun v -> complete id v));
  id
```

1. Generate fresh ID
2. Add to table as `Pending`
3. Schedule evaluation task
4. Return ID immediately (non-blocking)

---

# Completing a Future

```ocaml
let rec complete id v =
  match Hashtbl.find_opt table id with
  | Some (Pending (_, _, ks)) ->
      Hashtbl.replace table id (Completed (v, []));
      List.iter (fun k -> k v) ks   (* Call all waiters *)
  | _ -> ()
```

1. Update status: `Pending → Completed`
2. Call all registered continuations

---

# Awaiting a Future

```ocaml
let await id k =
  incr_ref id;
  match Hashtbl.find_opt table id with
  | Some (Completed (v, _)) ->
      decr_ref id; k v              (* Already done *)
  | Some (Pending (e, env, ks)) ->
      let k' v = decr_ref id; k v in
      Hashtbl.replace table id (Pending (e, env, k'::ks))
  | Some (Dependent dep) ->
      let k' v = decr_ref id; k v in
      Hashtbl.replace table id 
        (Dependent { dep with waiters = k'::dep.waiters });
      check_and_resolve_dependent id
  | None -> runtime_error "invalid future"
```

---

# Creating a Dependent Future

```ocaml
let create_dependent_future depends_on compute =
  let id = fresh_id () in
  List.iter incr_ref depends_on;
  
  let all_done, values = check_dependencies depends_on in
  if all_done then begin
    Hashtbl.add table id (Completed (compute values, depends_on));
    id
  end else begin
    Hashtbl.add table id (Dependent { depends_on; compute; waiters=[] });
    List.iter (fun d -> register_listener d id) depends_on;
    id
  end
```

**Key:** If deps already done, resolve immediately.

---

# Dependency Resolution

```ocaml
let rec check_and_resolve_dependent id =
  match Hashtbl.find_opt table id with
  | Some (Dependent { depends_on; compute; waiters }) ->
      let all_done, values = check_dependencies depends_on in
      if all_done then begin
        let result = compute values in
        Hashtbl.replace table id (Completed (result, depends_on));
        List.iter decr_ref depends_on;   (* GC *)
        List.iter (fun k -> k result) waiters
      end
  | _ -> ()
```

**Cascade:** When #0 completes → check #1, #2 → check #3 → ...

---

# Part 3: Operator Polymorphism

---

# Binary Operator Template

```ocaml
let binary_int_op_commutative op_name int_op v1 v2 k =
  match v1, v2 with
  | Future id1, Future id2 ->
      let new_id = Future.create_dependent_future [id1; id2]
        (fun [v1; v2] -> Int (int_op (extract v1) (extract v2)))
      in k (Future new_id)
  | Future id, Int n | Int n, Future id ->
      let new_id = Future.create_dependent_future [id]
        (fun [v] -> Int (int_op (extract v) n))
      in k (Future new_id)
  | Int n1, Int n2 -> k (Int (int_op n1 n2))
  | _ -> runtime_error "type error"
```

---

# Using the Template (eval.ml)

```ocaml
| Plus (e1, e2) ->
    eval_cps env e1 (fun v1 ->
      eval_cps env e2 (fun v2 ->
        binary_int_op_commutative "Plus" (+) v1 v2 k))

| Minus (e1, e2) ->
    eval_cps env e1 (fun v1 ->
      eval_cps env e2 (fun v2 ->
        binary_int_op_ordered "Minus" (-) v1 v2 k))
```

**Pattern:** Evaluate operands, dispatch based on types.

---

# The Async Case (eval.ml)

```ocaml
| Async e' ->
    let id = Future.create e' env in
    k (Future id)
```

**That's it.** Create and return immediately.

---

# Part 4: Case Study

---

# Diamond: The Code

```ocaml
let base = async (100) in
let left = base + 10 in
let right = base + 20 in
left + right
```

---

# Diamond: Step 1

```ocaml
let base = async (100) in ...
```

**Action:**
- `Future.create (100) env` → ID #0
- `table[#0] = Pending(100, env, [])`
- `Scheduler.schedule(eval 100)`

**Returns:** `Future #0`

---

# Diamond: Step 2

```ocaml
let left = base + 10 in ...
```

**Action:**
- Evaluate `base` → `Future #0`
- Evaluate `10` → `Int 10`
- `binary_int_op` sees `(Future #0, Int 10)`
- `create_dependent_future [#0] (fun [v] -> v+10)` → ID #1
- `table[#1] = Dependent { depends_on=[#0]; ... }`

**Returns:** `Future #1`

---

# Diamond: Step 3

```ocaml
let right = base + 20 in ...
```

**Same pattern:**
- `create_dependent_future [#0] (fun [v] -> v+20)` → ID #2
- `table[#2] = Dependent { depends_on=[#0]; ... }`

**Returns:** `Future #2`

---

# Diamond: Step 4

```ocaml
left + right
```

**Action:**
- `binary_int_op` sees `(Future #1, Future #2)`
- `create_dependent_future [#1, #2] (fun [a,b] -> a+b)` → ID #3
- `table[#3] = Dependent { depends_on=[#1,#2]; ... }`

**Returns:** `Future #3` (this is the program result)

---

# Diamond: Resolution

```
Scheduler runs task for #0
  → eval (100) → complete(#0, 100)
  → check_and_resolve #1: deps=[#0] all done!
      → compute: 100+10=110, complete #1
  → check_and_resolve #2: deps=[#0] all done!
      → compute: 100+20=120, complete #2
  → check_and_resolve #3: deps=[#1,#2] all done!
      → compute: 110+120=230, complete #3

Final: 230
```

---

# Summary

| Component | Responsibility |
|-----------|----------------|
| `table` | Future ID → Status mapping |
| `create` | Async: schedule + return |
| `create_dependent_future` | Operator: register deps |
| `check_and_resolve` | Cascade resolution |
| `binary_int_op_*` | Type dispatch |

---

# Module Dependencies

```
syntax.ml (types)
    |
scheduler.ml (queue)
    |
future.ml (state machine)
    |
eval.ml (CPS evaluator)
```

**No circular imports.** `eval_cps_ref` breaks the cycle.

---

# Questions?
