---
title: "Sub_Async: Operational Semantics"
subtitle: "5 Core Rules for Implicit Async Coordination"
author: "Chen Tianhao"
date: "January 2026"
classoption: "aspectratio=169"
theme: "metropolis"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{amssymb}
---

## Outline

1. **Language Motivation**: Space/Time Decoupling (WeChat Analogy)
2. **Formalization Motivation**: Externalize runtime state
3. **Configuration**: $\langle e, s \rangle$ where $s = (\rho, \Phi, Q)$
4. **5 Core Rules**: E-ASYNC, E-SCHEDULE, E-COMPLETE, E-LIFT-OP, E-RESOLVE
5. **Comparison with Aeff**

---

## Why Sub_Async? (Language Motivation)

| Rule | WeChat Analogy | Key Insight |
|------|---------------|-------------|
| **E-ASYNC** | Post task to group | Space decoupling |
| **E-SCHEDULE** | Whoever grabs it | Non-determinism |
| **E-COMPLETE** | Auto-notify on done | Continuation-based notify |
| **E-LIFT-OP** | Register dependency | No await, build graph |
| **E-RESOLVE** | Cascade trigger | Auto-propagation |

**Core innovation**: Operators detect Futures $\to$ implicit parallelism

---

## WeChat Group Analogy

| Concept | WeChat Group | Sub_Async |
|---------|--------------|-----------|
| Post task | "@everyone: fetch data" | `async e` |
| Who picks up | Whoever grabs it first | `Scheduler.run_one_random()` |
| Notify completion | "Done! @you" | `complete id v` |
| Auto-dependency | "Wait for both, then compute" | `create_dependent_future` |

**Core idea**: Post without specifying who (space decoupling), return immediately (time decoupling)

---

## Why Formalize? (The "Nothing Hidden" Problem)

**Aeff**: Parallel processes explicit in syntax

```
P || Q       (* Parallelism visible in AST *)
```

**Sub_Async**: Scheduler and Future table "hidden" in OCaml runtime

```ocaml
Hashtbl.add table id (Pending ...)   (* Where is this in semantics? *)
Scheduler.schedule (fun () -> ...)   (* Where is this? *)
```

**Solution**: Externalize into Configuration.

---

## Configuration

$$\langle e, s \rangle \quad \text{where } s = (\rho, \Phi, Q)$$

| Component | Meaning | OCaml Implementation |
|-----------|---------|---------------------|
| $\rho$ | Environment | `env : (string * value) list` |
| $\Phi$ | Future table | `Hashtbl : id -> status` |
| $Q$ | Task queue | `Scheduler.queue` |

**Update notation**:

- $s[id \mapsto v]$ — update $\Phi(id) = v$ (modify Future table)
- $s \oplus id$ — $Q := Q \cup \{id\}$ (add task to queue)
- $s \ominus id$ — $Q := Q \backslash \{id\}$ (remove task from queue)

<!-- These are **shorthand** for state changes. Instead of writing $(ρ, Φ', Q')$ every time, we write operations on $s$.

**Example**: $s[id \mapsto \text{Pending}(...)] \oplus id$ means "update Future table AND add to queue" -->

---

## Future Status (State Machine)

```ocaml
status ::= Pending(e, rho, ks)     (* Scheduled, not complete *)
         | Completed(v)            (* Done *)
         | Dependent(deps, f, ks)  (* Waiting for dependencies *)
```

**Transitions**:

- $\text{Pending} \xrightarrow{\text{E-COMPLETE}} \text{Completed}$
- $\text{Dependent} \xrightarrow{\text{E-RESOLVE}} \text{Completed}$
- `async e` creates Pending

---

## Rule 1: E-ASYNC

**Formal**:

$$\frac{id \text{ fresh}}{\langle \texttt{async } e, s \rangle \to \langle \text{Future}(id), s[id \mapsto \text{Pending}(e, s.\rho, [])] \oplus id \rangle} \text{ (E-ASYNC)}$$

**Intuition**: `async e` immediately returns `Future(id)`, schedules task.

---

## E-ASYNC: WeChat Analogy

```
[You]: "@everyone: compute expensive_task"
       (post to group, don't wait for reply)
       
[System]: Returns Future #0 immediately
          Task added to queue Q
```

**Key**: Fire and forget. Don't specify who. Don't wait.

---

## E-ASYNC: OCaml Code

```ocaml
(* eval.ml *)
| Async e' ->
    let id = Future.create e' env in
    k (Future id)

(* future.ml *)
let create e env =
  let id = fresh_id () in
  Hashtbl.add table id (Pending (e, env, []));  (* Phi[id |-> ...] *)
  Scheduler.schedule (fun () -> ...);           (* Q + id *)
  id
```

---

## Rule 2: E-SCHEDULE

**Formal**:

$$\frac{id \in s.Q \quad s.\Phi(id) = \text{Pending}(e', \rho', ks)}{\langle v, s \rangle \to \langle v, s' \rangle} \text{ (E-SCHEDULE)}$$

**Intuition**: When main expression is a value, pick a pending task to run.

---

## E-SCHEDULE: WeChat Analogy

```
[Three tasks waiting in the group]

Task #0: "fetch user info"
Task #1: "validate permissions"  
Task #2: "check quota"

[Alice]: (randomly grabs Task #1) "I'll do validation"
```

**Key**: Whoever grabs it, does it (non-deterministic scheduling).

---

## E-SCHEDULE: OCaml Code

```ocaml
(* eval.ml - main loop *)
while !steps_remaining > 0 && not (Scheduler.is_empty ()) do
  Scheduler.run_one_random ();    (* Non-deterministic! *)
  decr steps_remaining
done;

(* scheduler.ml *)
let run_one_random () =
  let idx = Random.int (Queue.length queue) in  (* Random choice *)
  (* ... pick task at idx and execute ... *)
  t ()
```

---

## Rule 3: E-COMPLETE

**Formal**:

$$\frac{s.\Phi(id) = \text{Pending}(v', \rho', ks) \quad (v' \text{ is a value})}{\langle e, s \rangle \to \langle e, s[id \mapsto \text{Completed}(v')] \ominus id \rangle}$$

$+ \forall k \in ks.\ k(v')$ \hfill (E-COMPLETE)

**Intuition**: Task completes, notify all waiters.

---

## E-COMPLETE: WeChat Analogy

```
[Alice]: "Done! Result is 1000"
         (auto-notify everyone waiting for this result)

[Bob]: (receives notification) "Great, I can continue"
[Carol]: (receives notification) "Great, me too"
```

**Key**: Completion auto-notifies. No polling needed.

---

## E-COMPLETE: OCaml Code

```ocaml
(* future.ml *)
let rec complete id v =
  match Hashtbl.find_opt table id with
  | Some (Pending (_, _, ks)) ->
      Hashtbl.replace table id (Completed (v, []));  (* Phi[id |-> Completed] *)
      List.iter (fun k -> k v) ks                    (* Notify waiters *)
  | _ -> ()
```

---

## Rule 4: E-LIFT-OP

**Formal**:

$$\frac{id \text{ fresh} \quad v_1 = \text{Future}(id_1) \lor v_2 = \text{Future}(id_2)}{\langle v_1 \oplus v_2, s \rangle \to \langle \text{Future}(id), s[id \mapsto \text{Dependent}(deps, \oplus, [])] \rangle}$$

where $deps = [id \mid v_i = \text{Future}(id)]$ \hfill (E-LIFT-OP)

**Intuition**: Operator detects Future operands, creates Dependent Future instead of blocking.

---

## E-LIFT-OP: WeChat Analogy

```
[You]: "When Alice and Bob both finish, sum their results"
       (not waiting, just registering dependency)

[System]: Creates Future #3
          depends_on: [#1, #2]
          compute: (+)
          
[You]: (continue other work, non-blocking)
```

**Key**: Don't await. Build dependency graph instead.

---

## E-LIFT-OP: OCaml Code

```ocaml
(* eval.ml - simplified *)
let binary_op op v1 v2 k = match v1, v2 with
  | Future id1, Future id2 ->
      k (Future (create_dependent [id1;id2] (fun [a;b] -> op a b)))
  | Future id, Int n | Int n, Future id ->
      k (Future (create_dependent [id] (fun [a] -> op a n)))
  | Int a, Int b -> 
      k (Int (op a b))
```

**Key**: Same operator, different behavior based on operand types.

---

## Rule 5: E-RESOLVE

**Formal**:

$$\frac{s.\Phi(id) = \text{Dependent}(deps, f, ks) \quad \forall id' \in deps.\ s.\Phi(id') = \text{Completed}(v_{id'})}{\langle e, s \rangle \to \langle e, s[id \mapsto \text{Completed}(f(values))] \rangle}$$

$+ \forall k \in ks.\ k(f(values))$ \hfill (E-RESOLVE)

**Intuition**: All dependencies complete $\to$ auto-resolve $\to$ cascade notify.

---

## E-RESOLVE: WeChat Analogy

```
[System]: Task #3 depends on [#1, #2]

[Alice completes #1]: -> check #3, #2 not done, wait
[Bob completes #2]:   -> check #3, #1 already done (yes!)
                      -> all deps complete!
                      -> auto-compute: 110 + 120 = 230
                      -> notify all waiters of #3

Cascade: once #3 completes, may trigger #4, #5...
```

**Key**: Avalanche-style auto-resolution.

---

## E-RESOLVE: OCaml Code

```ocaml
(* future.ml *)
let rec check_and_resolve_dependent id =
  match Hashtbl.find_opt table id with
  | Some (Dependent dep) ->
      let all_completed, values = check_dependencies dep.depends_on in
      if all_completed then begin
        let result = dep.compute values in           (* f(values) *)
        Hashtbl.replace table id (Completed (result, dep.depends_on));
        List.iter (fun k -> k result) dep.waiters    (* Cascade! *)
      end
  | _ -> ()
```

---

## Rule Relations: Diamond Example

```ocaml
let x = async (100) in    (* E-ASYNC: #0 Pending *)
let left = x + 10 in      (* E-LIFT-OP: #1 Dependent [#0] *)
let right = x + 20 in     (* E-LIFT-OP: #2 Dependent [#0] *)
left + right              (* E-LIFT-OP: #3 Dependent [#1, #2] *)
```

**Dependency Graph**:

- `#0` Pending (root) $\to$ executes via E-SCHEDULE
- `#1`, `#2` Dependent on `#0` $\to$ resolve via E-RESOLVE  
- `#3` Dependent on `#1`, `#2` $\to$ final result

---

## Execution Trace

| Step | Rule | State Change |
|------|------|-------------|
| 1 | E-ASYNC | $\Phi[\#0 \mapsto \text{Pending}(100)]$, $Q = \{\#0\}$ |
| 2 | E-LIFT-OP | $\Phi[\#1 \mapsto \text{Dependent}([\#0], +10)]$ |
| 3 | E-LIFT-OP | $\Phi[\#2 \mapsto \text{Dependent}([\#0], +20)]$ |
| 4 | E-LIFT-OP | $\Phi[\#3 \mapsto \text{Dependent}([\#1,\#2], +)]$ |
| 5 | E-SCHEDULE | Pick $\#0$ from $Q$ |
| 6 | E-COMPLETE | $\Phi[\#0 \mapsto \text{Completed}(100)]$ |
| 7 | E-RESOLVE | $\Phi[\#1 \mapsto \text{Completed}(110)]$ |
| 8 | E-RESOLVE | $\Phi[\#2 \mapsto \text{Completed}(120)]$ |
| 9 | E-RESOLVE | $\Phi[\#3 \mapsto \text{Completed}(230)]$ |

---

## Comparison with Aeff

| Concept | Aeff | Sub_Async |
|---------|------|-----------|
| Async creation | $\uparrow op\ V.M$ (Signal) | `async e` $\to$ E-ASYNC |
| Parallelism | $P \parallel Q$ (explicit syntax) | $Q$ (implicit queue) |
| Await | `await p as x in M` | E-LIFT-OP (auto) |
| Notification | $\downarrow op\ V.M$ (Interrupt) | E-COMPLETE/RESOLVE |
| Handler | `with H handle M` | Implicit in $\Phi$ |

---

## Aeff: Explicit Parallelism

$$\langle M \rangle \parallel \langle N \rangle \quad \text{(Two processes, visible in syntax)}$$

$$\texttt{handle } M \texttt{ with } H \quad \text{(Explicit handler)}$$

**Formalization**: ~10+ rules for process interaction.

---

## Sub_Async: Implicit Coordination

```ocaml
let x = async e1 in
let y = async e2 in
x + y
```

**No** $\parallel$ syntax. **No** explicit handler.

Parallelism emerges from:

1. Multiple tasks in $Q$ (implicit $\parallel$)
2. E-SCHEDULE chooses non-deterministically
3. E-RESOLVE auto-propagates

**Formalization**: 5 core rules.

---

## Why Simpler?

| Aeff | Sub_Async |
|------|-----------|
| $P \parallel Q$ | Flattened in $Q$ |
| $\downarrow op\ V$ (interrupt) | continuation list `ks` |
| Handler matching | Pattern match on status |
| Process scheduling rules | Single E-SCHEDULE |

**Trade-off**: Less expressive (no dynamic interrupt), but simpler semantics.

---

## Summary

**5 Core Rules**:

1. **E-ASYNC**: Create Future, schedule task
2. **E-SCHEDULE**: Non-deterministic task execution
3. **E-COMPLETE**: Task done, notify waiters
4. **E-LIFT-OP**: Operator creates Dependent Future
5. **E-RESOLVE**: All deps done, auto-resolve

**vs Aeff**: No explicit $\parallel$, no interrupt $\downarrow op$ — simpler semantics

---

## Questions?

**Repository**: `github.com/MuscleOne/sub_async_release`

**Key files**:

- `src/sub_async/eval.ml` — CPS evaluator
- `src/sub_async/future.ml` — Future state machine
- `src/sub_async/scheduler.ml` — Non-deterministic scheduler
