---
title: "Sub_Async: Operational Semantics"
subtitle: "Interleaving Semantics for Implicit Async Coordination"
author: "Chen Tianhao"
date: "January 2026"
classoption: "aspectratio=169"
theme: "metropolis"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{amssymb}
---

<!-- cd /mnt/c/Users/p2215292/Desktop/comptuting/Formal\ Semantics\ of\ Programming\ Languages/sub_async_release/docs/slides && pandoc SLIDES_CORE_RULES.md -t beamer --pdf-engine=xelatex -o SLIDES_CORE_RULES.pdf -->

## Outline

1. **Language Motivation**: Space/Time Decoupling (WeChat Analogy)
2. **Formalization Motivation**: Externalize runtime state
3. **Configuration**: $\langle e, s \rangle$ where $s = (\rho, \Phi, Q)$
4. **Interleaving Semantics**: True concurrency via non-determinism
5. **6 Core Rules**: E-ASYNC, E-SCHEDULE, E-COMPLETE, E-RESOLVE, E-LIFT-OP, E-AWAIT
6. **Comparison with Aeff**

---

## Why Sub_Async? (Language Motivation)

| Rule | WeChat Analogy | Key Insight |
|------|---------------|-------------|
| **E-ASYNC** | Post job to group | Space decoupling |
| **E-SCHEDULE** | Whoever grabs it | Non-determinism |
| **E-COMPLETE** | Future done, status change | State transition only |
| **E-LIFT-OP** | "When ready, compute" | Build graph, not block |
| **E-AWAIT** | "Is it done yet?" | Main pulls when needed |

**Core innovation**: Operators detect Futures $\to$ implicit parallelism

---

## WeChat Group Analogy

| Concept | WeChat Group | Sub_Async |
|---------|--------------|-----------|
| Post job | "@everyone: fetch data" | `async e` |
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
| $Q$ | Pending Future ids | `Scheduler.queue` |

**Update notation**:

- $s[id \mapsto v]$ — update $\Phi(id) = v$ (modify Future table)
- $s \oplus id$ — $Q := Q \cup \{id\}$ (add Future to queue)
- $s \ominus id$ — $Q := Q \backslash \{id\}$ (remove Future from queue)

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

- $\text{Pending} \xrightarrow{\text{E-SCHEDULE + E-COMPLETE}} \text{Completed}$
- $\text{Dependent} \xrightarrow{\text{E-RESOLVE}} \text{Completed}$
- `async e` creates Pending, E-AWAIT pulls value

---

## Interleaving Semantics (True Concurrency)

**Key insight**: Non-deterministic scheduling = all possible interleavings

$$\frac{\langle e, s \rangle \to_{\text{main}} \langle e', s' \rangle}{\langle e, s \rangle \to \langle e', s' \rangle} \text{ (STEP-MAIN)}$$

$$\frac{s.Q \neq \emptyset \quad \langle e, s \rangle \to_{\text{sched}} \langle e, s' \rangle}{\langle e, s \rangle \to \langle e, s' \rangle} \text{ (STEP-SCHED)}$$

**No priority** between rules $\Rightarrow$ true concurrency!

---

## WeChat Analogy: True Concurrency

```
+------------------------------------------------+
|  Everyone online simultaneously                |
|                                                |
|  [You]    [MemberA]  [MemberB]  [MemberC]      |
|    |         |          |          |           |
|    +--post-->|          |          |           |
|    |         +--------->|          |  (any     |
|    |<--------+          |<---------+   order!) |
|                                                |
|  Who acts next? -> Non-deterministic!          |
+------------------------------------------------+
```

**Not** "post and wait" — **all act concurrently**

---

## Rule 1: E-ASYNC

**Formal**:

$$\frac{id \text{ fresh}}{\langle \texttt{async } e, s \rangle \to \langle \text{Future}(id), s[id \mapsto \text{Pending}(e, s.\rho, [])] \oplus id \rangle} \text{ (E-ASYNC)}$$

**Intuition**: `async e` immediately returns `Future(id)`, adds $id$ to scheduler queue $Q$.

---

## E-ASYNC: WeChat Analogy

```
[You]: "@everyone: compute expensive_task"
       (post to group, don't wait for reply)
       
[System]: Returns Future #0 immediately
          Future #0 added to queue Q
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

$$\frac{id \in s.Q \quad s.\Phi(id) = \text{Pending}(e', \rho', ks)}{\langle e, s \rangle \to_{\text{sched}} \langle e, s' \rangle} \text{ (E-SCHEDULE)}$$

where $s'$ reflects one step of evaluating $e'$ in environment $\rho'$.

**Intuition**: **At any time**, non-deterministically pick a pending Future from $Q$ to execute. Main expression $e$ unchanged.

---

## E-SCHEDULE: WeChat Analogy

```
[Three Futures waiting in Q]

Future #0: compute "fetch user info"
Future #1: compute "validate permissions"  
Future #2: compute "check quota"

[Scheduler]: (randomly picks Future #1) Execute its computation
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
  (* ... pick Future at idx and execute its computation ... *)
  t ()
```

---

## Rule 3: E-COMPLETE

**Formal**:

$$\frac{s.\Phi(id) = \text{Pending}(v', \rho', ks) \quad (v' \text{ is a value})}{\langle e, s \rangle \to_{\text{sched}} \langle e, s[id \mapsto \text{Completed}(v')] \ominus id \rangle}$$

(E-COMPLETE)

**Intuition**: Future $id$'s computation reached value $v'$. Status changes Pending $\to$ Completed.

---

## E-COMPLETE: WeChat Analogy

```
[Future #1's computation finishes]
[Scheduler]: Updates Phi: Future #1 status -> Completed(1000)
             (just state change, doesn't notify anyone)

[Later, when main program needs the result...]
[Main]: "@Phi: is #1 done?" -> "Yes, here's 1000"
```

**Key**: Completion is just state change. **Consumers poll when they need it**.

---

## E-COMPLETE: OCaml Code

```ocaml
(* future.ml - Future completion *)
let complete id v =
  Hashtbl.replace table id (Completed (v, deps))  (* Just state change *)
  (* No active notification! Waiters check via await *)

(* eval.ml - main program polls when needed *)
let rec value_to_int v k = match v with
  | Int n -> k n
  | Future id -> Future.await id (fun v' -> value_to_int v' k)
      (* Main program ACTIVELY queries: "is it done?" *)
```

---

## Rule 4: E-RESOLVE (New!)

**Formal**:

$$\frac{s.\Phi(id) = \text{Dependent}(deps, f, ks) \quad \forall d \in deps.\ s.\Phi(d) = \text{Completed}(v_d)}{\langle e, s \rangle \to_{\text{sched}} \langle e, s[id \mapsto \text{Completed}(f([v_d]))] \rangle}$$

(E-RESOLVE)

**Intuition**: All dependencies completed $\Rightarrow$ resolve Dependent Future.

---

## E-RESOLVE: WeChat Analogy

```
[Future #3 depends on #1 and #2]

[System checks]: Is #1 done? Yes (100)
                 Is #2 done? Yes (200)
                 
[System]: All deps ready! Compute: 100 + 200 = 300
          Future #3 status -> Completed(300)
```

**Key**: Automatic resolution when dependencies complete.

---

## Rule 5: E-LIFT-OP

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

## Rule 6: E-AWAIT (Main Program Queries)

**Formal**:

$$\frac{s.\Phi(id) = \text{Completed}(v)}{\langle \texttt{await}(id), s \rangle \to_{\text{main}} \langle v, s \rangle}$$ (E-AWAIT-READY)

$$\frac{s.\Phi(id) \neq \text{Completed}}{\langle \texttt{await}(id), s \rangle \to_{\text{main}} \langle \texttt{await}(id), s \rangle}$$ (E-AWAIT-SPIN)

**Intuition**: Main checks status. If ready, get value. If not, **spin** — but scheduler can interleave!

---

## E-AWAIT-SPIN: Why It's OK (Progress)

**Old concern**: E-AWAIT-SPIN looks like stuttering (no progress).

**Resolution**: In interleaving semantics, **STEP-SCHED can fire concurrently**!

```
Possible trace:
  <await(#0), s>  ->_main  <await(#0), s>   (spin)
  <await(#0), s>  ->_sched <await(#0), s'>  (#0 executes)
  <await(#0), s'> ->_main  <100, s'>        (ready!)
```

**Progress**: If $Q \neq \emptyset$, system always has a step (via STEP-SCHED).

---

## E-AWAIT: WeChat Analogy

```
[Main program evaluating: if (x > 0) then ... ]

[Main]: "I need the actual value of x now"
        "@ FutureTable: is #1 done?"

[If Completed]: "Yes, here's 100" -> continue with if(100 > 0)
[If Pending]:   "Not yet" -> (but workers still computing!)
```

**Key**: Main **checks** but doesn't block the world. Workers continue concurrently.

---

## E-AWAIT: OCaml Code

```ocaml
(* future.ml *)
let await id k =
  match Hashtbl.find_opt table id with
  | Some (Completed (v, _)) -> k v    (* Ready! Return value *)
  | Some (Pending (_, _, ks)) ->
      (* Not ready: register k, keep scheduling *)
      Hashtbl.replace table id (Pending (e, env, k::ks))
  | Some (Dependent dep) ->
      (* Check if deps all done, resolve if so *)
      check_and_resolve_dependent id; ...
```

**Key**: `await` is called by main program when it **needs** the value.

---

## Rule Relations: Diamond Example

```ocaml
let x = async (100) in    (* E-ASYNC: #0 Pending *)
let left = x + 10 in      (* E-LIFT-OP: #1 Dependent [#0] *)
let right = x + 20 in     (* E-LIFT-OP: #2 Dependent [#0] *)
left + right              (* E-LIFT-OP: #3 Dependent [#1, #2] *)
(* When result is needed: main program AWAITS #3 *)
```

**Dependency Graph**:

- `#0` Pending (root) $\to$ executes via E-SCHEDULE
- `#1`, `#2` Dependent on `#0`  
- `#3` Dependent on `#1`, `#2`
- **When main needs result**: E-AWAIT triggers resolution chain

---

## Execution Trace

| Step | Rule | State Change |
|------|------|-------------|
| 1 | E-ASYNC | $\Phi[\#0 \mapsto \text{Pending}(100)]$, $Q = \{\#0\}$ |
| 2 | E-LIFT-OP | $\Phi[\#1 \mapsto \text{Dependent}([\#0], +10)]$ |
| 3 | E-LIFT-OP | $\Phi[\#2 \mapsto \text{Dependent}([\#0], +20)]$ |
| 4 | E-LIFT-OP | $\Phi[\#3 \mapsto \text{Dependent}([\#1,\#2], +)]$ |
| 5 | E-SCHEDULE | Pick $\#0$ from $Q$, execute |
| 6 | E-COMPLETE | $\Phi[\#0 \mapsto \text{Completed}(100)]$ |
| 7 | **E-RESOLVE** | $\#1$ deps ready $\to$ $\Phi[\#1 \mapsto \text{Completed}(110)]$ |
| 8 | **E-RESOLVE** | $\#2$ deps ready $\to$ $\Phi[\#2 \mapsto \text{Completed}(120)]$ |
| 9 | **E-RESOLVE** | $\#3$ deps ready $\to$ $\Phi[\#3 \mapsto \text{Completed}(230)]$ |
| 10 | E-AWAIT | Main queries $\#3$ $\to$ returns 230 |

---

## Comparison with Aeff

| Concept | Aeff | Sub_Async |
|---------|------|-----------|
| Async creation | $\uparrow op\ V.M$ (Signal) | `async e` $\to$ E-ASYNC |
| Parallelism | $P \parallel Q$ (explicit syntax) | $Q$ (implicit queue) |
| Await | `await p as x in M` (explicit) | E-AWAIT (implicit, when needed) |
| Completion | $\downarrow op\ V.M$ (Interrupt) | E-COMPLETE (state change) |
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

1. Multiple Futures in $Q$ (implicit $\parallel$)
2. E-SCHEDULE chooses non-deterministically
3. E-AWAIT pulls results, triggering resolution chain

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

**Interleaving Semantics** with **6 Core Rules**:

1. **E-ASYNC**: Create Future, add to $Q$
2. **E-SCHEDULE**: Non-deterministically execute a Future (any time!)
3. **E-COMPLETE**: Pending $\to$ Completed when done
4. **E-RESOLVE**: Dependent $\to$ Completed when deps ready
5. **E-LIFT-OP**: Operator creates Dependent Future
6. **E-AWAIT**: Main checks; spins if not ready (but scheduler interleaves)

**Progress**: If $Q \neq \emptyset \lor e$ can step, system progresses.

**vs Aeff**: No explicit $\parallel$, no interrupt — concurrency via interleaving

---

## Questions?

**Repository**: `github.com/MuscleOne/sub_async_release`

**Key files**:

- `src/sub_async/eval.ml` — CPS evaluator
- `src/sub_async/future.ml` — Future state machine
- `src/sub_async/scheduler.ml` — Non-deterministic scheduler
