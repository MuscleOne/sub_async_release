---
title: "Sub_Async: Operational Semantics"
subtitle: "Non-deterministic Semantics for Implicit Async Coordination"
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
3. **Abstract Syntax**: Types, expressions, values
4. **Configuration**: $\langle e, s \rangle$ where $s = (\rho, \Phi, Q)$
5. **Future Status**: Exactly 3 states (Pending, Completed, Dependent)
6. **Non-deterministic Semantics**: True concurrency via rule choice
7. **6 Core Rules**:
   - Main rules (M-*): M-ASYNC, M-LIFT-OP, M-AWAIT
   - Scheduler rules (S-*): S-SCHEDULE, S-COMPLETE, S-RESOLVE
8. **Comparison with Aeff**

---

## Why Sub_Async? (Language Motivation)

| Rule | WeChat Analogy | Key Insight |
|------|---------------|-------------|
| **M-ASYNC** | Post job to group | Space decoupling |
| **M-LIFT-OP** | "When ready, compute" | Build graph, not block |
| **M-AWAIT** | "Give me the result" | Extract when ready |
| **S-SCHEDULE** | Whoever grabs it | Non-determinism |
| **S-COMPLETE** | Future done, status change | State transition only |
| **S-RESOLVE** | Dependencies ready | Auto-resolve |

**Core innovation**: Operators detect Futures $\to$ implicit parallelism

---

## WeChat Group Analogy

| Concept | WeChat Group | Sub_Async |
|---------|--------------|-----------|
| Post job | "@everyone: fetch data" | `async e` |
| Who picks up | Whoever grabs it first | `Scheduler.run_one_random()` |
| Job done | Status updated in shared board | `complete id v` |
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

## Abstract Syntax (1/2)

**Expressions**:
$$e ::= x \mid n \mid b \mid e_1 \mathbin{\mathit{op_s}} e_2 \mid e_1 \mathbin{\mathit{op_b}} e_2 \mid \texttt{if } e_1 \texttt{ then } e_2 \texttt{ else } e_3$$
$$\mid \texttt{fun } x \texttt{ is } e \mid e_1\ e_2 \mid \texttt{let } x = e_1 \texttt{ in } e_2 \mid \texttt{async } e$$

**Operators**: $\mathit{op_s} \in \{+, -, *, /, <, =\}$ (strict); \quad $\mathit{op_b} \in \{\land, \lor\}$ (short-circuit)

**Values** (subset of expressions: $v \subseteq e$):
$$v ::= n \mid b \mid \langle x, e, \rho \rangle \mid \texttt{Future}(id)$$

**Environments**:
$$\rho ::= \emptyset \mid \rho[x \mapsto v]$$

---

## Abstract Syntax (2/2)

**Lists**:
$$\textit{ids} ::= [\,] \mid id :: \textit{ids} \qquad \textit{vs} ::= [\,] \mid v :: \textit{vs}$$

**Auxiliary**:
$$\text{range}(\rho) \triangleq \{v \mid \exists x.\ \rho(x) = v\} \qquad id \in ids \triangleq \text{list membership}$$
$$\text{collect}(\Phi, [\,]) = [\,]$$
$$\text{collect}(\Phi, id :: \textit{ids}) = v :: \text{collect}(\Phi, \textit{ids}) \quad \text{if } \Phi(id) = \texttt{Completed}(v)$$

**Types**:
$$\tau ::= \texttt{int} \mid \texttt{bool} \mid \tau_1 \to \tau_2 \mid \texttt{Future}\ \tau$$

**Restricted sub-language** (for Future tasks): $e_f ::= x \mid n \mid b \mid e_f \mathbin{\mathit{op_s}} e_f \mid \texttt{if } e_f \texttt{ then } e_f \texttt{ else } e_f \mid \ldots$ (no `async`)

---

## Configuration

$$\langle e, s \rangle \quad \text{where } s = (\rho, \Phi, Q)$$

| Component | Meaning | Accessor |
|-----------|---------|----------|
| $\rho$ | Environment: $x \mapsto v$ | $s.\rho$ |
| $\Phi$ | Future table: $id \mapsto \sigma$ | $s.\Phi$ |
| $Q$ | Task set (nondet choice, no fairness/probability) | $s.Q$ |

**Formal definitions**:
$$\text{dom}(\Phi) \triangleq \{id \mid \exists \sigma.\ \Phi(id) = \sigma\}$$
$$s[id \mapsto \sigma] \triangleq (\rho, \Phi[id \mapsto \sigma], Q)$$
$$s \oplus id \triangleq (\rho, \Phi, Q \cup \{id\}) \qquad s \ominus id \triangleq (\rho, \Phi, Q \setminus \{id\})$$
$$\text{fresh}(\Phi) \triangleq \text{choose } id \text{ such that } id \notin \text{dom}(\Phi)$$

<!-- These are **shorthand** for state changes. Instead of writing $(ρ, Φ', Q')$ every time, we write operations on $s$.

**Example**: $s[id \mapsto \text{Pending}(...)] \oplus id$ means "update Future table AND add to queue" -->

---

## Future Status (State Machine)

**Exactly 3 states** (exhaustive):

$$\sigma ::= \texttt{Pending}(e, \rho) \mid \texttt{Completed}(v) \mid \texttt{Dependent}(\textit{ids}, f)$$

where $f : v^{|ids|} \to v$ is a combine function (arity = dependency list length).

| Status | Meaning | In $Q$? |
|--------|---------|---------|
| $\texttt{Pending}(e, \rho)$ | Computation $e$ with environment $\rho$ | Yes |
| $\texttt{Completed}(v)$ | Done, holds value $v$ | No |
| $\texttt{Dependent}(\textit{ids}, f)$ | Waiting for all $id \in \textit{ids}$, then apply $f$ | No |

---

## Future Status Transitions

**State diagram**:

- $\texttt{Pending} \xrightarrow{\text{S-SCHEDULE + S-COMPLETE}} \texttt{Completed}$
- $\texttt{Dependent} \xrightarrow{\text{S-RESOLVE}} \texttt{Completed}$

**Creation**:

- `async e` $\to$ creates $\texttt{Pending}(e, \rho)$
- `Future(id) op_s v` $\to$ creates $\texttt{Dependent}([id], f)$

**Extraction**: M-AWAIT pulls value from $\texttt{Completed}$

---

## Well-Formedness Invariant

**Definition**: A state $s = (\rho, \Phi, Q)$ is **well-formed**, written $\text{WF}(s)$, iff:

1. $Q \subseteq \text{dom}(\Phi)$ \quad (no dangling task ids)
2. $id \in Q \Leftrightarrow \Phi(id) = \texttt{Pending}(\_, \_)$ \quad (Q tracks exactly Pending)
3. $\Phi(id) = \texttt{Dependent}(\textit{ids}, f) \Rightarrow \forall id' \in \textit{ids}.\ id' \in \text{dom}(\Phi)$ \quad (deps exist)
4. $\texttt{Future}(id) \in \text{range}(\rho) \Rightarrow id \in \text{dom}(\Phi)$ \quad (no wild Future)

**Lemma (WF Preservation)**: If $\text{WF}(s)$ and $\langle e, s \rangle \to \langle e', s' \rangle$, then $\text{WF}(s')$.

---

## Evaluation Contexts (CBV, Left-to-Right)

**General contexts** (where evaluation can proceed):
$$E ::= [\,] \mid E\ e \mid v\ E \mid E \mathbin{\mathit{op_s}} e \mid v \mathbin{\mathit{op_s}} E \mid \texttt{let } x = E \texttt{ in } e \mid \texttt{if } E \texttt{ then } e_2 \texttt{ else } e_3$$

**Demand contexts** (positions requiring **concrete** value — triggers M-AWAIT):
$$E_d ::= [\,]\ e \mid v\ [\,] \mid \texttt{if } [\,] \texttt{ then } e_2 \texttt{ else } e_3$$

**Note**: $\mathit{op_s}$ positions **not** in $E_d$ — Futures trigger M-LIFT-OP instead of await.

**Context rule**:
$$\frac{\langle e, s \rangle \to \langle e', s' \rangle}{\langle E[e], s \rangle \to \langle E[e'], s' \rangle}$$ \hfill (E-CONTEXT)

---

## Non-deterministic Semantics

**Key insight**: All rules share one reduction relation $\to$

- Multiple rules may be applicable at the same time
- **Non-deterministic choice** which rule fires (no probability/fairness modeled)

**Rule naming convention**:

- **M-*** (Main): expression $e$ steps forward
- **S-*** (Scheduler): $e$ unchanged, only state $s$ changes

**No priority** $\Rightarrow$ models all possible interleavings

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

## Main Rules: M-ASYNC

**Formal**:

$$\frac{id = \text{fresh}(s.\Phi) \quad e \in e_f \quad \texttt{Future}(\_) \notin \text{range}(s.\rho)}{\langle \texttt{async } e, s \rangle \to \langle \texttt{Future}(id), (s \oplus id)[id \mapsto \texttt{Pending}(e, s.\rho)] \rangle}$$
\hfill (M-ASYNC)

**Intuition**: `async e` immediately returns `Future(id)`, adds $id$ to task set $Q$.

**Restrictions** (design choice for simpler semantics):

- $e \in e_f$: task body has no `async` syntax
- $\texttt{Future}(\_) \notin \text{range}(s.\rho)$: captured env is **Future-free** (task runs independently)

---

## M-ASYNC: WeChat Analogy

```
[You]: "@everyone: compute expensive_task"
       (post to group, don't wait for reply)
       
[System]: Returns Future #0 immediately
          Future #0 added to queue Q
```

**Key**: Fire and forget. Don't specify who. Don't wait.

---

## M-ASYNC: OCaml Code

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

## Scheduler Rules: S-SCHEDULE

**Formal**:

$$\frac{id \in s.Q \quad s.\Phi(id) = \texttt{Pending}(e', \rho') \quad (e', \rho') \to_f (e'', \rho'')}{\langle e, s \rangle \to \langle e, s[id \mapsto \texttt{Pending}(e'', \rho'')] \rangle}$$

\hfill (S-SCHEDULE)

where $\to_f$ is the standard small-step relation **restricted to $e_f$** (no async/Future ops).

**Intuition**: Non-deterministically pick a pending Future from $Q$, execute one step, update $\Phi$.

**Note**: Since $e' \in e_f$, the step $\to_f$ cannot create new Futures or modify $(\Phi, Q)$.

---

## S-SCHEDULE: WeChat Analogy

```
[Three Futures waiting in Q]

Future #0: compute "fetch user info"
Future #1: compute "validate permissions"  
Future #2: compute "check quota"

[Scheduler]: (randomly picks Future #1) Execute its computation
```

**Key**: Whoever grabs it, does it (non-deterministic scheduling).

---

## S-SCHEDULE: OCaml Code

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

## Scheduler Rules: S-COMPLETE

**Formal**:

$$\frac{id \in s.Q \quad s.\Phi(id) = \texttt{Pending}(v, \rho)}{\langle e, s \rangle \to \langle e, (s \ominus id)[id \mapsto \texttt{Completed}(v)] \rangle}$$

\hfill (S-COMPLETE)

**Intuition**: Future $id$ finished (expression reduced to value). Remove from $Q$, mark Completed.

---

## S-COMPLETE: WeChat Analogy

```
[Future #1's computation finishes]
[Scheduler]: Updates Phi: Future #1 status -> Completed(1000)
             (just state change, doesn't notify anyone)

[Later, when main program needs the result...]
[Main]: "@Phi: is #1 done?" -> "Yes, here's 1000"
```

**Key**: Completion is just state change. **Consumers poll when they need it**.

---

## S-COMPLETE: OCaml Code

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

## Scheduler Rules: S-RESOLVE

**Formal**:

$$\frac{s.\Phi(id) = \texttt{Dependent}(\textit{ids}, f) \quad \forall id' \in \textit{ids}.\, \exists v.\, s.\Phi(id') = \texttt{Completed}(v)}{\langle e, s \rangle \to \langle e, s[id \mapsto \texttt{Completed}(f(\text{collect}(s.\Phi, \textit{ids})))] \rangle}$$

\hfill (S-RESOLVE)

**Intuition**: All dependencies completed $\Rightarrow$ resolve Dependent Future.

---

## S-RESOLVE: WeChat Analogy

```
[Future #3 depends on #1 and #2]

[System checks]: Is #1 done? Yes (100)
                 Is #2 done? Yes (200)
                 
[System]: All deps ready! Compute: 100 + 200 = 300
          Future #3 status -> Completed(300)
```

**Key**: Automatic resolution when dependencies complete.

---

## Main Rules: M-LIFT-OP

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{Future}(id_1) \mathbin{\mathit{op_s}} \texttt{Future}(id_2), s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_1, id_2], f_{op_s})] \rangle}$$
\hfill (M-LIFT-OP-FF)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{Future}(id_1) \mathbin{\mathit{op_s}} n, s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_1], f_{op_s,n})] \rangle}$$
\hfill (M-LIFT-OP-FV)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle n \mathbin{\mathit{op_s}} \texttt{Future}(id_2), s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_2], f_{n,op_s})] \rangle}$$
\hfill (M-LIFT-OP-VF)

where $f_{op_s}([n_1, n_2]) = n_1 \mathbin{op_s} n_2$, $f_{op_s,n}([n_1]) = n_1 \mathbin{op_s} n$, $f_{n,op_s}([n_2]) = n \mathbin{op_s} n_2$.

**Combine functions**: $f : v^{|ids|} \to v$ (arity matches dependency list length).

---

## M-LIFT-OP: WeChat Analogy

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

## M-LIFT-OP: OCaml Code

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

## M-LIFT-OP: Limitations

**Which operators can be lifted?**

| Operators | Liftable? | Reason |
|-----------|-----------|--------|
| `+`, `-`, `*`, `/`, `<`, `=` | Yes | Strict evaluation |
| `&&`, `||` | **No** | Short-circuit: need left value first |

**Problem**: `Future(id) && e` — can't decide whether to evaluate `e` until `id` completes.

**Current**: Boolean ops with Futures block-await both sides (lose short-circuit).

---

## Main Rules: M-AWAIT

**Note**: `await` is not explicit syntax — triggered implicitly at **demand contexts** $E_d$.

**Rule for demand contexts**:
$$\frac{s.\Phi(id) = \texttt{Completed}(v)}{\langle E_d[\texttt{Future}(id)], s \rangle \to \langle E_d[v], s \rangle}$$
\hfill (M-AWAIT)

**Rule for top-level result** (program needs final value):
$$\frac{s.\Phi(id) = \texttt{Completed}(v)}{\langle \texttt{Future}(id), s \rangle \to \langle v, s \rangle}$$
\hfill (M-AWAIT-FINAL)

**Instances of $E_d$**: if-condition, function operator/argument positions.

**Not in $E_d$**: $\mathit{op_s}$ positions (Futures trigger M-LIFT-OP instead).

**If not completed?** The term is **stuck** — but S-SCHEDULE can still fire!

---

## Progress Property

**Theorem (Progress)**: If $\text{WF}(s)$, then either:

1. $e$ is a non-Future value (done!), or
2. $e = \texttt{Future}(id)$ with $\Phi(id) = \texttt{Completed}(v)$ (can M-AWAIT-FINAL), or
3. $\exists e', s'.\ \langle e, s \rangle \to \langle e', s' \rangle$ (can step)

**Stuck condition**: $e = E_d[\texttt{Future}(id)]$ or $e = \texttt{Future}(id)$ where $\Phi(id) \neq \texttt{Completed}$ **and** $Q = \emptyset$.

*Note: Typing rules omitted (standard STLC + Future); Progress holds for well-typed terms.*

**Key insight**: When main is stuck on a Future, S-SCHEDULE can still fire (if $Q \neq \emptyset$)!

```
Possible trace:
  <if Future(#0) then..., s>   -- main stuck, needs bool, Q = {#0}
  <if Future(#0) then..., s>   ->  <..., s'>   (S-SCHEDULE fires)
  <if Future(#0) then..., s'>  ->  <if true then..., s'>  (M-AWAIT)
```

**True concurrency**: Main stuck $\neq$ system stuck.

---

## M-AWAIT: WeChat Analogy

```
[Main program evaluating: if (x > 0) then ... ]
[x is Future(#1)]

[Main]: "I need the actual value of x now"
        "@ FutureTable: give me #1's result"

[If Completed]: "Here's 100" -> continue with if(100 > 0)
[If Pending]:   Main is stuck -- but scheduler keeps working!
```

**Key**: Main **waits** for result. But scheduler rules can still fire concurrently.

---

## M-AWAIT: OCaml Code

```ocaml
(* eval.ml - implicit await when concrete value needed *)
let rec value_to_int v k = match v with
  | Int n -> k n
  | Future id -> Future.await id (fun v' -> value_to_int v' k)
  | _ -> runtime_error "integer expected"

(* Example: if-then-else needs bool, triggers implicit await *)
| If (e1, e2, e3) ->
    eval_cps env e1 (fun v1 ->
      value_to_bool v1 (fun b -> ...))  (* await if v1 is Future *)
```

**Key**: `await` triggered implicitly by evaluation contexts needing concrete values.

---

## Rule Relations: Diamond Example

```ocaml
let x = async (100) in    (* M-ASYNC: #0 Pending *)
let left = x + 10 in      (* M-LIFT-OP: #1 Dependent [#0] *)
let right = x + 20 in     (* M-LIFT-OP: #2 Dependent [#0] *)
left + right              (* M-LIFT-OP: #3 Dependent [#1, #2] *)
(* When result is needed: implicit await on #3 *)
```

**Dependency Graph**:

- `#0` Pending (root) $\to$ executes via S-SCHEDULE
- `#1`, `#2` Dependent on `#0`  
- `#3` Dependent on `#1`, `#2`
- **When main needs result**: M-AWAIT triggers resolution chain

---

## Execution Trace

| Step | Rule | State Change |
|------|------|-------------|
| 1 | M-ASYNC | $\Phi[\#0 \mapsto \texttt{Pending}(100, \rho)]$, $Q = \{\#0\}$ |
| 2 | M-LIFT-OP | $\Phi[\#1 \mapsto \texttt{Dependent}([\#0], \lambda v.\, v+10)]$ |
| 3 | M-LIFT-OP | $\Phi[\#2 \mapsto \texttt{Dependent}([\#0], \lambda v.\, v+20)]$ |
| 4 | M-LIFT-OP | $\Phi[\#3 \mapsto \texttt{Dependent}([\#1,\#2], \lambda (a,b).\, a+b)]$ |
| 5 | S-SCHEDULE | Pick $\#0$ from $Q$, execute |
| 6 | S-COMPLETE | $\Phi[\#0 \mapsto \texttt{Completed}(100)]$ |
| 7 | S-RESOLVE | $\Phi[\#1 \mapsto \texttt{Completed}(110)]$ |
| 8 | S-RESOLVE | $\Phi[\#2 \mapsto \texttt{Completed}(120)]$ |
| 9 | S-RESOLVE | $\Phi[\#3 \mapsto \texttt{Completed}(230)]$ |
| 10 | M-AWAIT | Extract $230$ from $\#3$ |

---

## Comparison with Aeff

| Concept | Aeff | Sub_Async |
|---------|------|-----------|
| Async creation | $\uparrow op\ V.M$ (Signal) | `async e` $\to$ M-ASYNC |
| Parallelism | $P \parallel Q$ (explicit syntax) | $Q$ (implicit queue) |
| Await | `await p as x in M` (explicit) | M-AWAIT (implicit, when needed) |
| Completion | $\downarrow op\ V.M$ (Interrupt) | S-COMPLETE (state change) |
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
2. S-SCHEDULE chooses non-deterministically
3. M-AWAIT pulls results, triggering resolution chain

**Formalization**: 6 core rules.

---

## Why Simpler?

| Aeff | Sub_Async |
|------|-----------|
| $P \parallel Q$ | Flattened in $Q$ |
| $\downarrow op\ V$ (interrupt) | Polling via M-AWAIT |
| Handler matching | Pattern match on status |
| Process scheduling rules | Single S-SCHEDULE |

**Trade-off**: Less expressive (no dynamic interrupt), but simpler semantics.

---

## Summary

**Non-deterministic Semantics** with **7 Core Rules + E-CONTEXT**:

**Main rules** (M-*): expression $e$ steps

- **M-ASYNC**: Create Future (restricted: Future-free task + env), add to $Q$
- **M-LIFT-OP**: Operator on Future creates Dependent Future (no blocking)
- **M-AWAIT / M-AWAIT-FINAL**: Extract value at demand contexts or top-level

**Scheduler rules** (S-*): $e$ unchanged, only state $s$ changes

- **S-SCHEDULE**: Non-deterministically execute a Future (no global state change)
- **S-COMPLETE**: Pending $\to$ Completed when done
- **S-RESOLVE**: Dependent $\to$ Completed when all dependencies ready

**Key formal properties**: WF(s) preserved; Progress holds under WF.

---

## Questions?

**Repository**: `github.com/MuscleOne/sub_async_release`

**Key files**:

- `src/sub_async/eval.ml` — CPS evaluator
- `src/sub_async/future.ml` — Future state machine
- `src/sub_async/scheduler.ml` — Non-deterministic scheduler
