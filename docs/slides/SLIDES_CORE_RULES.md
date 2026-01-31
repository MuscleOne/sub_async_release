---
title: "Sub_Async: Operational Semantics"
subtitle: "Non-deterministic Semantics for Implicit Async Parallelism"
author: "Chen Tianhao"
date: "January 2026"
classoption: "aspectratio=169"
theme: "metropolis"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{amssymb}
---

<!-- cd "/mnt/c/Users/p2215292/Desktop/comptuting/Formal Semantics of Programming Languages/sub_async_release/docs/slides" && pandoc SLIDES_CORE_RULES.md -t beamer --pdf-engine=xelatex -o pdf/SLIDES_CORE_RULES.pdf -->

## Outline

1. **Motivation**: Space/time decoupling, externalize runtime state
2. **Abstract Syntax**: Expressions, values, Future status
3. **Configuration**: $\langle e, s \rangle$ where $s = (\rho, \Phi, Q)$
4. **Core Rules**:
   - Main: M-ASYNC, M-LIFT-OP (×3), M-AWAIT (×4)
   - Scheduler: S-SCHEDULE, S-COMPLETE, S-RESOLVE
5. **Progress Theorem**: Under $\text{WF}(s)$, never globally stuck

---

## Why Sub_Async? (Language Motivation)

**Core idea**: Space/time decoupling through implicit async parallelism.

| Concept | Analogy | Sub_Async Mechanism |
|---------|---------|---------------------|
| **Space decoupling** | Post to group, anyone handles | `async e` → any scheduler picks |
| **Time decoupling** | Return now, result later | `async e` → returns `Future(id)` |
| **Implicit parallelism** | "When both ready, compute" | `Future op Future` → dependency graph |
| **Non-blocking ops** | Don't wait, just register | M-LIFT-OP builds graph |
| **Pull semantics** | Ask when you need it | M-AWAIT extracts value |

**Innovation**: Operators auto-detect Futures → parallelism without explicit `||` (parallel) syntax.

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

## Abstract Syntax

**Expressions**:
$$e ::= x \mid n \mid b \mid e_1 \mathbin{\mathit{op}} e_2 \mid \texttt{if } e_1 \texttt{ then } e_2 \texttt{ else } e_3$$
$$\mid \texttt{fun } x \texttt{ is } e \mid e_1\ e_2 \mid \texttt{let } x = e_1 \texttt{ in } e_2 \mid \texttt{async } e$$

where $\mathit{op} \in \{+, -, *, /, <, =\}$ (strict operators only).

**Values**:
$$v ::= n \mid b \mid \langle x, e, \rho \rangle \mid \texttt{Future}(id)$$

**Future Status** (runtime states):
$$\sigma ::= \texttt{Pending}(e, \rho) \mid \texttt{Completed}(v) \mid \texttt{Dependent}(\overline{id}, f)$$

*Note: $\overline{id}$ denotes a list $[id_1, \ldots, id_n]$; $f : [\text{Val}] \to \text{Val}$ is a combine function.*

---

## Auxiliary Definitions

**List notation** (standard):
$$[] \quad \text{(empty list)} \qquad x :: xs \quad \text{(cons)} \qquad xs \mathbin{+\!\!+} ys \quad \text{(concatenation)}$$
$$|xs| \quad \text{(length)} \qquad [x_1, \ldots, x_n] \triangleq x_1 :: \cdots :: x_n :: []$$

**Semantic domains**:
$$\rho \in \text{Env} = \text{Var} \rightharpoonup \text{Val}$$
$$\Phi \in \text{FutureTable} = [(\text{Id} \times \text{Status})] \quad \text{(association list)}$$
$$Q \in \text{TaskQueue} = [\text{Id}]$$

**Operations**:
$$\text{fresh}(\Phi) \triangleq |\Phi| \quad \text{(sequential allocation: 0, 1, 2, ...)}$$
$$\text{lookup}([], id) \triangleq \bot \qquad \text{lookup}((id', \sigma) :: \Phi, id) \triangleq \begin{cases} \sigma & \text{if } id = id' \\ \text{lookup}(\Phi, id) & \text{otherwise} \end{cases}$$
$$\text{collect}(\Phi, [id_1, \ldots, id_n]) \triangleq [v_1, \ldots, v_n] \text{ where } \text{lookup}(\Phi, id_i) = \texttt{Completed}(v_i)$$

*$\text{collect}$ is partial: defined only when all $id_i$ are Completed.*

---

## Configuration

$$\langle e, s \rangle \quad \text{where } s = (\rho, \Phi, Q)$$

| Component | Meaning |
|-----------|---------|
| $e$ | Current expression |
| $\rho$ | Environment (binds variables to values) |
| $\Phi$ | Future table (maps ids to status) |
| $Q$ | Pending task set |

**Shorthand for state updates** (prepend semantics):
$$s[id \mapsto \sigma] \triangleq (\rho, (id, \sigma) :: \Phi, Q) \quad \text{(shadows previous entries)}$$
$$s \oplus id \triangleq (\rho, \Phi, id :: Q) \qquad s \ominus id \triangleq (\rho, \Phi, \text{filter}(\neq id, Q))$$

*We write $s.\Phi$, $s.\rho$, $s.Q$ for projections. $\text{lookup}$ returns first match (newest).*

---

## Future Status (State Machine)

| Status | Created by | Transitions to |
|--------|-----------|----------------|
| $\texttt{Pending}(e, \rho)$ | M-ASYNC | $\texttt{Completed}$ via S-COMPLETE |
| $\texttt{Dependent}(\overline{id}, f)$ | M-LIFT-OP | $\texttt{Completed}$ via S-RESOLVE |
| $\texttt{Completed}(v)$ | S-COMPLETE, S-RESOLVE | (terminal) |

**State diagram** (exhaustive for this core calculus):
$$\texttt{Pending} \xrightarrow{\text{S-COMPLETE}} \texttt{Completed} \xleftarrow{\text{S-RESOLVE}} \texttt{Dependent}$$

---

## Well-Formedness Invariant

**Definition**: $\text{WF}(s)$ for state $s = (\rho, \Phi, Q)$ iff:

1. $id \in Q \Leftrightarrow \exists e, \rho'.\, \text{lookup}(\Phi, id) = \texttt{Pending}(e,\rho')$ \quad (Q tracks pending)
2. $\text{lookup}(\Phi, id) = \texttt{Dependent}(\overline{id'}, f) \Rightarrow \forall id' \in \overline{id'}.\ id' \in \text{dom}(\Phi)$ \quad (no dangling)
3. $\text{lookup}(\Phi, id) = \texttt{Dependent}(\overline{id'}, f) \Rightarrow id \notin \overline{id'} \land \text{NoDup}(\overline{id'})$ \quad (no self-cycle)
4. $\rho(x) = \texttt{Future}(id) \Rightarrow id \in \text{dom}(\Phi)$ \quad (no dangling Future refs)

**Lemma (WF Preservation)**: $\text{WF}(s) \land \langle e, s \rangle \to \langle e', s' \rangle \Rightarrow \text{WF}(s')$

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

## Main Rules: M-ASYNC

**Formal**:

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{async } e, s \rangle \to \langle \texttt{Future}(id), (s \oplus id)[id \mapsto \texttt{Pending}(e, s.\rho)] \rangle}$$
\hfill (M-ASYNC)

**Intuition**: `async e` immediately returns `Future(id)`, adds $id$ to $Q$.

*The captured environment $s.\rho$ may contain Futures — enables patterns like:*
```
let x = async 1 in async (x + 1)   (* x is Future, captured in env *)
```

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

$$\frac{id \in s.Q \quad \text{lookup}(s.\Phi, id) = \texttt{Pending}(e', \rho') \quad \langle e', (\rho', s.\Phi, []) \rangle \to \langle e'', s'' \rangle}{\langle e, s \rangle \to \langle e, (s.\rho,\ s''.\Phi,\ s.Q \mathbin{+\!\!+} s''.Q)[id \mapsto \texttt{Pending}(e'', s''.\rho)] \rangle}$$

\hfill (S-SCHEDULE)

**Intuition**: Non-deterministically pick a pending Future from $Q$, execute one step.

*Note: Substep starts with $(\rho', s.\Phi, [])$. If nested `async` creates new Futures, they appear in $s''.\Phi$ (which extends $s.\Phi$) and $s''.Q$.*

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

$$\frac{id \in s.Q \quad \text{lookup}(s.\Phi, id) = \texttt{Pending}(v, \rho) \quad v \text{ is a value}}{\langle e, s \rangle \to \langle e, (s \ominus id)[id \mapsto \texttt{Completed}(v)] \rangle}$$

\hfill (S-COMPLETE)

**Intuition**: Future $id$ finished (expression reduced to value). Remove from $Q$, mark Completed.

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

$$\frac{\text{lookup}(s.\Phi, id) = \texttt{Dependent}(\overline{id'}, f) \quad \forall id' \in \overline{id'}.\, \exists v.\, \text{lookup}(s.\Phi, id') = \texttt{Completed}(v)}{\langle e, s \rangle \to \langle e, s[id \mapsto \texttt{Completed}(f(\text{collect}(s.\Phi, \overline{id'})))] \rangle}$$

\hfill (S-RESOLVE)

**Intuition**: All dependencies completed $\Rightarrow$ resolve Dependent Future.

---

## Main Rules: M-LIFT-OP (1/2)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{Future}(id_1) \mathbin{\mathit{op}} \texttt{Future}(id_2), s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_1, id_2], f_{op})] \rangle}$$
\hfill (M-LIFT-OP-FF)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{Future}(id_1) \mathbin{\mathit{op}} v_2, s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_1], \lambda v_1.\, v_1 \mathbin{op} v_2)] \rangle}$$
\hfill (M-LIFT-OP-FV)

**Intuition**: When operator encounters Future(s), create a new Dependent Future instead of blocking.

---

## Main Rules: M-LIFT-OP (2/2)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle v_1 \mathbin{\mathit{op}} \texttt{Future}(id_2), s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_2], \lambda v_2.\, v_1 \mathbin{op} v_2)] \rangle}$$
\hfill (M-LIFT-OP-VF)

**Combine function $f$**:

- $f : [\text{Val}] \to \text{Val}$ is **not arbitrary** — always constructed by M-LIFT-OP rules
- For binary ops: $f_{op} = \lambda [v_1, v_2].\, v_1 \mathbin{op} v_2$
- S-RESOLVE invokes: $f(\text{collect}(s.\Phi, \overline{id}))$

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

## M-LIFT-OP: Limitations (Why No `&&`/`||`)

| Operator | Liftable? | Reason |
|----------|-----------|--------|
| `+`, `-`, `*`, `/` | Yes | Strict: needs both operands anyway |
| `<`, `=` | Yes | Comparison is strict |
| `&&`, `||` | No | **Short-circuit**: `false && e` must not evaluate `e` |

**The problem**: `Future(id) && e` — we can't decide whether to evaluate `e` without knowing the value of `Future(id)` first. This fundamentally conflicts with lift-to-dependency semantics.

**Design decision**: Omit `&&`/`||` from this core calculus. (Extension: explicit `await` syntax.)

---

## Main Rules: M-AWAIT (1/2)

`await` is **implicit** — triggered at positions requiring concrete values.

$$\frac{\text{lookup}(s.\Phi, id) = \texttt{Completed}(v)}{\langle \texttt{Future}(id), s \rangle \to \langle v, s \rangle}$$
\hfill (M-AWAIT)

$$\frac{\text{lookup}(s.\Phi, id) = \texttt{Completed}(v)}{\langle \texttt{if Future}(id) \texttt{ then } e_2 \texttt{ else } e_3, s \rangle \to \langle \texttt{if } v \texttt{ then } e_2 \texttt{ else } e_3, s \rangle}$$
\hfill (M-AWAIT-IF)

---

## Main Rules: M-AWAIT (2/2)

$$\frac{\text{lookup}(s.\Phi, id) = \texttt{Completed}(v)}{\langle \texttt{Future}(id)\ e, s \rangle \to \langle v\ e, s \rangle}$$
\hfill (M-AWAIT-APP1)

$$\frac{\text{lookup}(s.\Phi, id) = \texttt{Completed}(v')}{\langle v\ \texttt{Future}(id), s \rangle \to \langle v\ v', s \rangle}$$
\hfill (M-AWAIT-APP2)

**Notes**:

- M-AWAIT only extracts values from Futures. Actual $\beta$-reduction requires standard $\lambda$-calculus rules (omitted here).
- **Not demand**: `Future(id) + e` → M-LIFT-OP (builds dependency, no blocking).

---

## Progress Property (1/2)

**Theorem (Progress)**: If $\text{WF}(s)$ and $e$ is not a final value, then:
$$\exists e', s'.\ \langle e, s \rangle \to \langle e', s' \rangle \quad \text{OR} \quad Q \neq []$$

**Globally stuck** only when ALL of:

1. Main needs a Future at a **demand position** (if-cond, function, argument, top-level)
2. That Future not completed: $\text{lookup}(\Phi, id) \neq \texttt{Completed}(\_)$
3. No pending work: $Q = []$

**Key insight**: Main stuck $\neq$ system stuck!

---

## Progress Property (2/2)

**Example trace** (main blocked, system progresses):

```
  <if Future(#0) then..., s>   -- main needs bool, #0 in Q
  -> <if Future(#0) then..., s'>  (S-SCHEDULE)
  -> <if Future(#0) then..., s''> (S-COMPLETE)
  -> <if true then..., s''>       (M-AWAIT)
```

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

**9 Core Rules**:

| Rule | Category | Effect |
|------|----------|--------|
| **M-ASYNC** | Main | Creates Pending Future, adds to $Q$ |
| **M-LIFT-OP** (×3) | Main | Builds Dependent Future (no blocking) |
| **M-AWAIT** (×4) | Main | Extracts value from Completed Future |
| **S-SCHEDULE** | Scheduler | Executes one step of a Pending Future |
| **S-COMPLETE** | Scheduler | Pending → Completed (task done) |
| **S-RESOLVE** | Scheduler | Dependent → Completed (deps ready) |

**Key properties**:

- $\text{WF}(s)$ preserved by all rules
- Progress: system stuck $\Leftrightarrow$ awaiting incomplete Future **and** $Q = \emptyset$
- No fairness/probability — models all interleavings

---

## Questions?

**Repository**: `github.com/MuscleOne/sub_async_release`

**Key files**:

- `src/sub_async/eval.ml` — CPS evaluator
- `src/sub_async/future.ml` — Future state machine
- `src/sub_async/scheduler.ml` — Non-deterministic scheduler
