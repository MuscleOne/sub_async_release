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

1. **Language Motivation**: Space/Time Decoupling
2. **Formalization Motivation**: Externalize runtime state
3. **Abstract Syntax**: Expressions, values, Future status
4. **Configuration**: $\langle e, s \rangle$ where $s = (\rho, \Phi, Q)$
5. **Well-Formedness**: Invariant $\text{WF}(s)$
6. **6 Core Rules** (+ E-CONTEXT):
   - Main: M-ASYNC, M-LIFT-OP, M-AWAIT
   - Scheduler: S-SCHEDULE, S-COMPLETE, S-RESOLVE
7. **Progress**: Under $\text{WF}(s)$, never globally stuck
8. **Comparison with Aeff**

---

## Why Sub_Async? (Language Motivation)

**Core idea**: Space/time decoupling through implicit async coordination.

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

## Abstract Syntax (1/2)

**Expressions**:
$$e ::= x \mid n \mid b \mid e_1 \mathbin{\mathit{op}} e_2 \mid \texttt{if } e_1 \texttt{ then } e_2 \texttt{ else } e_3$$
$$\mid \texttt{fun } x \texttt{ is } e \mid e_1\ e_2 \mid \texttt{let } x = e_1 \texttt{ in } e_2 \mid \texttt{async } e$$

**Operators**: $\mathit{op} \in \{+, -, *, /, <, =\}$ (strict, liftable to Futures)

*Note: Short-circuit operators* (`&&`, `||`) *omitted — incompatible with Future lifting (see Limitations).*

**Values**:
$$v ::= n \mid b \mid \langle x, e, \rho \rangle \mid \texttt{Future}(id)$$

**Environments**:
$$\rho ::= \emptyset \mid \rho[x \mapsto v]$$

---

## Abstract Syntax (2/2)

**Lists**:
$$\textit{ids} ::= [\,] \mid id :: \textit{ids} \qquad \textit{vs} ::= [\,] \mid v :: \textit{vs}$$

**Auxiliary functions**:
$$\text{range}(\rho) \triangleq \{v \mid \exists x.\ \rho(x) = v\}$$
$$\text{collect}(\Phi, [\,]) = [\,]$$
$$\text{collect}(\Phi, id :: \textit{ids}) = v :: \text{collect}(\Phi, \textit{ids}) \quad \text{when } \Phi(id) = \texttt{Completed}(v)$$

**Restricted sub-language** $e_f$ (Future task bodies — no nested `async`):
$$e_f ::= x \mid n \mid b \mid e_f \mathbin{\mathit{op}} e_f \mid \texttt{if } e_f \texttt{ then } e_f \texttt{ else } e_f \mid \texttt{fun } x \texttt{ is } e_f \mid e_f\ e_f \mid \texttt{let } x = e_f \texttt{ in } e_f$$

*This is the full language minus* `async` *— ensures tasks cannot spawn sub-tasks.*

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
$$s \oplus id \triangleq (\rho, \Phi, Q \cup \{id\}) \qquad s \ominus id \triangleq (\rho, \Phi, Q \mathbin{\backslash} \{id\})$$
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
- `Future(id) op v` $\to$ creates $\texttt{Dependent}([id], f)$

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
$$E ::= [\,] \mid E\ e \mid v\ E \mid E \mathbin{\mathit{op}} e \mid v \mathbin{\mathit{op}} E \mid \texttt{let } x = E \texttt{ in } e \mid \texttt{if } E \texttt{ then } e_2 \texttt{ else } e_3$$

**Demand contexts** $E_d$ (positions requiring **concrete** value → triggers M-AWAIT):
$$E_d ::= [\,]\ e \mid v\ [\,] \mid \texttt{if } [\,] \texttt{ then } e_2 \texttt{ else } e_3$$

**Key design**: $\mathit{op}$ positions are **not** in $E_d$ — Futures at operator positions trigger M-LIFT-OP (builds dependency) instead of M-AWAIT (blocks).

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

## Main Rules: M-ASYNC

**Formal**:

$$\frac{id = \text{fresh}(s.\Phi) \quad e \in e_f}{\langle \texttt{async } e, s \rangle \to \langle \texttt{Future}(id), (s \oplus id)[id \mapsto \texttt{Pending}(e, s.\rho)] \rangle}$$
\hfill (M-ASYNC)

**Intuition**: `async e` immediately returns `Future(id)`, adds $id$ to $Q$.

**Restriction**: $e \in e_f$ ensures task body contains no nested `async`.

*Note: Environment $s.\rho$ may contain Futures — this allows patterns like:*
```
let x = async 1 in async (x + 1)   (* OK: x is Future, captured in env *)
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

$$\frac{id \in s.Q \quad s.\Phi(id) = \texttt{Pending}(e', \rho') \quad (e', \rho') \to_f (e'', \rho'')}{\langle e, s \rangle \to \langle e, s[id \mapsto \texttt{Pending}(e'', \rho'')] \rangle}$$

\hfill (S-SCHEDULE)

where $\to_f$ is the standard small-step relation **restricted to $e_f$** (no async/Future ops).

**Intuition**: Non-deterministically pick a pending Future from $Q$, execute one step, update $\Phi$.

**Note**: Since $e' \in e_f$, the step $\to_f$ cannot create new Futures or modify $(\Phi, Q)$.

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

## Main Rules: M-LIFT-OP

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{Future}(id_1) \mathbin{\mathit{op}} \texttt{Future}(id_2), s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_1, id_2], f_{op})] \rangle}$$
\hfill (M-LIFT-OP-FF)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle \texttt{Future}(id_1) \mathbin{\mathit{op}} v_2, s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_1], \lambda v_1.\, v_1 \mathbin{op} v_2)] \rangle}$$
\hfill (M-LIFT-OP-FV)

$$\frac{id = \text{fresh}(s.\Phi)}{\langle v_1 \mathbin{\mathit{op}} \texttt{Future}(id_2), s \rangle \to \langle \texttt{Future}(id), s[id \mapsto \texttt{Dependent}([id_2], \lambda v_2.\, v_1 \mathbin{op} v_2)] \rangle}$$
\hfill (M-LIFT-OP-VF)

where $f_{op}([v_1, v_2]) = v_1 \mathbin{op} v_2$ (semantic interpretation of operator $op$).

**Combine function** $f$: Partial function from value list to value. Always total for well-formed $\Phi$.

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

## Main Rules: M-AWAIT

**Note**: `await` is not explicit syntax — triggered implicitly at **demand contexts** $E_d$.

**Rule for demand contexts**:
$$\frac{s.\Phi(id) = \texttt{Completed}(v)}{\langle E_d[\texttt{Future}(id)], s \rangle \to \langle E_d[v], s \rangle}$$
\hfill (M-AWAIT)

**Rule for top-level result** (program needs final value):
$$\frac{s.\Phi(id) = \texttt{Completed}(v)}{\langle \texttt{Future}(id), s \rangle \to \langle v, s \rangle}$$
\hfill (M-AWAIT-FINAL)

**Instances of $E_d$**: if-condition, function operator/argument positions.

**Not in $E_d$**: $\mathit{op}$ positions (Futures trigger M-LIFT-OP instead).

**If not completed?** The term is **stuck** — but S-SCHEDULE can still fire!

---

## Progress Property

**Theorem (Progress)**: If $\text{WF}(s)$ and $e$ is not a final value, then:
$$\exists e', s'.\ \langle e, s \rangle \to \langle e', s' \rangle \quad \text{OR} \quad Q \neq \emptyset$$

**Globally stuck** only when ALL of:

1. Main needs a Future: $e = E_d[\texttt{Future}(id)]$ or $e = \texttt{Future}(id)$
2. That Future not completed: $\Phi(id) \neq \texttt{Completed}(\_)$
3. No pending work: $Q = \emptyset$

**Key insight**: Main stuck $\neq$ system stuck!

```
Trace (main blocked, system progresses):
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

**Non-deterministic Semantics**: 6 Core Rules + E-CONTEXT

| Rule | Category | Effect |
|------|----------|--------|
| **M-ASYNC** | Main | Creates Pending Future, adds to $Q$ |
| **M-LIFT-OP** | Main | Builds Dependent Future (no blocking) |
| **M-AWAIT** | Main | Extracts value from Completed Future |
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
