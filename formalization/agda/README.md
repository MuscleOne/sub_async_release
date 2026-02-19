# Sub_Async Agda Mechanization

Mechanization for the λ_fut semantics in the Functional Pearl submission.

## Snapshot (2026-02-19)

- Agda source size: **2924 LOC** (`wc -l *.agda`)
- Key modules compile from scratch with `--ignore-interfaces`:
	- `WFPreservation.agda` ✅
	- `TypePreservation.agda` ✅
- `WF-preserved` is fully mechanized (all 9 rules routed to proved lemmas).
- Type preservation remains **partial by design** (explicit postulates remain).

## Module map

```
SubAsync.agda        — Syntax/runtime objects (Expr, Value, Status, State)
WellFormedness.agda  — WF predicate, fresh-id, state update operators
Reductions.agda      — 9 reduction rules as inductive relation (_⟶_)
Types.agda           — Type system, subtyping, WT/EntryTyped definitions
WFPreservation.agda  — WF preservation theorem (complete)
TypePreservation.agda — Type preservation case developments (partial)
Examples.agda        — 12 executable step proofs
artifacts/           — audit notes, review reports
traces/              — traces from OCaml reference implementation
```

## Postulate inventory (current)

### Metatheory-facing postulates

- `WFPreservation.agda`
	- `NeedsFuture'`
	- `stuck-characterization`
- `TypePreservation.agda`
	- `funV-typing`
	- `S-SCHEDULE-type-preserves`
	- `type-preserved`

### Infrastructure/semantic abstraction postulates

- `SubAsync.agda`
	- `Var`, `_≟ᵥ_`, `CombineFunction`, `apply-combine`
- `Reductions.agda`
	- `_/_`, `eval-app`, `eval-app-val`
- `Examples.agda`
	- test variable symbols (`varX`, `varY`, `...`)

## Reproducibility commands

Run from `formalization/agda/`:

```bash
agda --version
agda --ignore-interfaces WFPreservation.agda
agda --ignore-interfaces TypePreservation.agda
```

Or run the script:

```bash
bash audit.sh
```

The script performs clean checks and writes a postulate inventory to `artifacts/`.

## Notes on trust boundary

- `WFPreservation.agda` includes two postulates at the bottom for stuck characterization; these are outside `WF-preserved` itself.
- The project does **not** currently pass `--safe` end-to-end because foundational syntax/runtime abstractions are postulated in `SubAsync.agda`.
- Paper claims should therefore be scoped precisely: complete WF-preservation mechanization, partial type-preservation mechanization.