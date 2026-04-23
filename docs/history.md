# Work log

Chronological record of work on this repo. Git log is authoritative for code
changes; this file adds the *why* — session context, decisions, reviews,
external feedback, and anything that doesn't fit in a commit message.

Append new entries at the bottom. New day → new `##` section. New commit or
work phase within a day → new `###` subsection.

---

## 2026-04-19: Project start

### Challenge pickup

Kevin Buzzard posted the Jacobian Challenge to Lean Zulip on the morning
of 2026-04-19: a single Lean file (`Jacobians/Challenge.lean`, v0.2) with
24 `sorry`s covering `genus`, `Jacobian`, Abel-Jacobi map `ofCurve`,
pushforward, pullback, degree, and their functoriality theorems. The
challenge is pinned to Mathlib commit `8e3c989` on Lean `v4.30.0-rc1`
and explicitly asks for no Mathlib edits — the formalization lives
downstream.

### Initial scaffold (`873828d`)

- Repo skeleton matching def-study conventions: `Jacobians/`, `docs/`,
  `refs/`, `scripts/`.
- Buzzard's `Challenge.lean` copied verbatim — tracked as the immutable
  target.
- `lakefile.lean` + `lean-toolchain` pinning the exact Mathlib rev.
- `README.md`, `CLAUDE.md`, `PROTOCOL.md`.

### Foundation work (same day, `94b11c6` → `4db4475`)

- CI workflow (`94b11c6`).
- Phase B Mathlib-gap survey (`docs/survey.md`): what's there, what's
  not. Key gaps: differential forms on general manifolds, line integrals,
  sheaf cohomology on complex manifolds, manifold quotients by discrete
  groups.
- References pulled into `refs/`: Milne AV/JV, Debarre AV course (free);
  Mumford Tata I & II (institutional). We'll lean heavily on Mumford.
- Detailed formalization plan (`docs/formalization-plan.md`, ~40 pages).
  Chooses the **period-lattice** construction, basis-free at the type
  level. Rejects algebraic Pic⁰ (needs GAGA), sheaf-cohomology
  `H¹(X, 𝒪)/H¹(X, ℤ)` (no manifold sheaf cohomology in Mathlib), and
  Hodge-decomposition routes.
- Amended plan adds **Track 2** (`4db4475`): concrete projective-curve
  constructions (`ProjectiveLine`, elliptic, hyperelliptic, plane curves)
  each satisfying Buzzard's typeclasses directly. Two parallel tracks
  from this point on.

---

## 2026-04-20: Adversarial review + ProjectiveLine

### Three-round review cycle (`62452c1` → `b73fc16`)

Put the plan through three independent reviews before writing more Lean:

- **Round 1: Gemini 3 Pro deep-think** (`62452c1`) — plan-level review.
  Amended per Gemini findings (`3bb117e`).
- **Round 2: Codex GPT-5** (`cb435a9`) — independent plan review. Applied
  8 Codex amendments (`a3785cf`).
- **Round 3: Claude self-review** (`618275b`) — adversarial bias against
  my own plan. Five **critical** fixes applied (`b73fc16`), including
  the "installed as global instance" requirement for
  `AX_FiniteDimOneForms` (else `Module.finrank` returns 0 on
  infinite-dim, collapsing downstream instances).

Lesson: three rounds of independent review across different models
caught distinct classes of issue. Gemini found mathematical errors,
Codex found Lean-typeclass gotchas, Claude-self found scope-creep in
the plan.

### Track 2: ProjectiveLine (`adeec56` → `5456eb2`)

First concrete scaffolding work. `Jacobians/ProjectiveCurve/Line.lean`:

- `abbrev ProjectiveLine := OnePoint ℂ` (Mathlib's one-point
  compactification).
- Explicit charts `chart0` (away from ∞) and `chart1` (away from 0), via
  `OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph.symm` and
  `Function.update` tricks.
- Continuity of chart1's inverse was the hardest piece — Codex-rescue
  delegation via `/tmp` handoff because sandbox couldn't write to repo.
- `ChartedSpace ℂ ProjectiveLine` (4/7 Buzzard instances, `84768be`).
- `IsManifold 𝓘(ℂ) ω ProjectiveLine` via `isManifold_of_contDiffOn`
  (`9649bf9`).
- `stereographic : ProjectiveLine ≃ₜ S²` via
  `onePointEquivSphereOfFinrankEq` (`5456eb2`).

**Result:** `Line.lean` **zero-sorry**, all 7 X-side Buzzard instances
(TopologicalSpace, T2Space, CompactSpace, ConnectedSpace, Nonempty,
ChartedSpace ℂ, IsManifold 𝓘(ℂ) ω).

### Lean wrinkles learned (recorded in plan `f8c3f27`)

- At this pin `PartialHomeomorph` was renamed to
  `OpenPartialHomeomorph` — hit this on every chart construction.
- `ω` is bound by `ContDiff.Manifold` as the smoothness-level notation;
  don't use it as a 1-form variable name.
- `universe` issues on `abbrev F : Type := ↥sub` — need `: Type _`.

---

## 2026-04-21: Part A (ComplexTorus) + Part B scaffolds

### ComplexTorus 7/7 (`ae26485` → `44a395a`)

`Jacobians/AbelianVariety/ComplexTorus.lean` —
`ComplexTorus V L := V ⧸ L.toAddSubgroup` for `L : Submodule ℤ V` with
`[IsZLattice ℝ L]` in a finite-dim ℂ-vector space.

Two failed attempts first, then a rebuild:

- First attempt used Mathlib's existential chart API (via covering maps)
  → got `ChartedSpace` cheap but couldn't prove `IsManifold` or
  `LieAddGroup` without access to the specific lifts.
- Second attempt with existential-chart-but-with-fixed-center → same
  obstacle.
- Third attempt — **explicit atlas with a fixed global injectivity ball
  around 0 + fixed lifts per point** — unlocks everything. Chart
  transitions are translations by lattice vectors, so all transition
  maps are `ContDiff` automatically.

**Result:** 7/7 Buzzard instances on abstract `(V, L)`, axiom-free,
zero-sorry. Covers Buzzard's ambient-space side of the Jacobian bridge.

**Typeclass pitfalls recorded:**
- `IsDiscrete (L.toAddSubgroup : Set V)` does NOT infer from
  `[DiscreteTopology L]` — bridge via
  `SetLike.isDiscrete_iff_discreteTopology`.
- `Quotient.out'` unavailable at pin — use
  `Classical.choose (QuotientAddGroup.mk'_surjective _)` for lifts.
- `IsZLattice` forces `[NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]` — stronger than the plan's original bundle.

### Deviation from plan (recorded in plan `a864ab0`)

Plan estimated 2–3 weeks for `ComplexTorus`. Actual: **~1 hour** of
Codex pair-programming. The existential-vs-explicit-atlas split was
the key design decision; picking explicit from the start would have
saved the two failed attempts. This matches the community-norm-too-slow
calibration from `~/.claude/CLAUDE.md` — Lean formalization in
familiar territory runs 5–10× faster than the pre-agent estimates.

### Siegel + Theta scaffolds (`18d487f`, `5aad6f4`)

- `Jacobians/AbelianVariety/Siegel.lean` — `SiegelUpperHalfSpace g` as
  a `Subtype` of `Matrix (Fin g) (Fin g) ℂ`. Switched from `structure`
  to `Subtype` per Gemini round 2: `structure` loses auto-inherited
  `TopologicalSpace`, `MetricSpace`, `NormedAddCommGroup` from the
  ambient matrix space.
- `Jacobians/AbelianVariety/Theta.lean` — `RiemannTheta z τ := ∑' n,
  thetaSummand z τ n`. Summability, analyticity, quasi-periodicity,
  heat equation all scaffolded TODOs.

### Gemini round-2 review (`ce6ccd0`, `docs/gemini-review-2.md`)

Gemini vetted Siegel + Theta + emerging Part B architecture. Three
architectural concerns recorded for Part B bridge:

1. **`NormedAddCommGroup` trap** on `ComplexTorus V L`: `IsZLattice`
   demands norm structure, but `HolomorphicOneForm X →ₗ[ℂ] ℂ` has no
   canonical norm (the Hodge inner product is downstream of the period
   matrix itself).
2. **`Classical.choose`-based charts** risk simp-opacity unless we keep
   strong rewrite lemmas.
3. **Dual `ChartedSpace` instance risk** (ambient `V` vs `Fin g → ℂ`):
   bake the basis into the `Jacobian` definition at the bridge.

Quick fixes applied; architectural concerns deferred to the bridge.

### Part B scaffolds (`19c7b3f` → `31a6bc7`)

- `Jacobians/RiemannSurface/OneForm.lean` — `HolomorphicOneForm X` as a
  `Submodule ℂ (X → ℂ → ℂ)` with two predicates (`IsHolomorphicOneFormCoeff`,
  `SatisfiesCotangentCocycle`), both currently stub-`True`. *Known
  issue at this point: the stub carrier is `⊤`, not yet flagged as
  unsound.*
- `Jacobians/RiemannSurface/Homology.lean` —
  `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))`.
- `Jacobians/Axioms/FiniteDimOneForms.lean` — first named axiom.
  Installed as global instance per Codex/Claude review. *This is
  where the 2026-04-22 unsoundness later bites.*
- `Jacobians/RiemannSurface/Genus.lean` —
  `genus X := Module.finrank ℂ (HolomorphicOneForm X)`.
- `Jacobians/RiemannSurface/Periods.lean` + `IntersectionForm.lean` —
  `periodMap` declared as axiom-stub for a `def`; `AX_PeriodInjective`
  as separate axiom.

### Remaining axioms declared (`4b6fbe6`)

Seven more axiom files added: `H1FreeRank2g`, `RiemannBilinear`,
`RiemannRoch`, `SerreDuality`, `AbelTheorem`, `BranchLocus`,
`PluckerFormula`. Two with Lean signatures at this pin (H1FreeRank2g
via `Module.Basis`; others need consumer-module types and stay
doc-only with target-signature sketches).

---

## 2026-04-22: Gemini axiom review + unsoundness fix + Jacobian bridge

### Gemini round-3 axiom review

Solicited adversarial review of the full axiom suite from `gemini-3-pro-preview`
(Deep Think timed out after 5 min). Saved to
`docs/gemini-review-axioms.md`.

**Top finding — CRITICAL:**

`AX_FiniteDimOneForms` installed as a global instance on top of the
`True ∧ True` submodule stub **injects `False` into the environment**.

Verified exploit via `lean_run_code`:

1. Stub carrier `{f | True ∧ True}` equals `⊤` as a submodule.
2. Hence `HolomorphicOneForm X ≃ₗ[ℂ] (X → ℂ → ℂ)` via
   `Submodule.topEquiv`.
3. The FD instance transfers → `FiniteDimensional ℂ (X → ℂ → ℂ)`.
4. `[ConnectedSpace X]` extends `[Nonempty X]`; extract `x₀`.
5. Evaluation at `x₀` gives a surjective
   `(X → ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ)`.
6. `Module.Finite.of_surjective` → `FiniteDimensional ℂ (ℂ → ℂ)`.
7. `rank_fun_infinite` + `Cardinal.aleph0_le_mk ℂ` → contradiction.

Any `exfalso` could have closed all 24 Buzzard sorries. Four days of
"progress" on a poisoned environment.

**Fix (`3c9940e`):**

- Switched submodule stub carrier to `⊥`:
  `holomorphicOneFormSubmodule X := (⊥ : Submodule ℂ (X → ℂ → ℂ))`
  (noncomputable).
- `HolomorphicOneForm X` is now 0-dim (provably).
- `instFiniteDimOneForms` elaborates via `unfold; infer_instance` from
  `Submodule.finiteDimensional_bot` — **no axiom invocation at the
  stub**.
- `genus X = 0` provably at the stub. The theorem sorry
  `genus_eq_zero_iff_homeo` is unclosable at stub level, but that's
  fine — it opens up honestly when `OneForm` predicates are refined.
- `AX_FiniteDimOneForms` axiom stays declared for the refinement phase.
- `lean_run_code` verified the exploit no longer closes.

**Other Gemini findings recorded:**

- `AX_RiemannBilinear` target signature needs existentials shifted over
  basis choice (original was mathematically false — `[I|τ]` holds only
  for symplectic-normalized bases).
- `AX_RiemannRoch` / `AX_SerreDuality` need `FiniteDimensional`
  hypotheses + ℤ-subtraction (else silently vacuous).
- `AX_PeriodInjective` too weak for Jacobian-as-complex-torus → needs
  `AX_PeriodLattice` (`IsZLattice`) upgrade.
- Missing `AX_IntersectionForm` — "symplectic basis" has no formal
  meaning without it.
- `AX_BranchLocus` should use `tsum` instead of `toFinset`.

### Gemini round-3 revisions applied (`85bcf7e`)

- New `Jacobians/Axioms/IntersectionForm.lean` — `intersectionForm`
  axiom-stub + `AX_IntersectionForm_{alternating, nondeg}`.
- Doc-only target signatures revised: `RiemannBilinear` shifts
  existentials, `RiemannRoch`/`SerreDuality` bundle FD + cast to ℤ,
  `BranchLocus` uses `tsum`.
- Discharge priority reordered infrastructure-first in plan §7.
- `AX_PeriodLattice` upgrade deferred to the Jacobian bridge, where the
  `NormedAddCommGroup`-on-ambient decision actually bites.

### Jacobian bridge (`87253d1`)

Codex-delivered in one session. Architectural approach: bake the basis
into the `Jacobian` definition, dodging Gemini round-2's dual-ChartedSpace
warning.

- `Jacobians/Axioms/PeriodLattice.lean` — `periodMapInBasis X x₀ b`
  composes `periodMap` with `b.dualBasis.equivFun` via
  `AddMonoidHom.toIntLinearMap`; `periodLatticeInBasis` as its range;
  `AX_PeriodLattice` asserting `IsZLattice ℝ ...` + `instPeriodLatticeDiscrete`.
- `Jacobians/Jacobian/Construction.lean` —
  `jacobianBasis X := Module.finBasis ℂ (HolomorphicOneForm X)`;
  `Jacobian X := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X
  (Classical.choice ‹Nonempty X›) (jacobianBasis X))`. All seven Buzzard
  instances (AddCommGroup, TopologicalSpace, T2Space, CompactSpace,
  ChartedSpace over `Fin (genus X) → ℂ`, IsManifold, LieAddGroup)
  elaborate via `change + infer_instance` off `ComplexTorus`.
- `Jacobians/Jacobian.lean` — top-level Part-C aggregator.

**Architectural wins:**

- Basis baked in → single `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`
  instance, matching Buzzard's signature exactly.
- No `NormedAddCommGroup` trap — ambient `Fin (genus X) → ℂ` has
  Mathlib's Pi normed structure for free.
- At the current stub (`genus X = 0` provably), `Jacobian X` is a
  0-dim complex torus; all instances still elaborate. Real content
  arrives automatically when `OneForm.lean` predicates get refined.

**Deferred:** universe-lift wrapper (`ComplexTorus (Fin (genus X) → ℂ)` is
`Type`, Buzzard asks `Type u`); basepoint-independence via
`AX_RiemannBilinear`; `ofCurve` + `pushforward` + `pullback` (need
`PathIntegral.lean`).

### Reproducibility fix (`e34d9a4`)

`lake-manifest.json` had been untracked the whole time. Committed for
reproducibility — pins Mathlib to `8e3c989` plus transitive deps.
Without it, `lake update` would drift from the challenge's fixed pin.

---

### Universe lift + 8 Buzzard sorries closed (same day, late)

With the bridge committed but stuck in `Type` while Buzzard asks for
`Type u`, the path forward was a ULift wrapper. Approach:

1. **Generic `chartedSpaceULift` transfer.** `ChartedSpace H M ⟹
   ChartedSpace H (ULift M)` by composing each chart with
   `Homeomorph.ulift.toOpenPartialHomeomorph`.
2. **`ulift_charts_eqOnSource` key lemma.** The transition between two
   ULift-composed charts is `EqOnSource`-equivalent to the downstairs
   transition. Proof chain: `trans_symm_eq_symm_trans_symm`,
   `trans_assoc`, `OpenPartialHomeomorph.symm_trans_self`,
   `ofSet_univ_eq_refl`, `refl_trans`.
3. **`uliftHasGroupoid`.** Any `HasGroupoid M (contDiffGroupoid n I)`
   transfers to `ULift M` because `StructureGroupoid.mem_of_eqOnSource`
   closes the gap.
4. **`IsManifold.mk'`** lifts `HasGroupoid` to `IsManifold`.

After that: `Jacobian (X : Type u) := ULift.{u, 0} (JacobianAmbient X)`
where `JacobianAmbient X` is the concrete `ComplexTorus` (made `abbrev`
so Mathlib's ULift-ABG/TS/T2/CompactSpace instances fire via
transparent unfolding).

**Six instances auto-derive via ULift**: `AddCommGroup`,
`TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace`,
`IsManifold`.

`LieAddGroup` transfer needs `IsTopologicalAddGroup (ULift _)` +
`ContMDiff` of add/neg through ULift — significant additional work.
Punted.

**Edited `Challenge.lean`** to fill:
- `genus` → `Jacobians.RiemannSurface.genus X` (line 47).
- `Jacobian` → `Jacobians.Jacobian X` (line 61).
- 6 instance sorries via `inferInstanceAs` / `change + infer_instance`.
- `noncomputable` added to `def genus`, `def Jacobian`, and the data
  instances (forced by Mathlib's `Module.finrank` being noncomputable
  and `Classical.choice` on the basepoint).
- `LieAddGroup` sorry at line 101 left unchanged.

Delegated initial attempt to Codex (agent `a93ef786914eecbc9`) which
timed out without producing output — finished manually via iterative
`lean_build` / `lean_run_code` using the lean-lsp MCP server to verify
each transfer lemma before committing.

**Result: 8 Buzzard sorries closed, 16 remain** (all in
`Challenge.lean`: `LieAddGroup` instance, 5 data defs, 10 theorems).

## Status snapshot (end of 2026-04-22)

- **Build:** green, 8328 jobs.
- **Sorries:** 16 in `Jacobians/Challenge.lean` (down from 24). Zero
  elsewhere.
- **Buzzard bridge:** `genus`, `Jacobian`, 6 of 7 typeclass instances
  filled via `Jacobians.Jacobian` (ULift-lifted complex torus).
  Remaining: `LieAddGroup`, Abel-Jacobi family (`ofCurve` + 3
  theorems), pushforward family (def + 3 theorems), pullback family
  (def + 3 theorems), `ContMDiff.degree`, `pushforward_pullback`,
  `genus_eq_zero_iff_homeo`.
- **Axioms declared with Lean signatures (10):** `AX_FiniteDimOneForms`,
  `AX_H1FreeRank2g`, `intersectionForm` +
  `AX_IntersectionForm_{alternating, nondeg}`, `AX_PeriodLattice` +
  `instPeriodLatticeDiscrete`, `AX_PeriodInjective`, `periodMap`
  (axiom-stub).
- **Axioms declared doc-only (6):** `AX_RiemannBilinear`,
  `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`,
  `AX_BranchLocus`, `AX_PluckerFormula`.
- **Part A** (`AbelianVariety/`): `ComplexTorus` complete (7/7
  instances, axiom-free); `Siegel` + `Theta` scaffolds.
- **Part B** (`RiemannSurface/`): `OneForm` safe stub; `Homology`,
  `Genus`, `Periods`, `IntersectionForm` scaffolds. `PathIntegral` not
  started.
- **Part C** (`Jacobian/`): `Construction.lean` bridges the abstract
  surface to the complex torus with 7 instances. `ofCurve`,
  `pushforward`, `pullback` not started.
- **Track 2** (`ProjectiveCurve/`): `Line` complete (7/7, 0 sorries).
  `Elliptic`, `Hyperelliptic`, `PlaneCurve` not started.
