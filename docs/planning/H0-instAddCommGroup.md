# `H0.instAddCommGroup` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:90`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~15 minutes, ~3 LOC (one-line `inferInstance` once `H0` is a `def`)
**Blocked by:** `H0` (`Jacobians/RiemannSurface/LineBundle.lean:85`)

**Statement (verbatim):**
```lean
/-- `H⁰(X, L)` is a ℂ-vector space. -/
axiom H0.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    AddCommGroup (H0 L)
attribute [instance] H0.instAddCommGroup
```

**Why it's an axiom right now:** Pure bookkeeping forced by the axiomatic `H0` type. Global sections of an analytic line bundle form a ℂ-vector space — in any Čech, sheaf-theoretic, or derived-functor model — by pointwise / cocycle addition of holomorphic-section representatives. The instance is `axiom` only because its carrier `H0 L` is still `axiom`-opaque; once `H0` is a real `def` backed by a Čech kernel or `L.globalSections`, the `AddCommGroup` instance propagates automatically from the underlying structure. It requires the `H0` infrastructure to proceed.

**Proof recipe**

1. **Bounded infrastructure piece:** The prerequisite is `def H0 L` (governed by [`H0.md`](H0.md)), which establishes a concrete model for global sections. This infrastructure PR must carry the mathematical heavy lifting of providing the algebraic structures on the sheaf sections.
2. **Post-infra discharge sequence:** In the *exact same PR* that lands the `H0` definition, replace the axiom with an `instance` whose body is `inferInstance` (or `inferInstanceAs (AddCommGroup L.globalSections)` if elaboration needs the hint). In `Jacobians/RiemannSurface/LineBundle.lean:90`, change:
   ```lean
   axiom H0.instAddCommGroup {X : Type*} [...] (L : LineBundle D) :
       AddCommGroup (H0 L)
   attribute [instance] H0.instAddCommGroup
   ```
   to:
   ```lean
   instance H0.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
       AddCommGroup (H0 L) := inferInstance
   ```
   The `attribute [instance]` line at `:94` becomes redundant and must be deleted.
3. **Reference:** This is the analytic analog of the abstract Mathlib pattern — for any abelian sheaf `F` on a site `(C, J)`, `Sheaf.H F 0` (= sections functor on injective resolution = global sections) lives in `Ab` (= `AddCommGrpCat`); see `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic:17–24`. 
4. **Batching:** Mirrored across the file, the exact same pattern applies to `H0.instModule` (`:96`), `H1.instAddCommGroup` (`:108`), and `H1.instModule` (`:114`). All four must be discharged within the same PR when `H0` and `H1` land as `def`s.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom H0.instAddCommGroup` (line 90) with `instance H0.instAddCommGroup ... := inferInstance`; drop the now-redundant `attribute [instance]` declaration at line 94. (Done as part of the `H0` definition PR).

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms AX_RiemannRoch` (downstream consumer in `Jacobians/Axioms/RiemannRoch.lean`) no longer lists `H0.instAddCommGroup`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `H0` is dischargeable only as a minimal-carrier `structure` (per the Next-deliverable paragraph of [`H0.md`](H0.md)) without an analytic `AddCommGroup` content, escalate before committing — the instance would propagate but lose proof-relevance on the underlying section-addition operation.

### Gemini critique addressed:
- Changed route from `mathlib-now` to `needs-infra` since typeclass synthesis fundamentally requires the opaque `H0` axiom to be replaced with a concrete definition first.
- Removed the incorrect risk warning regarding `ModuleCat ℂ`, as Mathlib's bundled category coercions (`Bundled`) to `Type` will automatically synthesize the needed `AddCommGroup` instances without issue.
- Added explicit mandate that this boilerplate instance definition must be folded into the *exact same PR* that implements `def H0`.

---
**Vetting trail.** Critique: `_vetting/H0-instAddCommGroup.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
