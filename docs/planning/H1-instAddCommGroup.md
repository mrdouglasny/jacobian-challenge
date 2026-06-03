# `H1.instAddCommGroup` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:108`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~15 minutes, ~3 LOC (bundled with H1 definition)
**Blocked by:** `H1` (`Jacobians/RiemannSurface/LineBundle.lean:104`)

**Statement (verbatim):**
```lean
axiom H1.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    AddCommGroup (H1 L)
attribute [instance] H1.instAddCommGroup
```

**Why it's an axiom right now:** Pure bookkeeping forced by the axiomatic `H1` type. First Čech cohomology `Ȟ¹(𝒰, L) = ker δ¹ / im δ⁰` is a quotient of a finite product of ℂ-modules by a sub-ℂ-module — so it carries a canonical `AddCommGroup` structure for free. The instance is `axiom` only because its carrier `H1 L` is still `axiom`-opaque; once `H1` becomes a real `def` (see [`H1.md`](H1.md)) returning `L.firstCohomology` (a bespoke Čech kernel-modulo-image), the instance propagates automatically.

**Proof recipe**

1. Wait for [`H1.md`](H1.md) (the prerequisite needs-infra recipe, effort 9) to land a real `def H1 L := L.firstCohomology`. The `LineBundle` recipe ([`LineBundle.md`](LineBundle.md)) and the `H1` recipe will construct `L.firstCohomology` as a quotient of the Čech cocycle group by the coboundary group. Because these are built using standard algebraic constructions, `QuotientAddGroup` will provide the `AddCommGroup` instance automatically.

2. Replace the axiom with an `instance` whose body is `inferInstance` (or `inferInstanceAs (AddCommGroup L.firstCohomology)` if elaboration needs the hint). In `Jacobians/RiemannSurface/LineBundle.lean:108`, change
   ```lean
   axiom H1.instAddCommGroup {X : Type*} [...] (L : LineBundle D) :
       AddCommGroup (H1 L)
   attribute [instance] H1.instAddCommGroup
   ```
   to
   ```lean
   instance H1.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
       AddCommGroup (H1 L) := inferInstance
   ```
   The `attribute [instance]` line at `:112` becomes redundant and should be deleted.

3. Reference: in the Čech model (Forster Ch. II §13), `Ȟ¹` is a subquotient of a finite product of ℂ-modules; the resulting `AddCommGroup` is canonical. In Lean, deriving this relies on applying `QuotientAddGroup` to the bespoke Čech complex construction.

4. Mirror of [`H0-instAddCommGroup.md`](H0-instAddCommGroup.md) and one of the four trivial-propagation siblings; batch all four (`H0.instAddCommGroup`, `H0.instModule`, `H1.instAddCommGroup`, `H1.instModule`) in the same PR once `H0` and `H1` are real `def`s.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom H1.instAddCommGroup` (line 108) with `instance H1.instAddCommGroup ... := inferInstance`; drop the now-redundant `attribute [instance]` declaration at line 112.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`) no longer lists `H1.instAddCommGroup`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `H1` is defined directly such that typeclass inference fails to find the underlying `AddCommGroup` via `QuotientAddGroup` (e.g., if the module structure is bundled differently), escalate to coordinate API choice with [`LineBundle.md`](LineBundle.md) and [`H1.md`](H1.md).
- If typeclass search picks up an unintended `AddCommGroup` (e.g. through a coercion to a `ModuleCat` object that has its own group structure), pin the body with `inferInstanceAs` to disambiguate.

### Gemini critique addressed:
- Changed **Route** from `mathlib-now` to `needs-infra`, properly classifying this as an administrative task necessarily bundled with the `H1` infrastructure.
- Removed hallucinated Mathlib references to `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` and the `Sheaf.H` derived functor API, which do not currently exist in Mathlib.
- Explicitly stated the instance will derive via `QuotientAddGroup` applied to the bespoke Čech cocycle/coboundary construction.

---
**Vetting trail.** Critique: `_vetting/H1-instAddCommGroup.md`. Verdict: revise. Revised: 2026-06-03.