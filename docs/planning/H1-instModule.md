# `H1.instModule` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:114`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~15 minutes, ~3 LOC (one-line `inferInstance` once `H1` is a `def`)
**Blocked by:** `H1` (`Jacobians/RiemannSurface/LineBundle.lean:104`), `H1.instAddCommGroup` (`:108`)

**Statement (verbatim):**
```lean
axiom H1.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    Module ℂ (H1 L)
attribute [instance] H1.instModule
```

**Why it's an axiom right now:** Companion to `H1.instAddCommGroup`. First Čech cohomology `Ȟ¹(𝒰, L)` is a quotient of a finite product of ℂ-modules (the Čech sections `Č^1(𝒰, L) = ∏_{i<j} L(U_i ∩ U_j)`) by a ℂ-submodule (`im δ⁰`) — so the ℂ-action descends canonically. The instance is `axiom` only because its carrier `H1 L` is `axiom`-opaque; once `H1` becomes a real `def` (see [`H1.md`](H1.md)) returning `L.firstCohomology`, the `Module ℂ` structure propagates as `inferInstance` from the underlying Čech-quotient ℂ-module.

**Proof recipe**

1. Discharge [`H1.md`](H1.md) and [`H1-instAddCommGroup.md`](H1-instAddCommGroup.md) first: this instance composes on top of the `AddCommGroup` instance and so requires `H1 L` to be a real `def` with that instance in scope.

2. Replace the axiom with an `instance` whose body is `inferInstance`. In `Jacobians/RiemannSurface/LineBundle.lean:114`, change
   ```lean
   axiom H1.instModule {X : Type*} [...] (L : LineBundle D) :
       Module ℂ (H1 L)
   attribute [instance] H1.instModule
   ```
   to
   ```lean
   instance H1.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
       Module ℂ (H1 L) := inferInstance
   ```
   The `attribute [instance]` line at `:118` becomes redundant and should be deleted.

3. Reference: Forster Ch. II §13–15 — Čech cohomology of a sheaf of ℂ-modules takes values in ℂ-modules by functoriality. In the Mathlib abstract analog, `Sheaf.H F 1` for a `ModuleCat ℂ`-valued sheaf inherits its ℂ-module structure from the `Ext`-group construction (`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`).

4. Final piece of the four-instance batch ({H0,H1} × {AddCommGroup, Module}); ship all four in the same PR after `H0` and `H1` become real `def`s. Together they retire 4 of the 13 axioms in `LineBundle.lean`.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom H1.instModule` (line 114) with `instance H1.instModule ... := inferInstance`; drop the now-redundant `attribute [instance]` declaration at line 118.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`) no longer lists `H1.instModule`; `#print axioms AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`) no longer lists `H1.instModule`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the eventual `LineBundle` carrier exposes its first cohomology as an abstract `AddCommGroup` without a registered ℂ-module structure (likely if the abstract `Sheaf.H F 1 : Ab` API is used directly), `inferInstance` will fail; escalate to coordinate with [`LineBundle.md`](LineBundle.md) for an explicit `Module ℂ` build.
- If typeclass search ordering causes `H1.instAddCommGroup` and `H1.instModule` to interact (one shadowing the other through definitional unfolding), pin both bodies with `inferInstanceAs` against the underlying `L.firstCohomology` carrier to disambiguate.
