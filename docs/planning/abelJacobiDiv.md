# `abelJacobiDiv` — discharge recipe

**Location:** `Jacobians/Axioms/AbelTheorem.lean:60`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~15 minutes, ~5 LOC
**Blocked by:** `Divisor`, `Divisor.instAddCommGroup`, `Divisor.deg` (`Jacobians/RiemannSurface/LineBundle.lean:51,56,63`)

**Statement (verbatim):**
```lean
/-- **Axiom-stub (data).** The Abel-Jacobi map extended linearly from
points to divisors. On a formal combination `∑ n_P · P`, evaluates to
`∑ n_P · ofCurveImpl P₀ P - (∑ n_P) · ofCurveImpl P₀ P₀`; basepoint
`P₀` is chosen via `Classical.arbitrary`. -/
axiom abelJacobiDiv (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Divisor X →+ Jacobian X
```

**Basepoint convention (revised; see cross-plan patch 2026-06-03).** The discharge below now takes the basepoint as an explicit parameter `(P₀ : X)` rather than fixing it via a global `Classical.choice ‹Nonempty X›`. This is required for compatibility with `AX_AbelTheorem`, whose `⊆` proof needs the basepoint to dynamically avoid `supp(D⁺) ∪ supp(D⁻)`. Concretely, we expose
```lean
noncomputable def abelJacobiDivAt (X : Type u) [...] (P₀ : X) : Divisor X →+ Jacobian X
```
and then define the parameter-free top-level
```lean
noncomputable def abelJacobiDiv (X : Type u) [...] : Divisor X →+ Jacobian X :=
  abelJacobiDivAt X (Classical.choice ‹Nonempty X›)
```
purely as a back-compat shim for callers that do not care which basepoint is used (e.g. `AX_ofCurve_inj` statements that depend only on the kernel, which is basepoint-independent). The `AX_AbelTheorem` proof itself must call `abelJacobiDivAt X P₀` with a `P₀ ∉ supp D` selected per-divisor (see `AX_AbelTheorem.md` Step 5). A basepoint-independence lemma
```lean
lemma abelJacobiDivAt_independent (P₀ Q₀ : X) (D : Divisor X) (hD : Divisor.deg X D = 0) :
    abelJacobiDivAt X P₀ D = abelJacobiDivAt X Q₀ D
```
will be needed to reconcile the two on degree-0 divisors; this is a straightforward telescoping argument (`ofCurveImpl X P₀ P - ofCurveImpl X Q₀ P = ofCurveImpl X P₀ Q₀` is independent of `P`, and contributes `(∑ n_P) · ofCurveImpl X P₀ Q₀ = 0` when `∑ n_P = 0`).

**Why it's an axiom right now:** This is pure linear-algebraic data: the `ℤ`-linear extension of `ofCurveImpl X P₀ : X → Jacobian X` to formal `ℤ`-combinations of points. It is axiomatized only because `Divisor X` is itself an opaque axiom-stub at `LineBundle.lean:51`; once `Divisor X` is realized as `FreeAbelianGroup X` (its planned encoding per ROADMAP), the universal property of `FreeAbelianGroup` discharges this in a handful of lines. Nothing classical (no sheaf cohomology, no meromorphic functions) is needed — only the curve-side `ofCurveImpl` def already lives in `Jacobians/Axioms/AbelJacobiMap.lean:229`.

**Proof recipe**

1. Land the `Divisor` infrastructure first. Replace the opaque axiom `Divisor X` (`Jacobians/RiemannSurface/LineBundle.lean:51`) with
   ```lean
   def Divisor (X : Type*) [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] : Type := FreeAbelianGroup X
   ```
   Then `Divisor.instAddCommGroup` (`LineBundle.lean:56`) reduces to `FreeAbelianGroup.instAddCommGroup` from Mathlib (`Mathlib.GroupTheory.FreeAbelianGroup`) and `Divisor.deg` (`LineBundle.lean:63`) reduces to `FreeAbelianGroup.lift (fun _ => (1 : ℤ))`. These three are the prerequisite recipes [`Divisor.md`](Divisor.md), [`Divisor-instAddCommGroup.md`](Divisor-instAddCommGroup.md), [`Divisor-deg.md`](Divisor-deg.md).

2. Take the basepoint as an explicit parameter. Per the cross-plan patch (2026-06-03), do **not** fix the basepoint by `Classical.choice` inside the definition. Instead, introduce the parameter-bearing form
   ```lean
   noncomputable def abelJacobiDivAt (X : Type u) [...] (P₀ : X) : Divisor X →+ Jacobian X
   ```
   which takes the basepoint as an explicit argument. Callers needing pole avoidance (notably the `⊆` direction of `AX_AbelTheorem`) supply `P₀ ∉ supp D` directly. The legacy nullary form `abelJacobiDiv X` is retained only as a thin shim defined as `abelJacobiDivAt X (Classical.choice ‹Nonempty X›)` for callers that only inspect the kernel (kernel is basepoint-independent on degree-0 divisors).

3. Define the underlying group hom via `FreeAbelianGroup.lift`. Recall that `FreeAbelianGroup.lift : (X → A) ≃ (FreeAbelianGroup X →+ A)` for any `AddCommGroup A` (Mathlib, `Mathlib.GroupTheory.FreeAbelianGroup.lift`). The `Jacobian X` carries `AddCommGroup` via the construction in `Jacobians/Jacobian/Construction.lean` (cited at `Jacobians/Axioms/AbelJacobiMap.lean:53`). Set:
   ```lean
   noncomputable def abelJacobiDivAt (X : Type u) [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] (P₀ : X) : Divisor X →+ Jacobian X :=
     FreeAbelianGroup.lift (fun P => ofCurveImpl X P₀ P)

   noncomputable def abelJacobiDiv (X : Type u) [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] : Divisor X →+ Jacobian X :=
     abelJacobiDivAt X (Classical.choice ‹Nonempty X›)
   ```
   The `ofCurveImpl X P₀ P₀ = 0` already holds definitionally (proved as `AX_ofCurve_self` at `Jacobians/Axioms/AbelJacobiMap.lean:246`), so the docstring's "subtract `(∑ n_P) · ofCurveImpl P₀ P₀`" correction is automatic — the basepoint summand vanishes in the image, so the lift over `(P ↦ ofCurveImpl X P₀ P)` is already the docstring's stated map (the `(∑ n_P) · ofCurveImpl P₀ P₀` term is just `0`).

4. Convert axiom to definition. In `Jacobians/Axioms/AbelTheorem.lean:60`, replace `axiom abelJacobiDiv ...` with the `noncomputable def` from step 3. Remove the `axiom` keyword; keep the exact same signature so downstream consumers still see `Divisor X →+ Jacobian X`.

5. Sanity-check downstream. `AX_AbelTheorem` (`Jacobians/Axioms/AbelTheorem.lean:66`) references `abelJacobiDiv X`; it must still typecheck. No `simp`-lemmas about the new `def` are needed for it (it only talks about `.ker`).

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — discharge `Divisor`, `Divisor.instAddCommGroup`, `Divisor.deg` (prerequisites; tracked in their own recipes).
- `Jacobians/Axioms/AbelTheorem.lean` — replace `axiom abelJacobiDiv` (line 60) with a `noncomputable def` using `FreeAbelianGroup.lift` and `ofCurveImpl` + `Classical.choice`.

**Acceptance**
- `lake build Jacobians.Axioms.AbelTheorem` succeeds.
- `#print axioms AX_AbelTheorem` still lists `AX_AbelTheorem` and `PrincipalDivisors` but no longer lists `abelJacobiDiv`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the `Divisor = FreeAbelianGroup X` discharge changes the signature of `Divisor X` (e.g. universe polymorphism shift), escalate — `abelJacobiDiv` consumers (downstream `AX_AbelTheorem`, `AX_ofCurve_inj`) will need their universe parameters re-aligned.
- If `Jacobian X` turns out not to be a bare `AddCommGroup` at the universe where `FreeAbelianGroup.lift` expects it (note the `ULift.up` wrapping at `AbelJacobiMap.lean:232`), wrap `ofCurveImpl` in an `AddMonoidHom`-friendly form or use `ULift.addMonoidHom` — escalate if this requires changing the `ofCurveImpl` signature.
- If `Classical.choice` proves problematic for `#print axioms` (it is acceptable and pervasive, but might be flagged by strict linters), escalate to redesign the signature if a basepoint-free definition is mandated.

### Gemini critique addressed
- **Effort recalibrated:** Reduced Effort from 3 to 1 and estimated LOC from ~80 to ~5, reflecting that this map is a trivial 1-line definition once `Divisor X` maps to `FreeAbelianGroup X`.
- **Typeclass fix:** Replaced `Classical.arbitrary X` with `Classical.choice ‹Nonempty X›`. The `abelJacobiDiv` axiom signature only provides `[Nonempty X]`, so `Classical.arbitrary` would have caused a typeclass synthesis failure for `[Inhabited X]`.

---
**Vetting trail.** Critique: `_vetting/abelJacobiDiv.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Refactored `abelJacobiDiv` to expose an explicit-basepoint variant `abelJacobiDivAt X P₀` so `AX_AbelTheorem`'s `⊆` proof can choose `P₀ ∉ supp D`; the nullary `abelJacobiDiv X` is retained as a `Classical.choice`-backed shim plus a basepoint-independence lemma on degree-0 divisors.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
