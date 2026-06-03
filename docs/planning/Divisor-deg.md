# `Divisor.deg` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:63`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~15 minutes, ~5 LOC
**Blocked by:** `Divisor`, `Divisor.instAddCommGroup` (`Jacobians/RiemannSurface/LineBundle.lean:51,56`)

**Statement (verbatim):**
```lean
/-- The degree of a divisor: for a formal combination `D = ∑ n_P · P`,
`deg D := ∑ n_P`. An `AddMonoidHom` `Divisor X →+ ℤ`. -/
axiom Divisor.deg (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ ℤ
```

**Why it's an axiom right now:** The degree map sums coefficients: `(∑ n_P · P) ↦ ∑ n_P`. As a universal-property construction it is exactly the lift of the constant function `(_ : X) ↦ (1 : ℤ)` along `FreeAbelianGroup.lift`. It is axiomatized only because `Divisor X` is opaque (`Jacobians/RiemannSurface/LineBundle.lean:51`); once `Divisor X = FreeAbelianGroup X` lands, the degree is a one-line application of Mathlib's universal lift.

**Proof recipe**

1. Discharge prerequisites. Land [`Divisor.md`](Divisor.md) and [`Divisor-instAddCommGroup.md`](Divisor-instAddCommGroup.md). After they land, `Divisor X` reduces to `FreeAbelianGroup X` with its canonical `AddCommGroup` instance.

2. Cite Mathlib's free-group universal property. The key Mathlib decl is
   ```lean
   FreeAbelianGroup.lift : (X → A) ≃ (FreeAbelianGroup X →+ A)
   ```
   from `Mathlib.GroupTheory.FreeAbelianGroup`. Given any `f : X → A` with `A` an `AddCommGroup`, `FreeAbelianGroup.lift f : FreeAbelianGroup X →+ A` is the unique extension that agrees with `f` on generators. In particular, `FreeAbelianGroup.lift (fun _ : X => (1 : ℤ))` is precisely the degree map: it sends `FreeAbelianGroup.of P` (the generator at `P`) to `1`, hence sends `∑ n_P · P` to `∑ n_P`.

3. Replace the axiom with a `def`. In `Jacobians/RiemannSurface/LineBundle.lean:63`, replace
   ```lean
   axiom Divisor.deg (X : Type*) [...] : Divisor X →+ ℤ
   ```
   with
   ```lean
   noncomputable def Divisor.deg (X : Type*) [TopologicalSpace X] [T2Space X]
       [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ ℤ :=
     FreeAbelianGroup.lift (fun _ : X => (1 : ℤ))
   ```
   `noncomputable` because `FreeAbelianGroup.lift` is noncomputable in Mathlib. The signature is unchanged.

4. Optional: add an `@[simp]` lemma `Divisor.deg_of (P : X) : Divisor.deg X (FreeAbelianGroup.of P) = 1`. This is `FreeAbelianGroup.lift.of` from Mathlib. It will be useful for downstream consumers of `Divisor.deg`, e.g. `AX_RiemannRoch.lean` proofs of the degree equation. Not required to discharge the axiom.

5. Reference: Forster, *Lectures on Riemann Surfaces*, Ch. I §8, equation defining `deg D = ∑ n_P`; same formula in Mumford Vol I §II.2.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom Divisor.deg` (line 63) with the `noncomputable def` above. Optionally add a `@[simp]` lemma `Divisor.deg_of`.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms Jacobians.Axioms.Divisor.deg` no longer shows it as an axiom; it only mentions `Classical.choice` / propext / `Quot.sound` (Mathlib baseline).
- Any downstream theorem mentioning degrees (e.g. `AX_RiemannRoch`, `AX_AbelTheorem`) still typechecks; `#print axioms` for those no longer lists `Divisor.deg`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Divisor` was sealed `@[irreducible]` in step 1 of [`Divisor.md`](Divisor.md), `FreeAbelianGroup.lift` will not synthesize on `Divisor X` until unsealed; use `unseal Divisor in` or escalate to drop the seal.
- If a downstream consumer (e.g. `Jacobians/Axioms/RiemannRoch.lean`) was implicitly relying on `Divisor.deg` being opaque (so its `simp` set did not unfold), expect new `simp` lemmas to leak; if proofs break, the fix is to mark the new `def` `@[irreducible]` rather than the type. Escalate only if that workaround fails to restore downstream builds.