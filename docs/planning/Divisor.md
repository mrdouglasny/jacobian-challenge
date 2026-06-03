# `Divisor` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:51`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** < 15 minutes, ~5 LOC
**Blocked by:** `Divisor.instAddCommGroup` (`Jacobians/RiemannSurface/LineBundle.lean:56`)

**Statement (verbatim):**
```lean
/-- **Opaque axiom type.** The group of divisors on a compact Riemann
surface `X`. Classically: formal `ℤ`-combinations of points of `X`.
Forms an `AddCommGroup` via the declared instance below. -/
axiom Divisor (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type
```

**Why it's an axiom right now:** This is pure bookkeeping: divisors are classically formal `ℤ`-linear combinations of points, i.e. the free abelian group on the underlying set. The file docstring (`Jacobians/RiemannSurface/LineBundle.lean:20`) already names the planned encoding (`FreeAbelianGroup X`). It is left as `axiom` only because the file groups all line-bundle stubs together and `LineBundle`/`H¹` need genuine sheaf-cohomology infrastructure; `Divisor` itself is trivially dischargeable today via Mathlib's `FreeAbelianGroup`.

**Proof recipe**

1. Pick the encoding. Use Mathlib's `FreeAbelianGroup` (declared in `Mathlib.GroupTheory.FreeAbelianGroup`, providing `FreeAbelianGroup : Type u → Type u` together with an `AddCommGroup` instance and the universal `FreeAbelianGroup.lift : (X → A) →+ (FreeAbelianGroup X →+ A)` for any `AddCommGroup A`). This is exactly the planned encoding from the file's header comment at `Jacobians/RiemannSurface/LineBundle.lean:20`.

2. Replace the axiom with an `abbrev` and suppress unused variable linting. In `Jacobians/RiemannSurface/LineBundle.lean:51`, replace:
   ```lean
   axiom Divisor (X : Type*) [...] : Type
   ```
   with:
   ```lean
   abbrev Divisor (X : Type u) [_ : TopologicalSpace X] [_ : T2Space X]
       [_ : CompactSpace X] [_ : ConnectedSpace X] [_ : ChartedSpace ℂ X]
       [_ : IsManifold 𝓘(ℂ) ω X] : Type u := FreeAbelianGroup X
   ```
   *Note 1:* Using `abbrev` instead of `def` is strictly required here so Lean 4's typeclass resolution (e.g., finding `AddCommGroup`) fires transparently through the alias without additional boilerplate.
   *Note 2:* Because the RHS is purely algebraic (`FreeAbelianGroup X`), the geometric typeclasses passed to `Divisor` are unused. You must bind them with `_ :` to avoid Lean 4 linter errors.

3. Universe sanity. `Divisor X : Type` in the current axiom signature; `FreeAbelianGroup X : Type u` if `X : Type u`. The `Type` (= `Type 0`) return in the axiom is too strict — bump to `Type u` as shown above. Check that all downstream consumers (`PrincipalDivisors`, `LineBundle`, `H0`, `H1`, `canonicalDivisor`, `Jacobians/Axioms/AbelTheorem.lean:60` `abelJacobiDiv`) still typecheck — they should, since none of them constrain `Divisor X` to `Type 0`.

4. Discharge the companion recipes. With this `abbrev` in place:
   - `Divisor.instAddCommGroup` (`Jacobians/RiemannSurface/LineBundle.lean:56`) becomes `inferInstance` — see `Divisor-instAddCommGroup.md`.
   - `Divisor.deg` (`Jacobians/RiemannSurface/LineBundle.lean:63`) becomes `FreeAbelianGroup.lift (fun _ => (1 : ℤ))` — see `Divisor-deg.md`.
   - `abelJacobiDiv` (`Jacobians/Axioms/AbelTheorem.lean:60`) becomes a one-line `FreeAbelianGroup.lift` — see `abelJacobiDiv.md`.

5. Reference: Forster, *Lectures on Riemann Surfaces*, Ch. I §8 (divisors as the free abelian group on points, written `D = ∑ n_P · P` with `n_P = 0` for all but finitely many `P`); Mumford, *Curves and their Jacobians* / *Abelian Varieties* Vol I §II.2 for the algebro-geometric variant.

**Gemini critique addressed:**
- Reclassified route from `provable-from-other-axioms` to `mathlib-now`, as this is a direct Mathlib definition replacement.
- Recalibrated effort radically downwards from 4 (2–3 days) to 1 (< 15 minutes).
- Changed the prescribed syntax from `def` to `abbrev` to properly leverage Lean 4 typeclass transparency, avoiding manual instance forwarding.
- Added explicit `_ :` binders in the replacement signature to silence the unused variables linter on the purely topological/manifold arguments.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom Divisor` (line 51) with `abbrev Divisor (X) [...] := FreeAbelianGroup X`. Add `import Mathlib.GroupTheory.FreeAbelianGroup` at the top if it is not already pulled in transitively via `Jacobians.RiemannSurface.Genus`.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds without linter warnings.
- `#print axioms Jacobians.Axioms.Divisor` returns nothing project-local (`Divisor` is now an `abbrev`); downstream `#print axioms AX_AbelTheorem` no longer lists `Divisor`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If raising the return universe from `Type` to `Type u` cascades into universe-polymorphism errors at `abelJacobiDiv` or in the `AbelJacobiMap.lean` quotient constructions (`Jacobians/Axioms/AbelJacobiMap.lean:317–460` uses `ULift` heavily), escalate: the fix may require coordinated universe annotations across `Divisor` / `LineBundle` / `Jacobian`.
- If a downstream file previously pattern-matched on `Divisor X` as an opaque type and breaks due to `abbrev` revealing the `FreeAbelianGroup` structure, escalate to revert to `def` and manually implement all `AddCommGroup` boilerplate instances.

---
**Vetting trail.** Critique: `_vetting/Divisor.md`. Verdict: revise. Revised: 2026-06-03.