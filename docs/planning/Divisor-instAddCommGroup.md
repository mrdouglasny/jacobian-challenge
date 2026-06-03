# `Divisor.instAddCommGroup` — discharge recipe

**Location:** `Jacobians/RiemannSurface/LineBundle.lean:56`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~10 minutes, ~3 LOC
**Blocked by:** `Divisor` (`Jacobians/RiemannSurface/LineBundle.lean:51`)

**Statement (verbatim):**
```lean
/-- Divisors form an additive commutative group. -/
axiom Divisor.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : AddCommGroup (Divisor X)
attribute [instance] Divisor.instAddCommGroup
```

**Why it's an axiom right now:** Only because `Divisor X` is itself opaque (`Jacobians/RiemannSurface/LineBundle.lean:51`). Once `Divisor X` is realized as `FreeAbelianGroup X` (see [`Divisor.md`](Divisor.md)), the `AddCommGroup` structure is already supplied by Mathlib's `FreeAbelianGroup.addCommGroup` instance (in `Mathlib.GroupTheory.FreeAbelianGroup`). No mathematical content; it is purely instance synthesis.

**Proof recipe**

1. Discharge prerequisite. Land [`Divisor.md`](Divisor.md): replace `axiom Divisor X` (`LineBundle.lean:51`) with `def Divisor X := FreeAbelianGroup X`.

2. Replace the axiom with an instance. In `Jacobians/RiemannSurface/LineBundle.lean:56`, drop all the mathematically irrelevant topological and manifold typeclasses (which needlessly clutter inference caching; the group structure only depends on `X : Type*`). Replace the axiom block:
   ```lean
   axiom Divisor.instAddCommGroup {X : Type*} [...] : AddCommGroup (Divisor X)
   attribute [instance] Divisor.instAddCommGroup
   ```
   with:
   ```lean
   instance Divisor.instAddCommGroup {X : Type*} : AddCommGroup (Divisor X) :=
     inferInstanceAs (AddCommGroup (FreeAbelianGroup X))
   ```
   The `inferInstanceAs` succeeds because Mathlib's `FreeAbelianGroup.addCommGroup` (in `Mathlib.GroupTheory.FreeAbelianGroup`) is registered as an instance and `Divisor X` unfolds.

3. Handling potential API opacity: If `Divisor` is intended to be `@[irreducible]` to preserve API hygiene, `inferInstanceAs` will not see through the seal. The idiomatic Lean 4 solution is to define it as `def Divisor X := FreeAbelianGroup X deriving AddCommGroup` at `LineBundle.lean:51`, which auto-generates the instance before the irreducible attribute applies. If you strictly need the exact name `Divisor.instAddCommGroup` for downstream compatibility, define the manual `instance` block *before* applying the `@[irreducible]` attribute.

4. Drop the `attribute [instance]` line — the new declaration is already an `instance` (or auto-derived).

5. Confirm downstream synthesis. `Divisor.deg` (`LineBundle.lean:63`) takes a `Divisor X →+ ℤ`, which requires the new `AddCommGroup` instance on the source. `abelJacobiDiv` (`Jacobians/Axioms/AbelTheorem.lean:60`) similarly. Run `lake build` after the change; instance synthesis should pick up the new `instance` automatically.

**Files touched**
- `Jacobians/RiemannSurface/LineBundle.lean` — replace `axiom Divisor.instAddCommGroup` + the trailing `attribute [instance] Divisor.instAddCommGroup` (lines 56–59) with a single `instance Divisor.instAddCommGroup` definition (or remove it entirely if relying solely on `deriving AddCommGroup` at the definition site).

**Gemini critique addressed:**
- Removed the "junk binders" (manifold/topology typeclasses) from the proposed instance signature, as formal sums depend only on `X : Type*`.
- Removed pseudocode references to a non-existent Lean 4 `unseal` command, replacing them with idiomatic advice to use `deriving AddCommGroup` directly on the definition if an opaque API is desired.

**Acceptance**
- `lake build Jacobians.RiemannSurface.LineBundle` succeeds.
- `#print axioms Jacobians.Axioms.Divisor.instAddCommGroup` no longer shows it as an axiom.
- For any downstream theorem `T` that mentions `Divisor X` additively (e.g. `AX_AbelTheorem` via `abelJacobiDiv`), `#print axioms T` no longer lists `Divisor.instAddCommGroup`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Divisor` ends up being marked `@[irreducible]` and the instance synthesis fails, escalate only if applying `deriving AddCommGroup` to the `Divisor` definition also fails.
- If a future redesign turns `Divisor X` into a quotient or a sigma-type rather than `FreeAbelianGroup X`, this recipe needs to be rewritten with the actual `AddCommGroup` construction; escalate before changing the encoding.

---
**Vetting trail.** Critique: `_vetting/Divisor-instAddCommGroup.md`. Verdict: revise. Revised: 2026-06-03.