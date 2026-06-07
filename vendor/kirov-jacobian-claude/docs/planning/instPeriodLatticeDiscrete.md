# `instPeriodLatticeDiscrete` — discharge recipe

**Location:** `Jacobians/Axioms/PeriodLattice.lean:77`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 4 &nbsp;&nbsp; **Est:** ~3–5 focused days, ~200–300 LOC
**Blocked by:** `AX_RiemannBilinear`, `AX_PeriodLattice`

**Statement (verbatim):**
```lean
/-- **Axiom (NOT VERIFIED).** In basis coordinates, the period image carries
the discrete topology.

This is one half of the data required by Mathlib's `IsZLattice`-based
`ComplexTorus` API. It should eventually be derived from
`AX_RiemannBilinear`, since a full lattice in a finite-dimensional real
vector space is automatically discrete. -/
axiom instPeriodLatticeDiscrete (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (periodLatticeInBasis X x₀ b)
```

**Why it's an axiom right now:** The file's docstring (lines 73–76) records the discharge plan: once `AX_RiemannBilinear` provides a symplectic basis with α-normalized period identity + symmetric `τ` with `Im τ` positive definite, the period image in `Fin (genus X) → ℂ` is the ℤ-span of `2g` ℝ-linearly independent column vectors of `[I_g | τ]`, hence discrete by Mathlib's `ZSpan` discreteness instance. The axiom is load-bearing only as a typeclass — `ComplexTorus` (`Jacobians/AbelianVariety/ComplexTorus.lean:11,20`) requires both `[DiscreteTopology L]` and `[IsZLattice ℝ L]`, and `JacobianAmbient` at `Jacobians/Jacobian/Construction.lean:135–136` instantiates them on `periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)`.

**Gemini critique addressed:**
- **Effort increased:** Re-calibrated to Effort 4 (~3–5 days, ~200–300 LOC) to account for the heavy matrix algebra involved in splitting real and imaginary parts.
- **Topology correction:** Eliminated the fabricated `DiscreteTopology.of_continuous_injective` lemma. Now correctly constructing `Homeomorph`s and relying on `Embedding.discreteTopology` to transport discreteness.
- **Submodule syntax fixed:** Replaced invalid `M.toLin'.range.map` syntax with `Submodule.map (M.toLin'.restrictScalars ℤ)`.
- **Linear independence proof fleshed out:** Added concrete steps detailing how `Complex.im` isolates the coefficients of `τ` and leverages `imPosDef`'s injectivity to conclude $\mathbb{R}$-linear independence.
- **Typeclass transfer fixed:** Replaced the unsafe submodule equality rewrite plan with a robust `LinearEquiv` (promoted to `Homeomorph`) between the topological spans.

**Proof recipe**

This is the discreteness half of the period-lattice theorem (Mumford, *Tata Lectures on Theta I*, Ch. II §2; Griffiths–Harris, Ch. 2 §2). 

1. **Obtain the symplectic data from `AX_RiemannBilinear`.** Cite
   `AX_RiemannBilinear` at `Jacobians/Axioms/RiemannBilinear.lean:69` to get
   `⟨b₀, cω, τ, hA, hτ⟩` with
   * `b₀ : AnalyticCycleBasis X x₀` (a ℤ-basis of `H1 X x₀` indexed by `Fin (2 * genus X)`, supplied by `b₀.isBasis` at `Jacobians/Axioms/AnalyticCycleBasis.lean:230`),
   * `cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` α-normalized,
   * `τ : SiegelUpperHalfSpace (genus X)` (constructor at `Jacobians/AbelianVariety/Siegel.lean:40`; `imPosDef` at line 54).

2. **Compute `periodMapInBasis X x₀ cω` on the symplectic basis.** Using
   `periodMapInBasis` at `Jacobians/Axioms/PeriodLattice.lean:53`, evaluate on
   `b₀.isBasis (αEmbed i)` (line 198 of `AnalyticCycleBasis.lean`) and
   `b₀.isBasis (βEmbed i)` (line 205). By `hA` and `hτ`:
   * `periodMapInBasis X x₀ cω (b₀.isBasis (αEmbed i)) = Pi.single i 1` (standard basis vector `e_i ∈ Fin g → ℂ`),
   * `periodMapInBasis X x₀ cω (b₀.isBasis (βEmbed i)) = τ.val i` (the `i`-th row of `τ`, viewed as `Fin g → ℂ`).

3. **Change of basis from `cω` to `b`.** The given basis `b` differs from `cω`
   by some invertible matrix `M : Matrix (Fin g) (Fin g) ℂ`. Coordinate
   transport along `b.dualBasis.equivFun` vs `cω.dualBasis.equivFun` gives
   `periodMapInBasis X x₀ b = M.toLin' ∘ₗ periodMapInBasis X x₀ cω`. So
   pushing the ℤ-span forward requires `Submodule.map`:
   `periodLatticeInBasis X x₀ b = Submodule.map (M.toLin'.restrictScalars ℤ) (periodLatticeInBasis X x₀ cω)`.

4. **Prove the ℝ-linear independence of the period vectors.**
   Concatenate the columns of `I_g` and the rows of `τ` into a single
   indexed family `v : Fin (2 * genus X) → (Fin (genus X) → ℂ)` using the
   `αEmbed`/`βEmbed` index splitting. To prove `v` is ℝ-linearly independent:
   assume a real linear relation $\sum c_i e_i + \sum d_j \tau_j = 0$ over $\mathbb{R}$.
   Apply `Complex.im` to both sides. Since the $e_i$ vectors are real, they vanish,
   yielding $\sum d_j \text{Im}(\tau_j) = 0$. Because $\text{Im}(\tau)$ is positive
   definite (`imPosDef`), its associated real linear map is injective, forcing all
   $d_j = 0$. Substituting back gives $\sum c_i e_i = 0$, forcing all $c_i = 0$.
   With the real dimension of `Fin (genus X) → ℂ` being `2 * genus X` (via
   `Complex.finrank_real_complex`, used at `Jacobians/ProjectiveCurve/Elliptic.lean:63`), 
   package `v` as `Module.Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ)` using
   `basisOfLinearIndependentOfCardEqFinrank` (as in `Jacobians/ProjectiveCurve/Elliptic.lean:62–63`).

5. **Build a `Homeomorph` to the period lattice.** From step 2, the ℤ-linear range of
   `periodMapInBasis X x₀ cω` equals the ℤ-span of `v`'s image. Construct a
   `LinearEquiv` over ℤ between Mathlib's `span ℤ (Set.range v)` and
   `periodLatticeInBasis X x₀ cω`. Since the ambient space is finite-dimensional
   and the map is continuous, this promotes to a `Homeomorph`.

6. **Transport discreteness to `cω`.** Invoke Mathlib's `DiscreteTopology` instance 
   for ℤ-spans of an ℝ-basis: `Mathlib.Algebra.Module.ZLattice.Basic` line 320 provides
   `instance [Finite ι] : DiscreteTopology (span ℤ (Set.range b))`. 
   Use `Embedding.discreteTopology` (via the `Homeomorph` from Step 5, which is an `Embedding`)
   to safely transport this instance and obtain `DiscreteTopology (periodLatticeInBasis X x₀ cω)`
   without running into motive type errors from submodule equality rewrites.

7. **Transport along the basis change of step 3.** The invertible change-of-basis matrix $M$
   gives a `Matrix.toContinuousLinearEquiv`, which provides a `Homeomorph` (and thus an `Embedding`)
   on the ambient vector space. Restrict this to the submodules to build a `Homeomorph`
   between `periodLatticeInBasis X x₀ cω` and `periodLatticeInBasis X x₀ b`. 
   Again use `Embedding.discreteTopology` to conclude `DiscreteTopology (periodLatticeInBasis X x₀ b)`.

8. **Replace `axiom` with `theorem` in
   `Jacobians/Axioms/PeriodLattice.lean:77`** and keep the
   `attribute [instance]` line below it (line 83) so downstream files
   continue to find the instance automatically.

**Implementation note:** steps 1–5 are the same construction needed by
`AX_PeriodLattice` (the ℝ-basis `v` of step 4 is the witness for
`IsZLattice ℝ`). Land them as shared helpers in a single supporting file
(`Jacobians/RiemannSurface/PeriodBasis.lean`, new), and both axioms become
short corollaries.

**Files touched**
- `Jacobians/Axioms/PeriodLattice.lean` — replace `axiom instPeriodLatticeDiscrete`
  (line 77) with `theorem` / `instance`; preserve `attribute [instance]` on
  line 83.
- `Jacobians/RiemannSurface/PeriodBasis.lean` *(new)* — shared helpers:
  the explicit matrix-vector algebra for the ℝ-basis `v` (step 4), the `Homeomorph`
  identifications (steps 5 and 7).

**Acceptance**
- `lake build Jacobians.Axioms.PeriodLattice` succeeds.
- `#print axioms Jacobians.Jacobian.Construction.JacobianAmbient` (the closest
  consumer, at `Jacobians/Jacobian/Construction.lean:132–136`) no longer lists
  `instPeriodLatticeDiscrete`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS;
  axiom count drops by 1.

**Risk / escalation triggers**
- The algebraic manipulations splitting complex matrix-vector products into real/imaginary parts (Step 4) can be highly tedious in Lean; if missing Mathlib lemmas for `Complex.im` interacting with `Matrix.mulVec` cause a severe block, escalate for a tactical split.
- If `AX_RiemannBilinear`'s α-normalization (its `cω` basis) is non-unique or
  its existential is only at `Nonempty` level, but `instPeriodLatticeDiscrete`
  needs the *given* basis `b`, the basis-change transport (step 7) is load-bearing.
- If Mathlib's `ZSpan.instDiscreteTopology` (line 320 of `ZLattice/Basic.lean`)
  in v4.28 does not pick up `Submodule ℤ (Fin (genus X) → ℂ)` because the
  norm-instance on `Fin g → ℂ` is the product norm rather than the ℝ-norm
  Mathlib expects, escalate — may need a `letI : NormedSpace ℝ (Fin g → ℂ)`
  alias or a `Complex.reSpace` interposition.

---
**Vetting trail.** Critique: `_vetting/instPeriodLatticeDiscrete.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
