# `AX_HyperellipticForm_polynomial_decomposition` — discharge recipe

**Location:** `Jacobians/Axioms/HyperellipticLiouville.lean:215`
**Route:** genuine-textbook &nbsp;&nbsp; **Effort:** 5 &nbsp;&nbsp; **Est:** ~1.5–3 focused weeks, ~600–900 LOC in 1 new file
**Blocked by:** none (L2 of the Liouville hierarchy; sub-step 4 already has the Mathlib-grade lemma in-tree)

**Statement (verbatim):**
```lean
axiom AX_HyperellipticForm_polynomial_decomposition
    {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      ∀ (a : HyperellipticAffine H) (hpY : a ∈ HyperellipticAffine.smoothLocusY H)
        (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
        {z : ℂ}
        (hz : z ∈ ((HyperellipticAffine.affineChartProjX a hpY) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target),
        form.coeff q z =
          g.eval z /
            (HyperellipticAffine.squareLocalHomeomorph (H := H) a hpY).symm
              (H.f.eval z)
```

**Why it's an axiom right now:** The chart-local coefficient `form.coeff q z` on a projX chart at a `smoothLocusY` representative is the function `ω / dx` read off in the `x`-coordinate. Because `dx` vanishes to first order at the branch points (`y = 0`, where `f(x) = 0`), `ω / dx` has *simple poles* at the branch points even when `ω` is holomorphic. The task is to identify this chart-local coefficient with `g(x) / y(x)` for a polynomial `g` of degree `< N/2 − 1` (where `N := H.f.natDegree`). The docstring (`HyperellipticLiouville.lean:174–214`) sketches the standard derivation; sub-step 4 — "entire + polynomial growth ⇒ polynomial" — is already discharged by `differentiable_eq_polynomial_of_growth` (`Jacobians/GeneralResults/EntireGrowth.lean:36`). The remaining sub-steps are project-specific complex analysis that Forster *Lectures on Riemann Surfaces* §13–14 ("differentials on hyperelliptic curves" / "differentials of the first kind") packages as a textbook chunk.

**Gemini critique addressed.** The previous recipe decomposed the wrong function — it asked the formalizer to prove `b ∈ ℂ[x]` for `form.coeff = a(x) + y·b(x)`, but that ansatz is *false* for `ω / dx`: the correct ansatz is `ω / dx = a(x) + g(x) / y` where `g(x) := y · (the antisymmetric part)` is the entire-then-polynomial object (and `a(x) ≡ 0` falls out from holomorphy at infinity). The previous recipe also pulled in `FieldTheory.RatFunc` and `RingTheory.AdjoinRoot` to set up the function field `ℂ(x)[y]/(y²−f)` — this abstract algebra is unnecessary; the decomposition is a pointwise symmetric/antisymmetric split with respect to the hyperelliptic involution `(x, y) ↦ (x, −y)` (`HyperellipticAffine.invol`, `Involution.lean:26`), which acts trivially on `x` and so commutes with the projX chart trivially. We rewrite the recipe accordingly: elementary pointwise symmetry over the two sheets, Riemann removable-singularities at the branch divisor (Forster §13.1, Satz on "Hebbarkeit"), and a growth bound on the infinity chart (Forster §14, "differentials of the first kind" / dimension count for `Ω¹` on a hyperelliptic curve). This is the route Gemini recommends and it eliminates all `RatFunc` / `AdjoinRoot` infrastructure.

**Proof recipe**

The single-file plan: `Jacobians/RiemannSurface/HyperellipticPointwiseSymmetry.lean` (new, ~600–900 LOC).

1. **Sub-step 1 — pointwise symmetric/antisymmetric split** (Forster §13.1, observation preceding the Satz on hyperelliptic differentials; Mumford *Tata Lectures I* Ch. IIIa 1A "the canonical involution"). The hyperelliptic involution `σ : (x, y) ↦ (x, −y)` is `HyperellipticAffine.invol` (`Jacobians/ProjectiveCurve/Hyperelliptic/Involution.lean:26`); it sends `smoothLocusY` into itself (`invol_mem_smoothLocusY`, `Involution.lean:122`). For `q : HyperellipticEvenProj H` with `Quotient.out q = Sum.inl a` and `a ∈ smoothLocusY`, let `q⁻ : HyperellipticEvenProj H` be the σ-image of `q` (built from `hyperellipticEvenInvol`, `Involution.lean:87`). Both `q` and `q⁻` lie over the same `x`-value via the projX chart. Define (locally on the projX chart target around `a`)

   ```
   a(z) := (form.coeff q z + form.coeff q⁻ z) / 2
   g̃(z) := (form.coeff q z − form.coeff q⁻ z) / 2 · (squareLocalHomeomorph a hpY).symm (H.f.eval z)
   ```

   directly as `ℂ → ℂ` functions on `(affineChartProjX a hpY).target`. No `RatFunc`, no `AdjoinRoot`. The factor of `y(z) := (squareLocalHomeomorph a hpY).symm (H.f.eval z)` (`AffineForm.lean:45`, branch chosen by IFT) absorbs the sign-change so `g̃` is the "polynomial half" we want. By construction, `form.coeff q z = a(z) + g̃(z) / y(z)`.

2. **Sub-step 2 — Riemann removable-singularities at the branch divisor** (Forster §13.1, "Hebbarkeitssatz"; the regular-extension argument across the Weierstrass points). Show `a` and `g̃` extend to entire `ℂ → ℂ` functions:
   - On `{z | H.f.eval z ≠ 0}` (the locus where both `(z, +y)` and `(z, −y)` define affine points in `smoothLocusY`), holomorphy of `form` (as `HolomorphicOneForm` on `HyperellipticEvenProj H`) implies `a` and `g̃` are holomorphic — chart-overlap argument via the cocycle `hyperellipticEvenCoeff_cocycle_inl_inl` (`EvenForm.lean:272`) between `affineChartProjX a hpY` and `affineChartProjX a.invol hpY'` (using `invol_mem_smoothLocusY`).
   - At each branch root `α` (`H.f.eval α = 0`, hence `(α, 0)` lies in `smoothLocusX \ smoothLocusY` by `eval_derivative_ne_zero_of_eval_eq_zero`, `OddAtlas/AffineChart.lean:52`), switch to the projY chart `affineChartProjY` (`OddAtlas/AffineChart.lean:291`), in which the local coordinate is `y` and `form.coeff` is regular by holomorphy. The chart-overlap cocycle (the projX × projY case, `AffineForm.lean:410` "symmetric") shows that `form.coeff q z` on the projX side has at worst a *simple pole* at `z = α` whose residues on the two sheets are *opposite in sign*. Hence `a(z) = (h₊ + h₋)/2` is *bounded* near `α` (the simple poles cancel) and `g̃(z) = y · (h₊ − h₋)/2` is *bounded* near `α` (the factor `y` vanishes to first order, killing the simple pole). By Riemann's removable-singularity theorem (Mathlib: `Complex.differentiableOn_update_limUnder_of_isLittleO` and `Complex.removable_singularity` in `Analysis.Complex.RemovableSingularity`), both extend holomorphically to all of `ℂ`.

3. **Sub-step 3 — growth at infinity** (Forster §14, dimension-count discussion preceding the genus formula for hyperelliptic curves; the analysis of `dx/y` and `xᵏ dx/y` as the basis of `H⁰(Ω¹)`). Use the cross-summand cocycle `hyperellipticEvenCoeff_cocycle_inl_inr` (`EvenForm.lean:2119`, real proof) to pull `form` back to the infinity chart `(t, u)` via `u = 1/x`, `y ~ x^{N/2}` where `N := H.f.natDegree`. Holomorphy of `form` at the infinity-chart fibre forces, after reading off the leading behaviour of `ω / dx = a(x) + g̃(x) / y`:
   - `a(x) = O(|x|⁻²)` as `|x| → ∞` — since `a` is entire (sub-step 2) and decays, Liouville (or `differentiable_eq_polynomial_of_growth` at degree `0` with the boundedness fact) forces `a ≡ 0`.
   - `g̃(x) / y(x) = O(|x|⁻²)`; since `|y(x)| ~ |x|^{N/2}`, this gives `g̃(x) = O(|x|^{N/2 − 2})`. So the entire `g̃` has polynomial growth of exponent `< N/2 − 1` (the strict inequality is what the axiom statement demands).

4. **Sub-step 4 — growth ⇒ polynomial** *(already in-tree)*. Apply `differentiable_eq_polynomial_of_growth (n := N/2 − 2)` (`Jacobians/GeneralResults/EntireGrowth.lean:36`) to the entire `g̃` from sub-steps 2+3 to extract `g : Polynomial ℂ` with `g.natDegree ≤ N/2 − 2`, i.e. `g.natDegree < N/2 − 1`, and `g̃ z = g.eval z` pointwise. Substituting `a ≡ 0` back into sub-step 1 gives

   ```
   form.coeff q z = g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z)
   ```

   which is precisely the existential witness for the axiom.

5. **Final assembly** in `Jacobians/Axioms/HyperellipticLiouville.lean`: rename `axiom AX_HyperellipticForm_polynomial_decomposition` to `theorem` and apply the lemmas of the new file. Body sketch:
   ```lean
   intro form
   -- sub-step 1+2: pointwise σ-split extends to entire `a, g̃ : ℂ → ℂ`
   obtain ⟨a_fn, g_fn, ha_diff, hg_diff, hsplit⟩ :=
     hyperelliptic_pointwise_decomposition form                 -- new lemma
   -- sub-step 3a: `a_fn ≡ 0` from infinity-chart decay
   have ha0 : ∀ z, a_fn z = 0 :=
     hyperelliptic_symmetric_part_vanishes form a_fn g_fn ha_diff hsplit
   -- sub-step 3b: `g_fn` has growth `< N/2 − 1`
   obtain ⟨C, hC⟩ :=
     hyperelliptic_antisymmetric_growth_bound form a_fn g_fn hg_diff hsplit
   -- sub-step 4: extract polynomial
   obtain ⟨g, hgDeg, hgEval⟩ :=
     differentiable_eq_polynomial_of_growth (H.f.natDegree / 2 - 2) g_fn hg_diff C hC
   refine ⟨g, by omega, ?_⟩
   intro a hpY q hQ z hz
   -- chart-local readout: substitute `a_fn = 0` and `g_fn = g.eval`
   rw [hsplit a hpY q hQ hz, ha0 z, zero_add, hgEval z]
   ```

**Next discrete deliverable:** Sub-step 1 (the σ-split definitions + the algebraic identity `form.coeff q z = a(z) + g̃(z)/y(z)`) is the most self-contained and unblocks both sub-step 2 (regularity statement needs `a`, `g̃` named) and sub-step 3 (growth statement also needs them named). Land it first in `Jacobians/RiemannSurface/HyperellipticPointwiseSymmetry.lean` with `sorry` on the regularity and growth lemmas; iterate.

**Files touched**
- `Jacobians/Axioms/HyperellipticLiouville.lean` — replace `axiom AX_HyperellipticForm_polynomial_decomposition` (line 215) with the assembled `theorem`.
- `Jacobians/RiemannSurface/HyperellipticPointwiseSymmetry.lean` — **new**, sub-steps 1+2+3 (~600–900 LOC).
- `Jacobians.lean` — add the new module to the umbrella.

**Acceptance**
- `lake build Jacobians.Axioms.HyperellipticLiouville` succeeds.
- `#print axioms genus_HyperellipticEven_le` (`HyperellipticLiouville.lean:279`) no longer lists `AX_HyperellipticForm_polynomial_decomposition` (it still lists L3 unless that one is also discharged in the same pass).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the projY chart at branch points (`OddAtlas/AffineChart.lean:291`) does not give "simple pole, opposite-sign residues" cleanly because of a `smoothLocusX`-vs-`smoothLocusY` boundary convention (`OddAtlas/AffineChart.lean:41,47`) that swaps which chart sees the branch — escalate; the bounded-near-`α` claim of sub-step 2 may need an auxiliary cocycle lemma.
- If `squareLocalHomeomorph.symm` (`AffineForm.lean:45`) does not interact cleanly with the σ-pair (i.e. the IFT-derived branch on `q` and `q⁻` is not provably `±` of one another locally), escalate: the pointwise split in sub-step 1 fails to be globally well-defined on the chart target until that sign relation is stated. (Sketch fix: a one-line lemma `squareLocalHomeomorph_invol_symm` derivable from `invol_invol` plus the IFT uniqueness clause.)
- If the infinity-chart growth bound in sub-step 3 cannot be stated without a "limit at `u = 0`" companion to `hyperellipticEvenCoeff_cocycle_inl_inr` (`EvenForm.lean:2119`), escalate to a recipe extension before forcing the bound through.

---
**Vetting trail.** Critique: `_vetting/AX_HyperellipticForm_polynomial_decomposition.md`. Verdict: reject. Revised: 2026-06-03.
