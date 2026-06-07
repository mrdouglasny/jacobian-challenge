# Abel's theorem, ⊇ direction — the Liouville / symmetric-product route

*2026-06-07. Recommended route for the `⊇` half of `AX_AbelTheorem`
(`PrincipalDivisors X ≤ (abelJacobiDiv X).ker`), via Gemini deep-think
(brief: [`docs/deep-think-residue-theorem-route.md`](../deep-think-residue-theorem-route.md)),
with Mathlib lemma names verified against our pin. Supersedes the Forster
residue + period-normalization `⊇` route in
[`AX_AbelTheorem.md`](AX_AbelTheorem.md).*

## TL;DR

**Do not build the residue theorem or manifold Stokes to prove Abel `⊇`.**
The residue theorem requires either fundamental-polygon side-pairings or
Stokes-with-boundary on a quotient manifold — both 3000+ LOC of topological
infrastructure Mathlib does not have. Instead use the classical "the Jacobi map
is constant on a rational pencil" argument, which trades 2D topology for 1D
complex analysis and reuses our strongest landed asset, `weightedFiberConservation`.

## The mathematics

Let `f : X → ℙ¹` be a non-constant meromorphic function with `div f = D`
(degree 0). Define
```
Φ : ℙ¹ → Jacobian X = ℂ^g / Λ,    Φ(y) = abelJacobiDiv X (f⁻¹(y))
                                       = ∑_{x ∈ f⁻¹(y)} ∫_{x₀}^{x} ω   (mod Λ)
```
where the sum is over the fiber divisor (with multiplicity) and `ω` ranges over
the `jacobianBasis X` of **holomorphic** 1-forms.

1. **Φ is well-defined.** Each fiber `f⁻¹(y)` is a finite divisor of constant
   degree `d = deg f` (our `weightedFiberConservation_of_contMDiff` +
   `AX_BranchLocus`, both theorems).
2. **Φ is holomorphic off the branch locus `B`.** Away from `B`, the `d` roots
   `xᵢ(y)` are local holomorphic functions of `y` (Mathlib IFT,
   `HasStrictFDerivAt.implicitFunction`), and each `∫_{x₀}^{xᵢ(y)} ω` is
   holomorphic in the upper endpoint (our `developingValue` /
   `canonicalArcIntegral` endpoint-analyticity, the same fact behind the
   discharged `AX_ofCurve_contMDiff` route).
3. **Φ extends holomorphically across `B` (removable).** At a branch point the
   sheets `xᵢ(y)` collide and individually acquire fractional-power behaviour,
   but the **symmetric** sum `∑ᵢ ∫ω` stays **bounded** — crucially because `ω`
   is *holomorphic* (no poles), so each integral is bounded as `y → b`. Bounded +
   holomorphic on a punctured neighbourhood ⇒ removable
   (`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`; boundedness
   via `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under`).
   *This is the step that dodges the residue theorem: holomorphic ω ⇒ no
   residues ⇒ pure removable-singularity, no contour integration.*
4. **Liouville ⇒ Φ constant.** `Φ : ℙ¹ → ℂ^g/Λ`; since `ℙ¹` is simply connected
   it lifts to `Φ̃ : ℙ¹ → ℂ^g` (covering `ℂ^g → ℂ^g/Λ`, our Kirov
   `ZLatticeQuotient` local-homeo API). `ℙ¹` compact ⇒ `Φ̃(ℙ¹)` bounded ⇒ `Φ̃`
   constant (`Differentiable.apply_eq_apply_of_bounded` /
   `Differentiable.exists_eq_const_of_bounded`).
5. **Conclude.** `Φ(0) = Φ(∞)`, i.e. `AJ(zeros) = AJ(poles)`, so
   `abelJacobiDiv X (div f) = AJ(zeros) − AJ(poles) = 0`. Hence
   `D ∈ ker(abelJacobiDiv X)`.

## Mathlib-name verification (against our pin, 2026-06-07)

| Need | Lemma | Status |
|------|-------|--------|
| Liouville (bounded entire ⇒ const) | `Differentiable.apply_eq_apply_of_bounded`, `Differentiable.exists_eq_const_of_bounded`, `Differentiable.exists_const_forall_eq_of_bounded` | ✅ present |
| Removable singularity | `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` | ✅ present |
| Boundedness ⇒ limit at puncture | `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under` | ✅ present |
| Local holomorphic roots | `HasStrictFDerivAt.implicitFunction` (`implicitFunction*` API) | ✅ present |
| Fiber degree constant | `weightedFiberConservation_of_contMDiff` (Wallace) + `AX_BranchLocus` (theorem) | ✅ ours |
| Endpoint-analyticity of `∫ω` | `developingValue` / `canonicalArcIntegral` (HI workstream) | ✅ ours |
| Torus covering lift | Kirov `ZLatticeQuotient` `isLocalHomeomorph_mk` | ✅ ours |
| **Residue API** (`Complex.residue`, `circleIntegral_eq_two_pi_I_mul_residue`) | — | ❌ **not found in our cache; Gemini's claim looks hallucinated. NOT NEEDED on this route.** |

## Concrete Lean decomposition (~800–1200 LOC, no Stokes)

| File | Proves | Reuses |
|------|--------|--------|
| `ArgumentPrinciple.lean` (~150) | `∑_p ord_p(f) = 0` (fiber degree at `0` = at `∞`) | `weightedFiberConservation`, `AX_BranchLocus` |
| `FiberAJMap.lean` (~250) | `Φ(y) := ∑_{x∈f⁻¹(y)} AJ(x)` well-defined in `Jacobian X` | `MeromorphicFunctionField`, `BranchedCover`, `canonicalArcIntegral`/periods |
| `FiberAJHolomorphic.lean` (~300) | `Φ` holomorphic on all of `ℙ¹` (IFT off `B`; removable across `B`) | IFT, removable-sing, `HolomorphicOneForm` API |
| `AbelKernel.lean` (~200) | `PrincipalDivisors X ≤ (abelJacobiDiv X).ker` (the `⊇` half) | Liouville, `ℙ¹` simply-connected lift |

**Single load-bearing lemma:** step 3 (symmetric-sum boundedness at branch points
⇒ removable). Everything else is assembly over existing infra.

## Scope / honest limits

- **This is the `⊇` direction only.** The `⊆` direction (Jacobi inversion:
  `ker ∩ deg-0 ⊆ PrincipalDivisors`) still needs `AX_RiemannRoch` +
  `AX_SerreDuality` (both still axioms) to build the third-kind differential.
  Unchanged by this route.
- **The general residue theorem is deferred, not solved.** If a later target
  (e.g. Serre duality) needs `∑res ω = 0` for *meromorphic* ω, the cheap route is
  still open. Gemini's ranking: reject fundamental-polygon (a) and
  partition-of-unity (b); the argument-principle bootstrap (c) only reaches
  *integer* residues (`df/f`) and does **not** span general ω; the ℙ¹-pushforward
  route (d) is cleanest but reintroduces the hard `pushforwardOneForm` trace.
- **picard-lefschetz repo as a Stokes substitute.** `~/Documents/GitHub/picard-lefschetz`
  has homotopy-invariant contour integration of holomorphic `n`-forms on
  real-`n`-dim contours in `ℂ^n` + `Stokes.lean` (structural closedness `∂ω=0`).
  This is **flat-`ℂ^n` / chain-contour** machinery — it can substitute for the
  *local* pieces of a general residue theorem (in-chart contour deformation, the
  puncture-limit Gemini misnamed) but not the global 2-cell gluing. Hold in
  reserve for the general residue theorem; **not needed for Abel `⊇`.**

## Vetting trail
Route proposed by Gemini deep-think 2026-06-07 (brief in
`docs/deep-think-residue-theorem-route.md`); Mathlib names independently
verified against `.lake/packages/mathlib` at our pin (residue API claim
falsified, route-critical names confirmed). Math is the standard Abel-theorem
proof via the Jacobi map being constant on a rational pencil (Griffiths–Harris
Ch. 2; Mumford, *Curves and their Jacobians*).
