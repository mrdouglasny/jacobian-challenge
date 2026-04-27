/-
# Unified coefficient family on `HyperellipticEvenProj H`

Combines the affine bundle (`AffineForm.lean`) and the affine-infinity
bundle (`AffineInfinityForm.lean`) into a coefficient family on the
quotient `HyperellipticEvenProj H`. Two of the three submodule
predicates -- `IsHolomorphicOneFormCoeff` and `IsZeroOffChartTarget` --
follow directly from the summand bundles via case-split on
`Quotient.out`.

The third predicate -- `SatisfiesCotangentCocycle` -- splits into:
* same-summand cases: handled by the within-summand cocycle bundles
  from S3/S4.
* cross-summand cases (`Sum.inl × Sum.inr` and symmetric): the
  Möbius-transition gluing region. Currently axiomatized at the
  smoothness level (in `EvenAtlas.lean`); the cocycle equation will
  follow once those smoothness axioms are discharged with explicit
  chain-rule computations on `x ↦ 1/x` and the polynomial-root
  corrections.

The coefficient is parametrized by **two** polynomials `g_aff` and
`g_inf` -- one for each summand. For the form to be globally well-
defined (i.e. the cross-summand cocycle to close), `g_aff` and `g_inf`
must be related by the Möbius transformation
`g_inf(u) du/v = g_aff(1/u) (-du/u²) (u^(g+1)/v)`. This relation is
encoded in S5; here we set up the framework before assembling it.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineInfinityForm
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas

namespace Jacobians.ProjectiveCurve.HyperellipticEvenProj

open scoped Manifold ContDiff Topology
open Polynomial
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity

variable {H : HyperellipticData}

/-- Unified coefficient family on `HyperellipticEvenProj H`: dispatch
to the affine or affine-infinity coefficient by case-splitting on
`Quotient.out q`. -/
noncomputable def hyperellipticEvenCoeff
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ) :
    HyperellipticEvenProj H → ℂ → ℂ := fun q =>
  match Quotient.out q with
  | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
  | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b

/-- The unified coefficient is analytic on each chart target. -/
theorem hyperellipticEvenCoeff_isHolomorphicOneFormCoeff
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ) :
    IsHolomorphicOneFormCoeff (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (chartAt H hf.out q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (chartAt H hf.out q).target
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt]
  unfold chartAt
  rcases hQ : Quotient.out q with a | b
  · show AnalyticOn ℂ _
      (((HyperellipticAffine.affineChartAt (H := H) a)
        : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out)).target
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineCoeff (H := H) g_aff a := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have h := hyperellipticAffineCoeff_isHolomorphicOneFormCoeff
      (H := H) g_aff a
    have hExtA : (extChartAt 𝓘(ℂ, ℂ) a).target =
        ((HyperellipticAffine.affineChartAt (H := H) a)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    rw [hExtA] at h
    exact h
  · show AnalyticOn ℂ _
      (((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)
        : OpenPartialHomeomorph (HyperellipticAffineInfinity H) ℂ).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).target
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineInfinityCoeff (H := H) g_inf b := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have h := hyperellipticAffineInfinityCoeff_isHolomorphicOneFormCoeff
      (H := H) g_inf b
    have hExtB : (extChartAt 𝓘(ℂ, ℂ) b).target =
        ((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    rw [hExtB] at h
    convert h using 1

/-- The unified coefficient vanishes off each chart target. -/
theorem hyperellipticEvenCoeff_isZeroOffChartTarget
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q z hz
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (chartAt H hf.out q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (chartAt H hf.out q).target
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hz
  unfold chartAt at hz
  rcases hQ : Quotient.out q with a | b
  · simp only [hQ] at hz
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineCoeff (H := H) g_aff a := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have hLift : (affineLiftChart H hf.out a).target =
        (HyperellipticAffine.affineChartAt (H := H) a).target := by
      simp [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hLift] at hz
    have h := hyperellipticAffineCoeff_isZeroOffChartTarget (H := H) g_aff a
    have hExtA : (extChartAt 𝓘(ℂ, ℂ) a).target =
        ((HyperellipticAffine.affineChartAt (H := H) a)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    apply h
    rw [hExtA]; exact hz
  · simp only [hQ] at hz
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineInfinityCoeff (H := H) g_inf b := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have hLift : (infinityLiftChart H hf.out b).target =
        (HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b).target := by
      simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hLift] at hz
    have h := hyperellipticAffineInfinityCoeff_isZeroOffChartTarget
      (H := H) g_inf b
    have hExtB : (extChartAt 𝓘(ℂ, ℂ) b).target =
        ((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    apply h
    rw [hExtB]; exact hz

/-! ## Same-summand cocycle equations (lifted from S3/S4)

The four-way cocycle case-split on `Quotient.out q × Quotient.out q'`
has same-summand and cross-summand cases. The same-summand cases lift
directly from the affine (resp. affine-infinity) bundle's
`SatisfiesCotangentCocycle` proof through `affineLiftChart`
(resp. `infinityLiftChart`).

Both same-summand cases are derived from a single generic helper
`cocycle_lifted_through_lift_openEmbedding`, parameterized by the
underlying type (`HyperellipticAffine H` or `HyperellipticAffineInfinity H`),
the open embedding (`proj ∘ Sum.inl` or `proj ∘ Sum.inr`), and the
within-summand cocycle bundle.

Cross-summand cases (`Sum.inl × Sum.inr`, `Sum.inr × Sum.inl`) are
the gluing-region cocycles that depend on the Möbius `x ↦ 1/x`
transition smoothness — currently axiomatized in `EvenAtlas.lean`. -/

/-- **Generic cocycle lift through an open embedding of charts.**

If a coefficient family `coeff'` on `X'` satisfies the cotangent cocycle on
`X'` and the chart at points `q, q' : HyperellipticEvenProj H` agrees with
the lift of the chart at corresponding `x, x' : X'` through an injective
open embedding `f`, then the lifted coefficient family satisfies the
cocycle equation between q and q'.

This is the structural pattern shared by both same-summand cocycles. -/
theorem cocycle_lifted_through_lift_openEmbedding
    [hf : Fact (¬ Odd H.f.natDegree)]
    {X' : Type*} [TopologicalSpace X']
    {f : X' → HyperellipticEvenProj H} (hOpen : Topology.IsOpenEmbedding f)
    (hInj : Function.Injective f)
    [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ, ℂ) ω X']
    (coeff' : X' → ℂ → ℂ)
    (hCocy' : SatisfiesCotangentCocycle X' coeff')
    (coeff_lifted : HyperellipticEvenProj H → ℂ → ℂ)
    {q q' : HyperellipticEvenProj H} {x x' : X'}
    (hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      (_root_.chartAt ℂ x : OpenPartialHomeomorph X' ℂ).lift_openEmbedding hOpen)
    (hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      (_root_.chartAt ℂ x' : OpenPartialHomeomorph X' ℂ).lift_openEmbedding hOpen)
    (hCoeffQ : coeff_lifted q = coeff' x)
    (hCoeffQ' : coeff_lifted q' = coeff' x')
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    coeff_lifted q z =
      coeff_lifted q' ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  classical
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((_root_.chartAt ℂ x : OpenPartialHomeomorph X' ℂ).lift_openEmbedding hOpen).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      ((_root_.chartAt ℂ x).lift_openEmbedding hOpen).target
    rw [hChQ]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      (((_root_.chartAt ℂ x : OpenPartialHomeomorph X' ℂ).lift_openEmbedding hOpen).symm
        : ℂ → HyperellipticEvenProj H) := by
    funext w; show (_root_.chartAt ℂ q).symm w = _; rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      (((_root_.chartAt ℂ x' : OpenPartialHomeomorph X' ℂ).lift_openEmbedding hOpen)
        : HyperellipticEvenProj H → ℂ) := by
    funext w; show (_root_.chartAt ℂ q') w = _; rw [hChQ']
  rw [hExtTarget] at hz
  rw [hExtSymm] at hSrc
  rw [extChartAt_source, hChQ'] at hSrc
  simp only [OpenPartialHomeomorph.lift_openEmbedding_target] at hz
  simp only [OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm] at hSrc
  obtain ⟨x'', hx''_src, hx''_eq⟩ := hSrc
  -- Use injectivity of f to extract the X'-side source hypothesis.
  have hx_eq : (_root_.chartAt ℂ x : OpenPartialHomeomorph X' ℂ).symm z = x'' :=
    hInj hx''_eq.symm
  have hSrcSmall : (_root_.chartAt ℂ x : OpenPartialHomeomorph X' ℂ).symm z ∈
      (_root_.chartAt ℂ x' : OpenPartialHomeomorph X' ℂ).source := by
    rw [hx_eq]; exact hx''_src
  have hzX : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := by
    rw [extChartAt_target]
    show z ∈ ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ x).target ∩ Set.range ↑𝓘(ℂ, ℂ)
    show z ∈ _ ∩ Set.range (id : ℂ → ℂ)
    rw [Set.range_id, Set.inter_univ]
    exact hz
  have hSrcX : (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) x').source := by
    rw [extChartAt_source]
    show (_root_.chartAt ℂ x : OpenPartialHomeomorph X' ℂ).symm z ∈ _
    exact hSrcSmall
  have hCocyVal := hCocy' x x' z hzX hSrcX
  rw [hCoeffQ]
  rw [hCoeffQ', hExtCoe', hExtSymm]
  simp only [OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_def, OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact hCocyVal

/-- Same-summand cocycle on the affine summand, derived from
`cocycle_lifted_through_lift_openEmbedding`. -/
theorem hyperellipticEvenCoeff_cocycle_inl_inl
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (q q' : HyperellipticEvenProj H)
    (a a' : HyperellipticAffine H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inl a')
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  refine cocycle_lifted_through_lift_openEmbedding (x := a) (x' := a')
    (isOpenEmbedding_proj_inl H hf.out)
    (proj_inl_injective H)
    (hyperellipticAffineCoeff (H := H) g_aff)
    (hyperellipticAffineCoeff_satisfiesCotangentCocycle (H := H) g_aff)
    (hyperellipticEvenCoeff (H := H) g_aff g_inf)
    ?_ ?_ ?_ ?_ hz hSrc
  · show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ]; rfl
  · show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ']; rfl
  · funext w
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) w = _
    rw [hQ]
  · funext w
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) w = _
    rw [hQ']

/-- Same-summand cocycle on the affine-infinity summand, derived from
`cocycle_lifted_through_lift_openEmbedding`. -/
theorem hyperellipticEvenCoeff_cocycle_inr_inr
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (q q' : HyperellipticEvenProj H)
    (b b' : HyperellipticAffineInfinity H)
    (hQ : Quotient.out q = Sum.inr b) (hQ' : Quotient.out q' = Sum.inr b')
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  refine cocycle_lifted_through_lift_openEmbedding (x := b) (x' := b')
    (isOpenEmbedding_proj_inr H hf.out)
    (proj_inr_injective H)
    (hyperellipticAffineInfinityCoeff (H := H) g_inf)
    (hyperellipticAffineInfinityCoeff_satisfiesCotangentCocycle (H := H) g_inf)
    (hyperellipticEvenCoeff (H := H) g_aff g_inf)
    ?_ ?_ ?_ ?_ hz hSrc
  · show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ]; rfl
  · show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt
    rw [hQ']; rfl
  · funext w
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) w = _
    rw [hQ]
  · funext w
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) w = _
    rw [hQ']

/-! ## Cross-summand cocycle (axiomatized, with gluing hypothesis)

The Möbius `x ↦ 1/x` transition between affine and affine-infinity charts.
The cocycle holds **only when** `g_inf` is determined from `g_aff` by the
gluing relation `g_inf(u) = -u^(g-1) g_aff(1/u)` (where
`g = (deg H.f - 2)/2` is the genus). The axioms below take this gluing
condition as an explicit hypothesis (`g_inf = infReverse H g_aff`), so they
are no longer mathematically false for arbitrary `(g_aff, g_inf)`.

Discharging the axioms (replacing them with real proofs) requires
explicit Möbius chain-rule computations; those depend on the smoothness
axioms in `EvenAtlas.lean`.

**Soundness note.** A previous version of these axioms quantified over all
pairs `(g_aff, g_inf)` without the gluing hypothesis — that was unsound
because the cocycle is genuinely false for non-matching pairs. The current
form (with `hGluing`) is mathematically correct as a *statement*; the
remaining work is to prove it. -/

/-- The "infinity-side" polynomial paired with `g` in the Möbius gluing.

For a basis monomial `g = X^k` (with `k ≤ g_topology - 1`), this is
`-X^(g_topology - 1 - k)`. In general it is `-Polynomial.reflect
(g_topology - 1) g`, where `g_topology = H.f.natDegree / 2 - 1`. The relation
`g_inf(u) = -u^(g_topology - 1) g(1/u)` exactly cancels the factors
`dx = -du/u²` and `y = v / u^(g_topology + 1)` in the change of variable. -/
noncomputable def infReverse (H : HyperellipticData) (g : Polynomial ℂ) :
    Polynomial ℂ :=
  -Polynomial.reflect (H.f.natDegree / 2 - 2) g

/-- **Cross-summand cocycle (affine → infinity).** Axiomatized; takes the
Möbius gluing relation `g_inf = infReverse H g_aff` as an explicit
hypothesis. -/
axiom hyperellipticEvenCoeff_cocycle_inl_inr_axiom
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff)
    (q q' : HyperellipticEvenProj H)
    (a : HyperellipticAffine H) (b : HyperellipticAffineInfinity H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inr b)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1)

/-- **Cross-summand cocycle (infinity → affine).** Axiomatized; takes the
Möbius gluing relation `g_inf = infReverse H g_aff` as an explicit
hypothesis. -/
axiom hyperellipticEvenCoeff_cocycle_inr_inl_axiom
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff)
    (q q' : HyperellipticEvenProj H)
    (b : HyperellipticAffineInfinity H) (a : HyperellipticAffine H)
    (hQ : Quotient.out q = Sum.inr b) (hQ' : Quotient.out q' = Sum.inl a)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1)

/-! ## Bundled cocycle and submodule membership

Combines the four sub-case cocycles (two real same-summand proofs +
two cross-summand axioms) into the single `SatisfiesCotangentCocycle`
predicate, then assembles full `holomorphicOneFormSubmodule` membership.
-/

theorem hyperellipticEvenCoeff_satisfiesCotangentCocycle
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff) :
    SatisfiesCotangentCocycle (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q q' z hz hSrc
  rcases hQ : Quotient.out q with a | b
  · rcases hQ' : Quotient.out q' with a' | b'
    · exact hyperellipticEvenCoeff_cocycle_inl_inl g_aff g_inf q q' a a' hQ hQ' hz hSrc
    · exact hyperellipticEvenCoeff_cocycle_inl_inr_axiom g_aff g_inf hGluing
        q q' a b' hQ hQ' hz hSrc
  · rcases hQ' : Quotient.out q' with a' | b'
    · exact hyperellipticEvenCoeff_cocycle_inr_inl_axiom g_aff g_inf hGluing
        q q' b a' hQ hQ' hz hSrc
    · exact hyperellipticEvenCoeff_cocycle_inr_inr g_aff g_inf q q' b b' hQ hQ' hz hSrc

/-- **Submodule membership for the unified coefficient family** (with the
gluing condition). `hyperellipticEvenCoeff g_aff g_inf` is in
`holomorphicOneFormSubmodule (HyperellipticEvenProj H)` whenever
`g_inf = infReverse H g_aff`. -/
theorem hyperellipticEvenCoeff_mem_submodule
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf ∈
      holomorphicOneFormSubmodule (HyperellipticEvenProj H) :=
  ⟨hyperellipticEvenCoeff_isHolomorphicOneFormCoeff g_aff g_inf,
   hyperellipticEvenCoeff_satisfiesCotangentCocycle g_aff g_inf hGluing,
   hyperellipticEvenCoeff_isZeroOffChartTarget g_aff g_inf⟩

/-! ## Linearity of `hyperellipticEvenCoeff` and `infReverse` -/

@[simp] theorem hyperellipticEvenCoeff_zero
    [hf : Fact (¬ Odd H.f.natDegree)] :
    hyperellipticEvenCoeff (H := H) 0 0 = 0 := by
  funext q z
  unfold hyperellipticEvenCoeff
  rcases hQ : Quotient.out q with a | b
  · simp [hyperellipticAffineCoeff_zero]
  · simp [hyperellipticAffineInfinityCoeff_zero]

theorem hyperellipticEvenCoeff_add
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff₁ g_inf₁ g_aff₂ g_inf₂ : Polynomial ℂ) :
    hyperellipticEvenCoeff (H := H) (g_aff₁ + g_aff₂) (g_inf₁ + g_inf₂) =
      hyperellipticEvenCoeff (H := H) g_aff₁ g_inf₁ +
        hyperellipticEvenCoeff (H := H) g_aff₂ g_inf₂ := by
  funext q z
  unfold hyperellipticEvenCoeff
  rcases hQ : Quotient.out q with a | b
  · simp [hQ, hyperellipticAffineCoeff_add]
  · simp [hQ, hyperellipticAffineInfinityCoeff_add]

theorem hyperellipticEvenCoeff_smul
    [hf : Fact (¬ Odd H.f.natDegree)]
    (c : ℂ) (g_aff g_inf : Polynomial ℂ) :
    hyperellipticEvenCoeff (H := H) (c • g_aff) (c • g_inf) =
      c • hyperellipticEvenCoeff (H := H) g_aff g_inf := by
  funext q z
  unfold hyperellipticEvenCoeff
  rcases hQ : Quotient.out q with a | b
  · simp [hQ, hyperellipticAffineCoeff_smul]
  · simp [hQ, hyperellipticAffineInfinityCoeff_smul]

@[simp] theorem infReverse_zero (H : HyperellipticData) :
    infReverse H 0 = 0 := by
  unfold infReverse; simp

theorem infReverse_add (H : HyperellipticData) (g g' : Polynomial ℂ) :
    infReverse H (g + g') = infReverse H g + infReverse H g' := by
  unfold infReverse
  rw [Polynomial.reflect_add]
  ring

theorem infReverse_smul (H : HyperellipticData) (c : ℂ) (g : Polynomial ℂ) :
    infReverse H (c • g) = c • infReverse H g := by
  unfold infReverse
  have : Polynomial.reflect (H.f.natDegree / 2 - 2) (c • g) =
      c • Polynomial.reflect (H.f.natDegree / 2 - 2) g := by
    ext n
    simp [Polynomial.coeff_reflect]
  rw [this, smul_neg]

/-! ## Polynomial-identity helpers for the S5 cocycle discharge

The Möbius gluing `(x, y) ↔ (1/x, y/x^(g+1))` translates the form
`g_aff(x) dx/y` into `g_inf(u) du/v` where `g_inf = -u^(g_top - 1) g_aff(1/u)`
(for `g_aff` of degree `< g_top`). The polynomial-level identity we need
for the cocycle discharge is the inverse of this:

  `g_aff(x) = -(infReverse H g_aff)(1/x) * x^(g_top - 1)`

valid when `g_aff.natDegree < g_top`. Below we prove this via
`Polynomial.eval₂_reflect_mul_pow`. -/

/-- **Polynomial identity for the Möbius reflection.** For
`p.natDegree ≤ N` and nonzero `x`,
`(reflect N p).eval (x⁻¹) * x^N = p.eval x`. Standard reflection lemma
in disguise — derived from `Polynomial.eval₂_reflect_mul_pow`. -/
lemma reflect_eval_inv_mul_pow {p : Polynomial ℂ} {N : ℕ}
    (h : p.natDegree ≤ N) {x : ℂ} (hx : x ≠ 0) :
    (Polynomial.reflect N p).eval (x⁻¹) * x ^ N = p.eval x := by
  haveI := invertibleOfNonzero hx
  have key := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) x N p h
  have hinv : (⅟x : ℂ) = x⁻¹ := invOf_eq_inv x
  simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id, hinv] at key
  exact key

/-- **`infReverse`–evaluation identity (the gluing relation).** For
`g.natDegree < H.f.natDegree / 2 - 1` and nonzero `x`,

    `g.eval x = -(infReverse H g).eval (x⁻¹) * x ^ (H.f.natDegree / 2 - 2)`

This is the algebraic core of the cross-summand cocycle: it expresses
the polynomial transformation under `x ↦ 1/x` matching the chart-
transition between affine and infinity charts. -/
lemma eval_eq_neg_infReverse_eval_inv_mul_pow
    (H : HyperellipticData) {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.f.natDegree / 2 - 1) {x : ℂ} (hx : x ≠ 0) :
    g.eval x =
      -(infReverse H g).eval (x⁻¹) * x ^ (H.f.natDegree / 2 - 2) := by
  -- hDeg : g.natDegree < H.f.natDegree / 2 - 1, i.e., g.natDegree ≤ H.f.natDegree / 2 - 2.
  have hN : g.natDegree ≤ H.f.natDegree / 2 - 2 := by omega
  have hRefl := reflect_eval_inv_mul_pow hN hx
  -- hRefl : (reflect (H.f.natDegree / 2 - 2) g).eval (x⁻¹) * x ^ (H.f.natDegree / 2 - 2)
  --       = g.eval x
  unfold infReverse
  rw [Polynomial.eval_neg]
  linear_combination -hRefl

/-! ## Möbius derivative helpers for the S5 cocycle discharge -/

/-- Derivative of the Möbius map `z ↦ 1/z` at nonzero `z`: `-(z²)⁻¹`. -/
lemma hasDerivAt_inv_complex {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := by
  have := (hasFDerivAt_inv hz).hasDerivAt
  simpa using this

/-- `fderiv` of `z ↦ 1/z` at nonzero `z` applied to `1` gives `-(z²)⁻¹`. -/
lemma fderiv_inv_apply_one {z : ℂ} (hz : z ≠ 0) :
    fderiv ℂ (fun w : ℂ => w⁻¹) z 1 = -(z ^ 2)⁻¹ := by
  have hderiv := hasDerivAt_inv_complex hz
  change deriv (fun w : ℂ => w⁻¹) z = _
  exact hderiv.deriv

/-! ## Gluing construction (affine ↔ infinity)

Explicit constructor for the infinity-image of an affine point with
nonzero `x`-coordinate, plus the proof that this image is gluing-related
to the original. Used to instantiate the cross-summand cocycle witnesses. -/

/-- Gluing image of an affine point with nonzero `x`-coordinate. Maps
`a = (z, y)` on the affine side to its image `b = (1/z, y · z⁻¹^(g+1))`
on the infinity side via the Möbius identification. -/
noncomputable def affineGluingImage
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hxNZ : a.val.1 ≠ 0) :
    HyperellipticAffineInfinity H :=
  ⟨(a.val.1⁻¹, a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2)),
   by
     change (a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2)) ^ 2 =
            (Polynomial.reverse H.f).eval a.val.1⁻¹
     exact HyperellipticAffineInfinity.mem_of_affine H hf.out a.val.1 a.val.2
       a.property hxNZ⟩

@[simp] lemma affineGluingImage_val_fst
    [Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hxNZ : a.val.1 ≠ 0) :
    (affineGluingImage a hxNZ).val.1 = a.val.1⁻¹ := rfl

@[simp] lemma affineGluingImage_val_snd
    [Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hxNZ : a.val.1 ≠ 0) :
    (affineGluingImage a hxNZ).val.2 =
      a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) := rfl

/-- The gluing image is in the gluing relation with the original. -/
lemma hyperellipticEvenGlue_affineGluingImage
    [Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hxNZ : a.val.1 ≠ 0) :
    HyperellipticEvenGlue H (Sum.inl a) (Sum.inr (affineGluingImage a hxNZ)) := by
  refine ⟨hxNZ, ?_, ?_⟩
  · simp [affineGluingImage_val_fst]
  · simp [affineGluingImage_val_snd]

/-- The two representatives `Sum.inl a` and `Sum.inr (affineGluingImage a)`
project to the same point in `HyperellipticEvenProj H`. -/
lemma proj_eq_affineGluingImage
    [Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hxNZ : a.val.1 ≠ 0) :
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr (affineGluingImage a hxNZ)) := by
  apply Quotient.sound
  show (hyperellipticEvenSetoid H).r (Sum.inl a) (Sum.inr (affineGluingImage a hxNZ))
  rw [hyperellipticEvenSetoid_rel_iff]
  right; left
  exact hyperellipticEvenGlue_affineGluingImage a hxNZ

/-! ## Coordinate-level cross-summand cocycle

The cocycle equation for the cross-summand transition, formulated in
coordinates (z, y, v) instead of going through chart structures.
This is the **algebraic core** of the cross-summand cocycle:
once chart-level structures are unwound to provide concrete coordinate
values satisfying the gluing relation `v = y · z⁻¹^(g+1)`, the cocycle
follows from `eval_eq_neg_infReverse_eval_inv_mul_pow`.
-/

/-! ### Chart-symm at the basepoint -/

/-- The IFT-derived `squareLocalHomeomorph` chart's `symm` evaluated at
the y² value (= `H.f.eval a.val.1`) returns the basepoint y-coordinate
`a.val.2`. This is the simplest chart-symm identification — it just uses
the chart's `left_inv` at the basepoint, no analytic-continuation
argument. -/
lemma squareLocalHomeomorph_symm_at_basepoint
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H) :
    (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval a.val.1) = a.val.2 := by
  set e := squareLocalHomeomorph (H := H) a hpY with he_def
  have hSrc : a.val.2 ∈ e.source := affineChartProjX_mem_source a hpY
  have hApp : (e : ℂ → ℂ) a.val.2 = a.val.2 ^ 2 := by
    simp [e, squareLocalHomeomorph]
  rw [show (H.f.eval a.val.1) = a.val.2 ^ 2 from a.property.symm]
  rw [← hApp]
  exact e.left_inv hSrc

/-- The gluing image of `a ∈ smoothLocusY` (with nonzero `x`) lies in
`smoothLocusY` of the reversed data (its `y`-coordinate is nonzero). -/
lemma affineGluingImage_mem_smoothLocusY
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (hxNZ : a.val.1 ≠ 0) :
    affineGluingImage a hxNZ ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
  show (affineGluingImage a hxNZ).val.2 ≠ 0
  rw [affineGluingImage_val_snd]
  exact mul_ne_zero hpY (pow_ne_zero _ (inv_ne_zero hxNZ))

/-- If `proj (Sum.inl a) = proj (Sum.inr b)` in `HyperellipticEvenProj H`,
then `b` is forced to be the gluing image of `a` (and `a.val.1 ≠ 0`).

This is the structural fact that pins down the infinity-side
representative when an affine and infinity point project to the same
quotient class. Used to identify chart values in the cross-summand
cocycle. -/
lemma proj_inl_eq_proj_inr_iff
    [hf : Fact (¬ Odd H.f.natDegree)]
    {a : HyperellipticAffine H} {b : HyperellipticAffineInfinity H}
    (h : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
         Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) :
    ∃ (hxNZ : a.val.1 ≠ 0), b = affineGluingImage a hxNZ := by
  have hRel : (hyperellipticEvenSetoid H).r (Sum.inl a) (Sum.inr b) :=
    Quotient.exact h
  rw [hyperellipticEvenSetoid_rel_iff] at hRel
  rcases hRel with hEq | hGl | hGl
  · exact absurd hEq (by simp)
  · obtain ⟨hxNZ, hb1, hb2⟩ := hGl
    refine ⟨hxNZ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [affineGluingImage_val_fst, hb1]
    · simp [affineGluingImage_val_snd, hb2]
  · exact absurd hGl (by simp [HyperellipticEvenGlue])

/-- **Coordinate-level cross-summand cocycle.** Given:
* low-degree polynomial `g_aff` (degree < `g_topology - 1`),
* coordinates `z, y` with `z ≠ 0`, `y ≠ 0`,
* gluing relation `v = y · z⁻¹^(H.f.natDegree / 2)`,

the cocycle equation
`g_aff(z)/y = (infReverse H g_aff)(z⁻¹)/v · (-(z²)⁻¹)`
holds. (The on-curve equations `y² = H.f.eval z`, `v² = H.f.reverse.eval z⁻¹`
are not needed for this purely algebraic identity, only the gluing
relation between `y` and `v`. `v ≠ 0` follows automatically from
`y ≠ 0`, `z ≠ 0`, and the gluing relation.) -/
lemma cross_summand_cocycle_coord
    [hf : Fact (¬ Odd H.f.natDegree)]
    {g_aff : Polynomial ℂ}
    (hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)
    {z y v : ℂ}
    (hz : z ≠ 0) (hy : y ≠ 0)
    (hglue : v = y * z⁻¹ ^ (H.f.natDegree / 2)) :
    g_aff.eval z / y =
      (infReverse H g_aff).eval (z⁻¹) / v * (-(z ^ 2)⁻¹) := by
  classical
  have hPoly := eval_eq_neg_infReverse_eval_inv_mul_pow H hDeg hz
  -- Sanity: H.f.natDegree / 2 ≥ 2 (since deg ≥ 3 and even).
  have hge : H.f.natDegree / 2 ≥ 2 := by
    have hd := H.h_degree
    have hev : ¬ Odd H.f.natDegree := hf.out
    have : Even H.f.natDegree := Nat.not_odd_iff_even.mp hev
    obtain ⟨m, hm⟩ := this; omega
  -- Key identity: z² · z^(N-2) · z⁻¹^N = 1 where N = H.f.natDegree / 2.
  set N := H.f.natDegree / 2 with hN_def
  have hPow : z ^ 2 * z ^ (N - 2) * z⁻¹ ^ N = 1 := by
    have hNeq : 2 + (N - 2) = N := by omega
    rw [show z ^ 2 * z ^ (N - 2) = z ^ N from by rw [← pow_add, hNeq]]
    rw [← mul_pow]
    rw [mul_inv_cancel₀ hz, one_pow]
  rw [hglue]
  field_simp
  rw [hPoly]
  -- Normalize 1/z back to z⁻¹.
  rw [show (1 / z : ℂ) = z⁻¹ from one_div z]
  -- Goal should be of the form `... * (z² · z^(N-2) · z⁻¹^N) = ...`
  linear_combination -hPow * (infReverse H g_aff).eval z⁻¹

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
