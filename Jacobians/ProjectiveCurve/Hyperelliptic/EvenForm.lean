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
open Polynomial Filter
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

/-- **Cross-summand cocycle (affine → infinity).** Axiomatized for the
sub-cases not yet discharged. The smoothLocusY × smoothLocusY case is
real (`cocycle_inl_inr_smoothLocusY_smoothLocusY`); the other 3 sub-cases
remain axiomatized. Takes the Möbius gluing relation
`g_inf = infReverse H g_aff` as an explicit hypothesis. -/
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

/-- The reflection identity at the chart level: for nonzero `x`,
`(H.f.reverse).eval x⁻¹ = H.f.eval x · x⁻¹^(deg H.f)`. -/
lemma reverse_eval_inv_eq
    (x : ℂ) (hx : x ≠ 0) :
    (H.f.reverse).eval x⁻¹ = H.f.eval x * x⁻¹ ^ H.f.natDegree := by
  haveI := invertibleOfNonzero hx
  have key := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) x H.f
  have hinv : (⅟x : ℂ) = x⁻¹ := invOf_eq_inv x
  simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id, hinv] at key
  have hx_pow : (x ^ H.f.natDegree) ≠ 0 := pow_ne_zero _ hx
  have h2 : (H.f.eval x * x⁻¹ ^ H.f.natDegree) * x ^ H.f.natDegree = H.f.eval x := by
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]
  rw [← mul_right_cancel₀ hx_pow (key.trans h2.symm)]

/-- **Chart-symm gluing identity (membership-conditional).** Given:
* `a ∈ smoothLocusY` with `a.val.1 ≠ 0`,
* `H.f.eval z ∈ e_a.target` (so `e_a.symm` is defined at this value),
* `z ≠ 0`,
* `LHS = e_a.symm(H.f.eval z) · z⁻¹^(g+1) ∈ e_b.source` (the "right
  branch" condition; ensures the IFT chart at `b` picks the matching
  branch),

we have `LHS = e_b.symm((H.f.reverse).eval z⁻¹)`. The on-curve
relations square both sides to `(H.f.reverse).eval z⁻¹`, and the
membership of `LHS` in `e_b.source` lets us apply `e_b` to both sides
(both end up at `(H.f.reverse).eval z⁻¹`), giving equality via
injectivity of `e_b` on its source. -/
lemma squareLocalHomeomorph_symm_gluing
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ} (hzMem : H.f.eval z ∈ (squareLocalHomeomorph (H := H) a hpY).target)
    (hzNZ : z ≠ 0)
    (b : HyperellipticAffineInfinity H)
    (hpY_b : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hSourceLHS :
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) *
        z⁻¹ ^ (H.f.natDegree / 2) ∈
      (squareLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b).source) :
    (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) *
        z⁻¹ ^ (H.f.natDegree / 2) =
      (squareLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b).symm
        ((Polynomial.reverse H.f).eval z⁻¹) := by
  set e_a := squareLocalHomeomorph (H := H) a hpY with he_a_def
  set e_b := squareLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b with he_b_def
  set y := e_a.symm (H.f.eval z)
  set lhs := y * z⁻¹ ^ (H.f.natDegree / 2)
  -- `y² = H.f.eval z` from chart right_inv.
  have hy_sq : y ^ 2 = H.f.eval z := by
    have h := e_a.right_inv hzMem
    have hAct : (e_a : ℂ → ℂ) y = y ^ 2 := by simp [e_a, squareLocalHomeomorph]
    rw [← hAct]; exact h
  -- Hence `lhs² = (H.f.reverse).eval z⁻¹` via the on-curve reflection.
  have hlhs_sq : lhs ^ 2 = (Polynomial.reverse H.f).eval z⁻¹ := by
    show (y * z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = (Polynomial.reverse H.f).eval z⁻¹
    rw [mul_pow, hy_sq]
    have hpow_eq : (z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = z⁻¹ ^ H.f.natDegree := by
      rw [← pow_mul]
      congr 1
      have hev : ¬ Odd H.f.natDegree := hf.out
      have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hev
      obtain ⟨m, hm⟩ := heven; omega
    rw [hpow_eq]
    exact (reverse_eval_inv_eq z hzNZ).symm
  -- Apply `e_b` to both sides; they coincide at `(H.f.reverse).eval z⁻¹`.
  have he_b_lhs : (e_b : ℂ → ℂ) lhs = lhs ^ 2 := by
    simp [e_b, squareLocalHomeomorph]
  have he_b_rhs_target :
      (Polynomial.reverse H.f).eval z⁻¹ ∈ e_b.target := by
    rw [← hlhs_sq, ← he_b_lhs]
    exact e_b.map_source hSourceLHS
  have he_b_rhs_source :
      e_b.symm ((Polynomial.reverse H.f).eval z⁻¹) ∈ e_b.source :=
    e_b.map_target he_b_rhs_target
  have he_b_rhs : (e_b : ℂ → ℂ) (e_b.symm ((Polynomial.reverse H.f).eval z⁻¹)) =
      (Polynomial.reverse H.f).eval z⁻¹ :=
    e_b.right_inv he_b_rhs_target
  have hcombine :
      (e_b : ℂ → ℂ) lhs =
      (e_b : ℂ → ℂ) (e_b.symm ((Polynomial.reverse H.f).eval z⁻¹)) := by
    rw [he_b_lhs, hlhs_sq, he_b_rhs]
  exact e_b.injOn hSourceLHS he_b_rhs_source hcombine

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

/-! ### Chart transition formula (projX × projU sub-case)

The chart transition `infinityLiftChart_b ∘ affineLiftChart_a.symm`
on the chart-overlap source equals `w ↦ w⁻¹` (the Möbius). This is
the core geometric content of the cross-summand cocycle in the
smoothLocusY × smoothLocusY (reverseData) sub-case. -/

private lemma chart_transition_eq_inv_X_U
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpY_b : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    {w : ℂ}
    (hw : w ∈ ((affineLiftChart H hf.out a).symm.trans
        (infinityLiftChart H hf.out b)).source) :
    (infinityLiftChart H hf.out b) ((affineLiftChart H hf.out a).symm w) = w⁻¹ := by
  have hwt : w ∈ (affineLiftChart H hf.out a).target := hw.1
  have hws : (affineLiftChart H hf.out a).symm w ∈
      (infinityLiftChart H hf.out b).source := hw.2
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target] at hwt
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm, affineLiftChart] at hws
  rw [affineChartAt_of_mem_smoothLocusY a hpY] at hwt hws
  obtain ⟨bb, hbb_src, hbb_eq⟩ := hws
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpY_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjX (H := H) a hpY).symm w)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hwNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  have hbb1 : bb.val.1 = w⁻¹ := by
    rw [hbb]; simp only [affineGluingImage_val_fst]
    rw [affineChartProjX_symm_apply_fst a hpY hwt]
  -- chart_q' applied to (proj∘Sum.inl) (chart_a.symm w) = (proj∘Sum.inr) bb (by gluing)
  -- Then lift_openEmbedding_apply gives (affineChartAt b) bb = bb.val.1 = w⁻¹.
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_apply]
  -- Rewrite affineChartAt → affineChartProjX in goal
  rw [show (HyperellipticAffine.affineChartAt (H := H) a).symm w =
      ((affineChartProjX (H := H) a hpY).symm w : HyperellipticAffine H) from by
    rw [affineChartAt_of_mem_smoothLocusY a hpY]]
  -- Now goal: infinityLiftChart b (proj H (Sum.inl ((affineChartProjX a hpY).symm w))) = w⁻¹
  rw [show proj H (Sum.inl ((affineChartProjX (H := H) a hpY).symm w)) =
      proj H (Sum.inr bb) from
    show (proj H ∘ Sum.inl) ((affineChartProjX (H := H) a hpY).symm w) =
      (proj H ∘ Sum.inr) bb from hbb_eq.symm]
  show ((HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).lift_openEmbedding
      (isOpenEmbedding_proj_inr H hf.out)) ((proj H ∘ Sum.inr) bb) = w⁻¹
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpY_b]
  exact hbb1

/-! ### Chart transition formula (projY × projU sub-case)

For `a ∉ smoothLocusY` (so `chart_a = affineChartProjY` at branch
point) and `b ∈ smoothLocusY` of reverseData (so `chart_b =
affineChartProjX` in reverseData frame), the chart transition is
`w ↦ x_a(w)⁻¹` where `x_a(w) = polynomialLocalHomeomorph.symm(w²)`. -/

private lemma chart_transition_eq_inv_Y_U
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpY_b : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    {w : ℂ}
    (hw : w ∈ ((affineLiftChart H hf.out a).symm.trans
        (infinityLiftChart H hf.out b)).source) :
    (infinityLiftChart H hf.out b) ((affineLiftChart H hf.out a).symm w) =
      ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ := by
  have hwt : w ∈ (affineLiftChart H hf.out a).target := hw.1
  have hws : (affineLiftChart H hf.out a).symm w ∈
      (infinityLiftChart H hf.out b).source := hw.2
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target] at hwt
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm, affineLiftChart] at hws
  rw [affineChartAt_of_not_mem_smoothLocusY a hpYn] at hwt hws
  -- Use that hpX matches the smoothLocusX derivation from hpYn.
  have hpX_eq : mem_smoothLocusX_of_y_eq_zero H (show a.val.2 = 0 by simpa [smoothLocusY] using hpYn) = hpX :=
    rfl
  obtain ⟨bb, hbb_src, hbb_eq⟩ := hws
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpY_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjY (H := H) a hpX).symm w)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hwNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  have hbb1 : bb.val.1 =
      ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ := by
    rw [hbb]; simp only [affineGluingImage_val_fst]
    rw [affineChartProjY_symm_apply_fst a hpX hwt]
  -- Now compute infinityLiftChart applied to chart_a.symm w.
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_apply]
  rw [show (HyperellipticAffine.affineChartAt (H := H) a).symm w =
      ((affineChartProjY (H := H) a hpX).symm w : HyperellipticAffine H) from by
    rw [affineChartAt_of_not_mem_smoothLocusY a hpYn]]
  rw [show proj H (Sum.inl ((affineChartProjY (H := H) a hpX).symm w)) =
      proj H (Sum.inr bb) from
    show (proj H ∘ Sum.inl) ((affineChartProjY (H := H) a hpX).symm w) =
      (proj H ∘ Sum.inr) bb from hbb_eq.symm]
  show ((HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).lift_openEmbedding
      (isOpenEmbedding_proj_inr H hf.out)) ((proj H ∘ Sum.inr) bb) =
      ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpY_b]
  exact hbb1

/-! ### Cross-summand cocycle: projX × projU sub-case (real proof)

The first sub-case of the cross-summand cocycle is now a real proof
(no axiom). Given `a ∈ smoothLocusY H` and `b ∈ smoothLocusY` of the
reversed data, the cocycle equation holds via:
* `chart_transition_eq_inv_X_U` (Möbius transition formula)
* `fderiv_inv_apply_one` (Möbius derivative)
* `squareLocalHomeomorph_symm_gluing` (chart-symm consistency)
* `cross_summand_cocycle_coord` (algebraic core).
-/

theorem cocycle_inl_inr_smoothLocusY_smoothLocusY
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff)
    (hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpY_b : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (q q' : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inr b)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  classical
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      affineLiftChart H hf.out a := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt; rw [hQ]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      infinityLiftChart H hf.out b := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt; rw [hQ']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = (affineLiftChart H hf.out a).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineLiftChart H hf.out a).target
    rw [hChQ]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      ((affineLiftChart H hf.out a).symm : ℂ → HyperellipticEvenProj H) := by
    funext w; show (_root_.chartAt ℂ q).symm w = _; rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      ((infinityLiftChart H hf.out b) : HyperellipticEvenProj H → ℂ) := by
    funext w; show (_root_.chartAt ℂ q') w = _; rw [hChQ']
  have hExtSrc' : (extChartAt 𝓘(ℂ, ℂ) q').source = (infinityLiftChart H hf.out b).source := by
    rw [extChartAt_source, hChQ']
  rw [hExtTarget] at hz
  have hSrc_lift : (affineLiftChart H hf.out a).symm z ∈
      (infinityLiftChart H hf.out b).source := by
    rw [hExtSymm] at hSrc; rw [hExtSrc'] at hSrc; exact hSrc
  have hzInOverlap : z ∈ ((affineLiftChart H hf.out a).symm.trans
      (infinityLiftChart H hf.out b)).source := ⟨hz, hSrc_lift⟩
  have hOverlapOpen : IsOpen ((affineLiftChart H hf.out a).symm.trans
      (infinityLiftChart H hf.out b)).source :=
    ((affineLiftChart H hf.out a).symm.trans (infinityLiftChart H hf.out b)).open_source
  rw [show (affineLiftChart H hf.out a).target =
      ((affineChartProjX (H := H) a hpY) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target from by
    simp [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [affineChartAt_of_mem_smoothLocusY a hpY]] at hz
  have hSrc_unwound : ((affineLiftChart H hf.out a).symm z) ∈
      (infinityLiftChart H hf.out b).source := hSrc_lift
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm, affineLiftChart] at hSrc_unwound
  rw [affineChartAt_of_mem_smoothLocusY a hpY] at hSrc_unwound
  obtain ⟨bb, hbb_src, hbb_eq⟩ := hSrc_unwound
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpY_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjX (H := H) a hpY).symm z)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hxNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  have hzNZ : z ≠ 0 := by
    rw [affineChartProjX_symm_apply_fst a hpY hz] at hxNZ; exact hxNZ
  set e_a := squareLocalHomeomorph (H := H) a hpY
  set e_b := squareLocalHomeomorph
    (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b
  set y : ℂ := e_a.symm (H.f.eval z) with hy_def
  have hyNZ : y ≠ 0 := squareLocalHomeomorph_symm_ne_zero a hpY hz
  have hbb2 : bb.val.2 = y * z⁻¹ ^ (H.f.natDegree / 2) := by
    rw [hbb]; simp only [affineGluingImage_val_snd]
    rw [affineChartProjX_symm_apply_fst a hpY hz]
    rw [affineChartProjX_symm_apply_snd a hpY hz]
  have hLHSinSrc : y * z⁻¹ ^ (H.f.natDegree / 2) ∈ e_b.source := by
    rw [← hbb2]; exact hbb_src
  set v : ℂ := e_b.symm ((Polynomial.reverse H.f).eval z⁻¹) with hv_def
  have hgluing_yz : y * z⁻¹ ^ (H.f.natDegree / 2) = v :=
    squareLocalHomeomorph_symm_gluing a hpY hz hzNZ b hpY_b hLHSinSrc
  have hQ'apply :
      (extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = z⁻¹ := by
    rw [hExtCoe', hExtSymm]
    exact chart_transition_eq_inv_X_U a hpY b hpY_b hzInOverlap
  have hFderivEq :
      fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 = -(z^2)⁻¹ := by
    rw [hExtCoe', hExtSymm]
    have hEqOnSrc : (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) =ᶠ[nhds z] (fun w => w⁻¹) := by
      refine eventually_of_mem (hOverlapOpen.mem_nhds hzInOverlap) ?_
      intro w hw
      exact chart_transition_eq_inv_X_U a hpY b hpY_b hw
    show fderiv ℂ (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) z 1 = -(z^2)⁻¹
    rw [Filter.EventuallyEq.fderiv_eq hEqOnSrc]
    exact fderiv_inv_apply_one hzNZ
  have hLHS : hyperellipticEvenCoeff (H := H) g_aff g_inf q z = g_aff.eval z / y := by
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) z = _
    rw [hQ]
    show hyperellipticAffineCoeff (H := H) g_aff a z = _
    have h1 : hyperellipticAffineCoeff (H := H) g_aff a z = affineProjXCoeff g_aff a hpY z := by
      simp [hyperellipticAffineCoeff, hpY]
    rw [h1, affineProjXCoeff_eq_on_target g_aff a hpY hz]
  have hzInvT : z⁻¹ ∈ ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)).target := by
    have hbb1 : bb.val.1 = z⁻¹ := by
      rw [hbb]; simp only [affineGluingImage_val_fst]
      rw [affineChartProjX_symm_apply_fst a hpY hz]
    have h1 : ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)) bb ∈
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)).target :=
      OpenPartialHomeomorph.map_source _ hbb_src
    rw [show ((affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)) bb = bb.val.1 from rfl,
      hbb1] at h1
    exact h1
  have hRHScoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q' z⁻¹ = g_inf.eval z⁻¹ / v := by
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) z⁻¹ = _
    rw [hQ']
    show hyperellipticAffineInfinityCoeff (H := H) g_inf b z⁻¹ = _
    have h1 : hyperellipticAffineInfinityCoeff (H := H) g_inf b z⁻¹ =
        hyperellipticAffineCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b z⁻¹ := rfl
    rw [h1]
    have h2 : hyperellipticAffineCoeff
        (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b z⁻¹ =
        affineProjXCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpY_b z⁻¹ := by
      show (if hpY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) then
          affineProjXCoeff (H := HyperellipticAffineInfinity.reverseData H hf.out)
            g_inf b hpY z⁻¹
        else _) = _
      rw [dif_pos hpY_b]
    rw [h2, affineProjXCoeff_eq_on_target
      (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpY_b hzInvT]
    show g_inf.eval z⁻¹ / e_b.symm
        ((HyperellipticAffineInfinity.reverseData H hf.out).f.eval z⁻¹) = _
    rfl
  rw [hLHS, hQ'apply, hRHScoeff, hFderivEq]
  rw [hGluing]
  exact cross_summand_cocycle_coord hDeg hzNZ hyNZ hgluing_yz.symm

/-! ### Cross-summand cocycle: projY × projU sub-case (real proof) -/

theorem cocycle_inl_inr_smoothLocusXNotY_smoothLocusY
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff)
    (hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpY_b : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (q q' : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inr b)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target)
    (hSrc : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q').source) :
    hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      hyperellipticEvenCoeff (H := H) g_aff g_inf q'
        ((extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1) := by
  classical
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      affineLiftChart H hf.out a := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt; rw [hQ]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      infinityLiftChart H hf.out b := by
    show Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold Jacobians.ProjectiveCurve.HyperellipticEvenProj.chartAt; rw [hQ']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = (affineLiftChart H hf.out a).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineLiftChart H hf.out a).target
    rw [hChQ]
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      ((affineLiftChart H hf.out a).symm : ℂ → HyperellipticEvenProj H) := by
    funext w; show (_root_.chartAt ℂ q).symm w = _; rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      ((infinityLiftChart H hf.out b) : HyperellipticEvenProj H → ℂ) := by
    funext w; show (_root_.chartAt ℂ q') w = _; rw [hChQ']
  have hExtSrc' : (extChartAt 𝓘(ℂ, ℂ) q').source = (infinityLiftChart H hf.out b).source := by
    rw [extChartAt_source, hChQ']
  rw [hExtTarget] at hz
  have hSrc_lift : (affineLiftChart H hf.out a).symm z ∈
      (infinityLiftChart H hf.out b).source := by
    rw [hExtSymm] at hSrc; rw [hExtSrc'] at hSrc; exact hSrc
  have hzInOverlap : z ∈ ((affineLiftChart H hf.out a).symm.trans
      (infinityLiftChart H hf.out b)).source := ⟨hz, hSrc_lift⟩
  have hOverlapOpen : IsOpen ((affineLiftChart H hf.out a).symm.trans
      (infinityLiftChart H hf.out b)).source :=
    ((affineLiftChart H hf.out a).symm.trans (infinityLiftChart H hf.out b)).open_source
  rw [show (affineLiftChart H hf.out a).target =
      ((affineChartProjY (H := H) a hpX) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target from by
    simp [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [affineChartAt_of_not_mem_smoothLocusY a hpYn]] at hz
  have hSrc_unwound : ((affineLiftChart H hf.out a).symm z) ∈
      (infinityLiftChart H hf.out b).source := hSrc_lift
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm, affineLiftChart] at hSrc_unwound
  rw [affineChartAt_of_not_mem_smoothLocusY a hpYn] at hSrc_unwound
  obtain ⟨bb, hbb_src, hbb_eq⟩ := hSrc_unwound
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpY_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjY (H := H) a hpX).symm z)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hxNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  set x_a : ℂ := (polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2) with hx_a_def
  have hx_aNZ : x_a ≠ 0 := by
    rw [affineChartProjY_symm_apply_fst a hpX hz] at hxNZ
    simpa [x_a] using hxNZ
  have hbb1 : bb.val.1 = x_a⁻¹ := by
    rw [hbb]; simp only [affineGluingImage_val_fst]
    simp only [affineChartProjY_symm_apply_fst a hpX hz, x_a]
  have hbb2 : bb.val.2 = z * x_a⁻¹ ^ (H.f.natDegree / 2) := by
    rw [hbb]; simp only [affineGluingImage_val_snd]
    rw [affineChartProjY_symm_apply_fst a hpX hz, affineChartProjY_symm_apply_snd a hpX hz]
  set e_b := squareLocalHomeomorph
    (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b
  -- bb.val.2 ∈ e_b.source, so bb.val.2 ≠ 0.
  have hbb2_in_src : bb.val.2 ∈ e_b.source := hbb_src
  have hbb2NZ : bb.val.2 ≠ 0 := by
    intro h0
    exact squareLocalHomeomorph_zero_notMem_source
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b (h0 ▸ hbb2_in_src)
  have hzNZ : z ≠ 0 := by
    intro hz0
    apply hbb2NZ
    rw [hbb2, hz0, zero_mul]
  -- Derive bb.val.2 = e_b.symm((H.f.reverse).eval x_a⁻¹) via e_b injectivity.
  set v : ℂ := e_b.symm ((Polynomial.reverse H.f).eval x_a⁻¹) with hv_def
  -- bb.val.2² = (H.f.reverse).eval bb.val.1 (curve equation in reverseData frame).
  have hbb2_sq : bb.val.2 ^ 2 = (Polynomial.reverse H.f).eval bb.val.1 := by
    have := bb.property
    -- bb.val.2² = (reverseData.f).eval bb.val.1 = (H.f.reverse).eval bb.val.1.
    show (bb.val.2)^2 = (Polynomial.reverse H.f).eval bb.val.1
    convert bb.property using 1
  have hbb2_sq_x_a_inv : bb.val.2 ^ 2 = (Polynomial.reverse H.f).eval x_a⁻¹ := by
    rw [hbb2_sq, hbb1]
  -- (H.f.reverse).eval x_a⁻¹ ∈ e_b.target.
  have h_target : (Polynomial.reverse H.f).eval x_a⁻¹ ∈ e_b.target := by
    rw [← hbb2_sq_x_a_inv]
    have : e_b bb.val.2 = bb.val.2 ^ 2 := by simp [e_b, squareLocalHomeomorph]
    rw [← this]
    exact e_b.map_source hbb2_in_src
  have hv_in_src : v ∈ e_b.source := e_b.map_target h_target
  -- e_b at both bb.val.2 and v gives same value.
  have h_eb_v : e_b v = (Polynomial.reverse H.f).eval x_a⁻¹ := e_b.right_inv h_target
  have h_eb_bb : e_b bb.val.2 = (Polynomial.reverse H.f).eval x_a⁻¹ := by
    have : e_b bb.val.2 = bb.val.2 ^ 2 := by simp [e_b, squareLocalHomeomorph]
    rw [this, hbb2_sq_x_a_inv]
  have hbb2_eq_v : bb.val.2 = v :=
    e_b.injOn hbb2_in_src hv_in_src (h_eb_bb.trans h_eb_v.symm)
  -- chart_q' (chart_q.symm z) = x_a⁻¹ (from chart_transition_eq_inv_Y_U).
  have hQ'apply :
      (extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = x_a⁻¹ := by
    rw [hExtCoe', hExtSymm]
    exact chart_transition_eq_inv_Y_U a hpX hpYn b hpY_b hzInOverlap
  -- fderiv computation: T'(z) = -(2z) / (f'(x_a) · x_a²) via chain rule.
  have hx_aHasDeriv : HasDerivAt
      (fun w : ℂ => (polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
      (2 * z / H.f.derivative.eval x_a) z :=
    affineChartProjY_to_projX_transition_hasDerivAt a hpX hz
  have hTHasDeriv : HasDerivAt
      (fun w : ℂ => ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹)
      (-(2 * z / H.f.derivative.eval x_a) / x_a ^ 2) z := by
    have := hx_aHasDeriv.fun_inv hx_aNZ
    convert this using 1
  have hFderivEq :
      fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 =
      -(2 * z / H.f.derivative.eval x_a) / x_a ^ 2 := by
    rw [hExtCoe', hExtSymm]
    have hEqOnSrc : (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) =ᶠ[nhds z]
      (fun w => ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹) := by
      refine eventually_of_mem (hOverlapOpen.mem_nhds hzInOverlap) ?_
      intro w hw
      exact chart_transition_eq_inv_Y_U a hpX hpYn b hpY_b hw
    show fderiv ℂ (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) z 1 = _
    rw [Filter.EventuallyEq.fderiv_eq hEqOnSrc]
    change deriv (fun w : ℂ => ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹) z = _
    exact hTHasDeriv.deriv
  -- LHS coefficient: 2 g_aff(x_a) / f'(x_a).
  have hLHS : hyperellipticEvenCoeff (H := H) g_aff g_inf q z =
      2 * g_aff.eval x_a / H.f.derivative.eval x_a := by
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) z = _
    rw [hQ]
    show hyperellipticAffineCoeff (H := H) g_aff a z = _
    have h1 : hyperellipticAffineCoeff (H := H) g_aff a z = affineProjYCoeff g_aff a hpX z := by
      simp [hyperellipticAffineCoeff, hpYn]
    rw [h1, affineProjYCoeff_eq_on_target g_aff a hpX hz]
  -- RHS coefficient at x_a⁻¹.
  have hzInvT : x_a⁻¹ ∈ ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)).target := by
    have h1 : ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)) bb ∈
      ((affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)).target :=
      OpenPartialHomeomorph.map_source _ hbb_src
    rw [show ((affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpY_b)) bb = bb.val.1 from rfl,
      hbb1] at h1
    exact h1
  have hRHScoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q' x_a⁻¹ =
      g_inf.eval x_a⁻¹ / v := by
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) x_a⁻¹ = _
    rw [hQ']
    show hyperellipticAffineInfinityCoeff (H := H) g_inf b x_a⁻¹ = _
    have h1 : hyperellipticAffineInfinityCoeff (H := H) g_inf b x_a⁻¹ =
        hyperellipticAffineCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b x_a⁻¹ := rfl
    rw [h1]
    have h2 : hyperellipticAffineCoeff
        (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b x_a⁻¹ =
        affineProjXCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpY_b x_a⁻¹ := by
      show (if hpY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) then
          affineProjXCoeff (H := HyperellipticAffineInfinity.reverseData H hf.out)
            g_inf b hpY x_a⁻¹
        else _) = _
      rw [dif_pos hpY_b]
    rw [h2, affineProjXCoeff_eq_on_target
      (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpY_b hzInvT]
    show g_inf.eval x_a⁻¹ / e_b.symm
        ((HyperellipticAffineInfinity.reverseData H hf.out).f.eval x_a⁻¹) = _
    rfl
  -- Algebraic step: combine cross_summand_cocycle_coord at (x_a, z, v) with rescaling.
  rw [hLHS, hQ'apply, hRHScoeff, hFderivEq]
  rw [hGluing]
  have hgluing_xz : v = z * x_a⁻¹ ^ (H.f.natDegree / 2) := hbb2_eq_v ▸ hbb2
  have hcore := cross_summand_cocycle_coord (H := H) (g_aff := g_aff)
    hDeg hx_aNZ hzNZ hgluing_xz
  have hf'NZ : H.f.derivative.eval x_a ≠ 0 :=
    polynomialLocalHomeomorph_symm_eval_derivative_ne_zero a hpX hz
  have hvNZ : v ≠ 0 := hbb2_eq_v ▸ hbb2NZ
  -- hcore : g_aff(x_a)/z = (infReverse H g_aff)(x_a⁻¹)/v * (-(x_a²)⁻¹)
  -- Goal: 2 * g_aff(x_a) / f'(x_a) = (infReverse H g_aff)(x_a⁻¹) / v *
  --       (-(2*z/f'(x_a)) / x_a²)
  calc 2 * g_aff.eval x_a / H.f.derivative.eval x_a
      = g_aff.eval x_a / z * (2 * z / H.f.derivative.eval x_a) := by
        field_simp
    _ = (infReverse H g_aff).eval x_a⁻¹ / v * (-(x_a^2)⁻¹) *
          (2 * z / H.f.derivative.eval x_a) := by rw [hcore]
    _ = (infReverse H g_aff).eval x_a⁻¹ / v *
          (-(2 * z / H.f.derivative.eval x_a) / x_a^2) := by ring

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
