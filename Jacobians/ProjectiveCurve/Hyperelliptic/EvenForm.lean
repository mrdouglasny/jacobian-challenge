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

/-- **Reverse-derivative identity** (cleared form). For nonzero `x`:
`x^N · (H.f.reverse)'(x⁻¹) + H.f'(x) · x² = N · H.f(x) · x`
where `N = H.f.natDegree`. Derived from differentiating
`reverse_eval_inv_eq` and equating via `HasDerivAt.unique`. -/
lemma reverse_derivative_eval_inv_mul_pow (x : ℂ) (hx : x ≠ 0) :
    x ^ H.f.natDegree * (Polynomial.reverse H.f).derivative.eval x⁻¹ +
      H.f.derivative.eval x * x ^ 2 =
      (H.f.natDegree : ℂ) * H.f.eval x * x := by
  have hxsqNZ : x ^ 2 ≠ 0 := pow_ne_zero _ hx
  have h_inv : HasDerivAt (fun w : ℂ => w⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv_complex hx
  have h_lhs : HasDerivAt (fun w : ℂ => (Polynomial.reverse H.f).eval w⁻¹)
      ((Polynomial.reverse H.f).derivative.eval x⁻¹ * (-(x ^ 2)⁻¹)) x := by
    have h1 := (Polynomial.reverse H.f).hasDerivAt x⁻¹
    exact h1.comp x h_inv
  have h_inv_pow : HasDerivAt
      (fun w : ℂ => w⁻¹ ^ H.f.natDegree)
      ((H.f.natDegree : ℕ) * x⁻¹ ^ (H.f.natDegree - 1) * (-(x ^ 2)⁻¹)) x :=
    h_inv.fun_pow _
  have h_f := H.f.hasDerivAt x
  have h_rhs := h_f.fun_mul h_inv_pow
  have h_eq_funs : (fun w : ℂ => (Polynomial.reverse H.f).eval w⁻¹) =ᶠ[nhds x]
      (fun w : ℂ => H.f.eval w * w⁻¹ ^ H.f.natDegree) := by
    have hOpen : IsOpen ({w : ℂ | w ≠ 0}) := isOpen_compl_singleton
    refine eventually_of_mem (hOpen.mem_nhds hx) ?_
    intro w hwNZ
    exact reverse_eval_inv_eq w hwNZ
  have h_rhs_lifted := h_rhs.congr_of_eventuallyEq h_eq_funs
  have h_unique := h_lhs.unique h_rhs_lifted
  push_cast at h_unique
  have h_step1 : (Polynomial.reverse H.f).derivative.eval x⁻¹ =
      -x ^ 2 * H.f.derivative.eval x * x⁻¹ ^ H.f.natDegree +
      (H.f.natDegree : ℂ) * H.f.eval x * x⁻¹ ^ (H.f.natDegree - 1) := by
    have hxsq_cancel : (-(x ^ 2)⁻¹) * -(x ^ 2) = 1 := by
      rw [neg_mul_neg]; exact inv_mul_cancel₀ hxsqNZ
    have h1 : (Polynomial.reverse H.f).derivative.eval x⁻¹ =
        ((Polynomial.reverse H.f).derivative.eval x⁻¹ * -(x ^ 2)⁻¹) * -(x ^ 2) := by
      rw [mul_assoc, hxsq_cancel, mul_one]
    rw [h1, h_unique]
    linear_combination
      ((H.f.natDegree : ℂ) * H.f.eval x * x⁻¹ ^ (H.f.natDegree - 1)) * hxsq_cancel
  rw [h_step1]
  by_cases hN : H.f.natDegree = 0
  · exfalso
    have hd := H.h_degree
    omega
  have hNge1 : H.f.natDegree ≥ 1 := Nat.one_le_iff_ne_zero.mpr hN
  have h_invN : x⁻¹ ^ H.f.natDegree * x ^ H.f.natDegree = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  have h_invN_pred : x⁻¹ ^ (H.f.natDegree - 1) * x ^ H.f.natDegree = x := by
    have hNeq : x ^ H.f.natDegree = x ^ (H.f.natDegree - 1) * x := by
      rw [show x ^ H.f.natDegree = x ^ (H.f.natDegree - 1 + 1) from by
        rw [Nat.sub_add_cancel hNge1]]
      rw [pow_succ]
    rw [hNeq]
    rw [show x⁻¹ ^ (H.f.natDegree - 1) * (x ^ (H.f.natDegree - 1) * x) =
      (x⁻¹ ^ (H.f.natDegree - 1) * x ^ (H.f.natDegree - 1)) * x from by ring]
    rw [show x⁻¹ ^ (H.f.natDegree - 1) * x ^ (H.f.natDegree - 1) = 1 from by
      rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]]
    ring
  linear_combination
    (-(x ^ 2) * H.f.derivative.eval x) * h_invN +
      ((H.f.natDegree : ℂ) * H.f.eval x) * h_invN_pred

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

/-! ### Chart transition formula (projX × projV sub-case)

For `a ∈ smoothLocusY` (so `chart_a = affineChartProjX`) and
`b ∉ smoothLocusY` of reverseData but `b ∈ smoothLocusX` (so
`chart_b = affineChartProjY`), the chart transition is
`w ↦ e_a.symm(H.f.eval w) · w⁻¹^(g+1)` (the y-coordinate of the
gluing image, which is the projY chart value on the infinity side). -/

private lemma chart_transition_eq_X_V
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpX_b : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn_b : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    {w : ℂ}
    (hw : w ∈ ((affineLiftChart H hf.out a).symm.trans
        (infinityLiftChart H hf.out b)).source) :
    (infinityLiftChart H hf.out b) ((affineLiftChart H hf.out a).symm w) =
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2) := by
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
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_not_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpYn_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjX (H := H) a hpY).symm w)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hwNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  have hbb2 : bb.val.2 =
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2) := by
    rw [hbb]; simp only [affineGluingImage_val_snd]
    rw [affineChartProjX_symm_apply_fst a hpY hwt,
        affineChartProjX_symm_apply_snd a hpY hwt]
  -- Now compute infinityLiftChart applied to chart_a.symm w.
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_apply]
  rw [show (HyperellipticAffine.affineChartAt (H := H) a).symm w =
      ((affineChartProjX (H := H) a hpY).symm w : HyperellipticAffine H) from by
    rw [affineChartAt_of_mem_smoothLocusY a hpY]]
  rw [show proj H (Sum.inl ((affineChartProjX (H := H) a hpY).symm w)) =
      proj H (Sum.inr bb) from
    show (proj H ∘ Sum.inl) ((affineChartProjX (H := H) a hpY).symm w) =
      (proj H ∘ Sum.inr) bb from hbb_eq.symm]
  show ((HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).lift_openEmbedding
      (isOpenEmbedding_proj_inr H hf.out)) ((proj H ∘ Sum.inr) bb) =
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2)
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_not_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpYn_b]
  exact hbb2

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

/-! ### Cross-summand cocycle: projX × projV sub-case (real proof)

For `a ∈ smoothLocusY` (so `chart_a = affineChartProjX`) and `b ∉
smoothLocusY` of reverseData but `b ∈ smoothLocusX` (so `chart_b =
affineChartProjY` at infinity branch point), the cocycle holds. Key
ingredients:
* `chart_transition_eq_X_V` (transition formula `T(w) = e_a.symm(H.f.eval w) · w⁻¹^(g+1)`)
* Product rule via `HasDerivAt.fun_mul` on `e_a.symm(H.f.eval w)` and `w⁻¹^(g+1)`
* Implicit identity `T(w)² = (H.f.reverse).eval w⁻¹` plus chain-rule
  uniqueness on `T²` to derive the implicit-form derivative
  `2 v T'_explicit z² = -(H.f.reverse)'(z⁻¹)`.
* `cross_summand_cocycle_coord` plus the implicit identity discharge
  the cocycle equation algebraically.
-/

theorem cocycle_inl_inr_smoothLocusY_smoothLocusXNotY
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff)
    (hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpX_b : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn_b : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
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
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_not_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpYn_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjX (H := H) a hpY).symm z)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hxNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  have hzNZ : z ≠ 0 := by
    rw [affineChartProjX_symm_apply_fst a hpY hz] at hxNZ; exact hxNZ
  set y : ℂ := (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) with hy_def
  have hyNZ : y ≠ 0 := squareLocalHomeomorph_symm_ne_zero a hpY hz
  set v : ℂ := y * z⁻¹ ^ (H.f.natDegree / 2) with hv_def
  have hvNZ : v ≠ 0 :=
    mul_ne_zero hyNZ (pow_ne_zero _ (inv_ne_zero hzNZ))
  have hzsqNZ : z^2 ≠ 0 := pow_ne_zero _ hzNZ
  have hbb1 : bb.val.1 = z⁻¹ := by
    rw [hbb]; simp only [affineGluingImage_val_fst]
    rw [affineChartProjX_symm_apply_fst a hpY hz]
  have hbb2 : bb.val.2 = v := by
    rw [hbb]; simp only [affineGluingImage_val_snd]
    rw [affineChartProjX_symm_apply_fst a hpY hz, affineChartProjX_symm_apply_snd a hpY hz]
  -- chart_q' (chart_q.symm z) = v (from chart_transition_eq_X_V).
  have hQ'apply :
      (extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = v := by
    rw [hExtCoe', hExtSymm]
    exact chart_transition_eq_X_V a hpY b hpX_b hpYn_b hzInOverlap
  -- HasDerivAt for T(w) = e_a.symm(H.f.eval w) * w⁻¹^(g+1).
  have hy_deriv : HasDerivAt
      (fun w : ℂ => (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w))
      (H.f.derivative.eval z / (2 * y)) z :=
    affineChartProjX_to_projY_transition_hasDerivAt (H := H) a hpY hz
  have hinv_deriv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z^2)⁻¹) z :=
    hasDerivAt_inv_complex hzNZ
  have hpow_deriv : HasDerivAt
      (fun w : ℂ => w⁻¹ ^ (H.f.natDegree / 2))
      ((H.f.natDegree / 2 : ℕ) * z⁻¹ ^ ((H.f.natDegree / 2) - 1) * (-(z^2)⁻¹)) z :=
    hinv_deriv.fun_pow _
  have hT_deriv := hy_deriv.fun_mul hpow_deriv
  -- T(w)² = (H.f.reverse).eval w⁻¹ on chart-target ∩ {w ≠ 0}.
  have hT_sq_eventually :
      (fun w : ℂ => ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2)) ^ 2) =ᶠ[nhds z]
      (fun w => (Polynomial.reverse H.f).eval w⁻¹) := by
    have hOpen1 : IsOpen (((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :=
      (affineChartProjX (H := H) a hpY).open_target
    have hOpen2 : IsOpen ({w : ℂ | w ≠ 0}) := isOpen_compl_singleton
    have hOpen : IsOpen (((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target ∩ {w | w ≠ 0}) :=
      hOpen1.inter hOpen2
    have hMem : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target ∩ {w | w ≠ 0} :=
      ⟨hz, hzNZ⟩
    refine eventually_of_mem (hOpen.mem_nhds hMem) ?_
    rintro w ⟨hwt, hwNZ⟩
    show ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = (Polynomial.reverse H.f).eval w⁻¹
    have hsymm_sq : ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w))^2 =
        H.f.eval w := by
      have hAct : ((squareLocalHomeomorph (H := H) a hpY) : ℂ → ℂ)
          ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w)) =
          ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w))^2 := by
        simp [squareLocalHomeomorph]
      have hRight := (squareLocalHomeomorph (H := H) a hpY).right_inv
        (show H.f.eval w ∈ (squareLocalHomeomorph (H := H) a hpY).target from hwt)
      rw [hAct] at hRight; exact hRight
    rw [mul_pow, hsymm_sq]
    have hpow_eq : (w⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = w⁻¹ ^ H.f.natDegree := by
      rw [← pow_mul]
      congr 1
      have hev : ¬ Odd H.f.natDegree := hf.out
      have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hev
      obtain ⟨m, hm⟩ := heven; omega
    rw [hpow_eq]
    exact (reverse_eval_inv_eq w hwNZ).symm
  have h_revs_deriv : HasDerivAt (fun w : ℂ => (Polynomial.reverse H.f).eval w⁻¹)
      ((Polynomial.reverse H.f).derivative.eval z⁻¹ * (-(z^2)⁻¹)) z := by
    have h2 := (Polynomial.reverse H.f).hasDerivAt z⁻¹
    exact h2.comp z hinv_deriv
  have hTsq_deriv_explicit := hT_deriv.fun_pow 2
  have hTsq_deriv_implicit : HasDerivAt
      (fun w : ℂ => ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2)) ^ 2)
      ((Polynomial.reverse H.f).derivative.eval z⁻¹ * (-(z^2)⁻¹)) z :=
    h_revs_deriv.congr_of_eventuallyEq hT_sq_eventually
  -- Uniqueness of derivative for T².
  have h_unique := hTsq_deriv_explicit.unique hTsq_deriv_implicit
  push_cast at h_unique
  simp only [pow_one] at h_unique
  -- h_unique : 2 * v * T'_explicit = (H.f.reverse)'(z⁻¹) * -(z²)⁻¹.
  -- Multiply both sides by z² (manually to avoid field_simp converting z⁻¹ inside eval):
  have h_unique_z2 :
      2 * v * (H.f.derivative.eval z / (2 * y) * z⁻¹ ^ (H.f.natDegree / 2) +
        y * (((H.f.natDegree / 2 : ℕ) : ℂ) * z⁻¹ ^ ((H.f.natDegree / 2) - 1) *
          -(z^2)⁻¹)) * z^2 =
      -(Polynomial.reverse H.f).derivative.eval z⁻¹ := by
    have step1 := congr_arg (fun e => e * z^2) h_unique
    simp only at step1
    rw [show ((Polynomial.reverse H.f).derivative.eval z⁻¹ * -(z^2)⁻¹) * z^2 =
        -((Polynomial.reverse H.f).derivative.eval z⁻¹ * ((z^2)⁻¹ * z^2)) from by ring,
        inv_mul_cancel₀ hzsqNZ, mul_one] at step1
    convert step1 using 1
  -- fderiv computation via Filter.EventuallyEq.fderiv_eq.
  have hFderivEq :
      fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 =
        H.f.derivative.eval z / (2 * y) * z⁻¹ ^ (H.f.natDegree / 2) +
          y * (((H.f.natDegree / 2 : ℕ) : ℂ) * z⁻¹ ^ ((H.f.natDegree / 2) - 1) *
            -(z^2)⁻¹) := by
    rw [hExtCoe', hExtSymm]
    have hEqOnSrc : (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) =ᶠ[nhds z]
      (fun w : ℂ => (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2)) := by
      refine eventually_of_mem (hOverlapOpen.mem_nhds hzInOverlap) ?_
      intro w hw
      exact chart_transition_eq_X_V a hpY b hpX_b hpYn_b hw
    show fderiv ℂ (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) z 1 = _
    rw [Filter.EventuallyEq.fderiv_eq hEqOnSrc]
    change deriv (fun w : ℂ => (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval w) *
        w⁻¹ ^ (H.f.natDegree / 2)) z = _
    exact hT_deriv.deriv
  -- LHS coefficient: g_aff(z) / y.
  have hLHS : hyperellipticEvenCoeff (H := H) g_aff g_inf q z = g_aff.eval z / y := by
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) z = _
    rw [hQ]
    show hyperellipticAffineCoeff (H := H) g_aff a z = _
    have h1 : hyperellipticAffineCoeff (H := H) g_aff a z = affineProjXCoeff g_aff a hpY z := by
      simp [hyperellipticAffineCoeff, hpY]
    rw [h1, affineProjXCoeff_eq_on_target g_aff a hpY hz]
  -- RHS coefficient at v: bb is in chart_b.source (projY in reverseData), so coeff = 2 g_inf(z⁻¹) / (H.f.reverse)'(z⁻¹).
  have hbb1_target_proj : bb.val.1 ∈
      (polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).source := hbb_src
  have hzInv_in_source : z⁻¹ ∈
      (polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).source := by
    rw [← hbb1]; exact hbb1_target_proj
  have hf'_red_NZ : (Polynomial.reverse H.f).derivative.eval z⁻¹ ≠ 0 :=
    polynomialLocalHomeomorph_no_critical_in_source
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b hzInv_in_source
  have hv_in_target : v ∈ ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)).target := by
    have h1 : ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)) bb ∈
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)).target :=
      OpenPartialHomeomorph.map_source _ hbb_src
    rw [show ((affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)) bb = bb.val.2 from rfl,
      hbb2] at h1
    exact h1
  -- polynomialLocalHomeomorph.symm(v²) = z⁻¹ via left_inv on z⁻¹ ∈ source + (H.f.reverse).eval z⁻¹ = v².
  have hxb_eq : (polynomialLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).symm (v^2) = z⁻¹ := by
    have hv_sq_eq : v^2 = (Polynomial.reverse H.f).eval z⁻¹ := by
      show (y * z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = _
      have hsymm_sq : y^2 = H.f.eval z := by
        have hAct : ((squareLocalHomeomorph (H := H) a hpY) : ℂ → ℂ) y = y^2 := by
          simp [squareLocalHomeomorph]
        have hRight := (squareLocalHomeomorph (H := H) a hpY).right_inv hz
        rw [hAct] at hRight
        show y^2 = H.f.eval z
        exact hRight
      rw [mul_pow, hsymm_sq]
      have hpow_eq : (z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = z⁻¹ ^ H.f.natDegree := by
        rw [← pow_mul]
        congr 1
        have hev : ¬ Odd H.f.natDegree := hf.out
        have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hev
        obtain ⟨m, hm⟩ := heven; omega
      rw [hpow_eq]
      exact (reverse_eval_inv_eq z hzNZ).symm
    rw [hv_sq_eq]
    -- (poly.symm)((H.f.reverse).eval z⁻¹) = z⁻¹ via left_inv.
    have hLeftInv := (polynomialLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).left_inv hzInv_in_source
    have hAct : ((polynomialLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) : ℂ → ℂ) z⁻¹ =
        (Polynomial.reverse H.f).eval z⁻¹ := by
      show (HyperellipticAffineInfinity.reverseData H hf.out).f.eval z⁻¹ = _
      rfl
    rw [hAct] at hLeftInv; exact hLeftInv
  have hRHScoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q' v =
      2 * g_inf.eval z⁻¹ / (Polynomial.reverse H.f).derivative.eval z⁻¹ := by
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) v = _
    rw [hQ']
    show hyperellipticAffineInfinityCoeff (H := H) g_inf b v = _
    have h1 : hyperellipticAffineInfinityCoeff (H := H) g_inf b v =
        hyperellipticAffineCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b v := rfl
    rw [h1]
    have h2 : hyperellipticAffineCoeff
        (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b v =
        affineProjYCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpX_b v := by
      show (if hpY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) then
          affineProjXCoeff (H := HyperellipticAffineInfinity.reverseData H hf.out)
            g_inf b hpY v
        else affineProjYCoeff (H := HyperellipticAffineInfinity.reverseData H hf.out)
          g_inf b _ v) = _
      rw [dif_neg hpYn_b]
    rw [h2, affineProjYCoeff_eq_on_target
      (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpX_b hv_in_target]
    rw [hxb_eq]
    rfl
  -- Algebraic close.
  rw [hLHS, hQ'apply, hRHScoeff, hFderivEq]
  rw [hGluing]
  -- Goal: g_aff(z)/y =
  --       (2 * (infReverse H g_aff)(z⁻¹) / (H.f.reverse)'(z⁻¹)) *
  --       (T'_explicit)
  -- Via cross_summand_cocycle_coord and h_unique_z2.
  have hcore := cross_summand_cocycle_coord (H := H) (g_aff := g_aff)
    hDeg hzNZ hyNZ rfl
  -- hcore : g_aff(z)/y = (infReverse H g_aff)(z⁻¹)/v · (-(z²)⁻¹)
  -- We have h_unique_z2 : 2 * v * T'_explicit * z² = -(H.f.reverse)'(z⁻¹).
  -- T'_explicit (call this E) = (f'(z)/(2y)) * z⁻¹^(g+1) + y * ((g+1) * z⁻¹^g * (-(z²)⁻¹)).
  -- Goal: g_aff(z)/y = (2 g_inf(z⁻¹)/(H.f.reverse)'(z⁻¹)) * E
  -- Multiply both sides by (H.f.reverse)'(z⁻¹) * v * z²:
  --   g_aff(z) (H.f.reverse)'(z⁻¹) v z² / y = 2 g_inf(z⁻¹) v z² E
  -- Substitute 2 v z² E = -(H.f.reverse)'(z⁻¹) (from h_unique_z2 rearranged):
  --   = -g_inf(z⁻¹) (H.f.reverse)'(z⁻¹)
  -- So: g_aff(z) v z² / y = -g_inf(z⁻¹).
  -- This is cross_summand_cocycle_coord rearranged.
  set E : ℂ := H.f.derivative.eval z / (2 * y) * z⁻¹ ^ (H.f.natDegree / 2) +
    y * (((H.f.natDegree / 2 : ℕ) : ℂ) * z⁻¹ ^ ((H.f.natDegree / 2) - 1) *
      -(z^2)⁻¹) with hE_def
  -- Goal (with E): g_aff(z)/y = (2 (infReverse H g_aff)(z⁻¹)/(H.f.reverse)'(z⁻¹)) * E.
  show g_aff.eval z / y =
    2 * (infReverse H g_aff).eval z⁻¹ / (Polynomial.reverse H.f).derivative.eval z⁻¹ * E
  -- h_unique_z2 (re-stated): 2 * v * E * z² = -(H.f.reverse)'(z⁻¹).
  have h_step : 2 * v * E * z^2 = -(Polynomial.reverse H.f).derivative.eval z⁻¹ := by
    have := h_unique_z2
    show 2 * v * E * z^2 = _
    linear_combination this
  -- Cocycle equation derivation: clear denominators manually to avoid field_simp
  -- introducing `1/z` form that breaks ring inside `eval`.
  -- From hcore (multiplied by y * v * z²): g_aff(z) * v * z² = -y * (infReverse)(z⁻¹).
  have h_cross : g_aff.eval z * v * z^2 = -(y * (infReverse H g_aff).eval z⁻¹) := by
    have := hcore
    rw [div_eq_iff hyNZ] at this
    rw [this, hv_def]
    field_simp
  -- Cocycle goal: g_aff(z)/y = (2 * (infReverse)(z⁻¹) / (H.f.reverse)'(z⁻¹)) * E
  -- Clear denominators: multiply both sides by y * (H.f.reverse)'(z⁻¹).
  rw [div_eq_iff hyNZ]
  -- Goal: g_aff(z) = (2 * (infReverse)(z⁻¹) / (H.f.reverse)'(z⁻¹) * E) * y
  rw [show (2 * (infReverse H g_aff).eval z⁻¹ /
        (Polynomial.reverse H.f).derivative.eval z⁻¹ * E) * y =
      (2 * (infReverse H g_aff).eval z⁻¹ * E * y) /
        (Polynomial.reverse H.f).derivative.eval z⁻¹ from by ring]
  rw [eq_div_iff hf'_red_NZ]
  -- Goal: g_aff(z) * (H.f.reverse)'(z⁻¹) = 2 * (infReverse)(z⁻¹) * E * y
  -- From h_step: (H.f.reverse)'(z⁻¹) = -(2 v E z²).
  -- From h_cross: y * (infReverse)(z⁻¹) = -(g_aff(z) * v * z²).
  have h_step' : (Polynomial.reverse H.f).derivative.eval z⁻¹ = -(2 * v * E * z^2) := by
    linear_combination h_step
  have h_cross' : y * (infReverse H g_aff).eval z⁻¹ = -(g_aff.eval z * v * z^2) := by
    linear_combination h_cross
  rw [h_step']
  linear_combination -2 * E * h_cross'

/-! ### Chart transition formula (projY × projV sub-case)

For `a ∉ smoothLocusY` (so `chart_a = affineChartProjY` at affine
branch point) and `b ∉ smoothLocusY` of reverseData but
`b ∈ smoothLocusX` (so `chart_b = affineChartProjY` at infinity branch
point), the chart transition is
`w ↦ w · x_a(w)⁻¹^(g+1)` where `x_a(w) = polynomialLocalHomeomorph.symm(w²)`. -/
private lemma chart_transition_eq_Y_V
    [hf : Fact (¬ Odd H.f.natDegree)]
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpX_b : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn_b : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    {w : ℂ}
    (hw : w ∈ ((affineLiftChart H hf.out a).symm.trans
        (infinityLiftChart H hf.out b)).source) :
    (infinityLiftChart H hf.out b) ((affineLiftChart H hf.out a).symm w) =
      w * ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ ^
        (H.f.natDegree / 2) := by
  have hwt : w ∈ (affineLiftChart H hf.out a).target := hw.1
  have hws : (affineLiftChart H hf.out a).symm w ∈
      (infinityLiftChart H hf.out b).source := hw.2
  simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target] at hwt
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_symm, affineLiftChart] at hws
  rw [affineChartAt_of_not_mem_smoothLocusY a hpYn] at hwt hws
  obtain ⟨bb, hbb_src, hbb_eq⟩ := hws
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_not_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpYn_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjY (H := H) a hpX).symm w)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hwNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  have hbb2 : bb.val.2 =
      w * ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ ^
        (H.f.natDegree / 2) := by
    rw [hbb]; simp only [affineGluingImage_val_snd]
    rw [affineChartProjY_symm_apply_fst a hpX hwt,
        affineChartProjY_symm_apply_snd a hpX hwt]
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
      w * ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ ^
        (H.f.natDegree / 2)
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [show (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b) =
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_not_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpYn_b]
  exact hbb2

/-! ### Cross-summand cocycle: projY × projV sub-case (real proof) -/

theorem cocycle_inl_inr_smoothLocusXNotY_smoothLocusXNotY
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ)
    (hGluing : g_inf = infReverse H g_aff)
    (hDeg : g_aff.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hpX_b : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn_b : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
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
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) :
        OpenPartialHomeomorph _ _) from
    affineChartAt_of_not_mem_smoothLocusY (H := HyperellipticAffineInfinity.reverseData H hf.out)
      b hpYn_b] at hbb_src
  have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
      (Sum.inl ((affineChartProjY (H := H) a hpX).symm z)) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
  obtain ⟨hxNZ, hbb⟩ := proj_inl_eq_proj_inr_iff hbb_eq'
  set x_a : ℂ := (polynomialLocalHomeomorph (H := H) a hpX).symm (z ^ 2) with hx_a_def
  have hx_aNZ : x_a ≠ 0 := by
    rw [affineChartProjY_symm_apply_fst a hpX hz] at hxNZ
    simpa [x_a] using hxNZ
  have hx_aSrc : x_a ∈ (polynomialLocalHomeomorph (H := H) a hpX).source := by
    have h_target : z^2 ∈ (polynomialLocalHomeomorph (H := H) a hpX).target := by
      simpa [affineChartProjY] using hz
    exact (polynomialLocalHomeomorph (H := H) a hpX).map_target h_target
  have hf'NZ : H.f.derivative.eval x_a ≠ 0 :=
    polynomialLocalHomeomorph_no_critical_in_source a hpX hx_aSrc
  have hbb1 : bb.val.1 = x_a⁻¹ := by
    rw [hbb]; simp only [affineGluingImage_val_fst]
    simp only [affineChartProjY_symm_apply_fst a hpX hz, x_a]
  set v : ℂ := z * x_a⁻¹ ^ (H.f.natDegree / 2) with hv_def
  have hbb2 : bb.val.2 = v := by
    rw [hbb]; simp only [affineGluingImage_val_snd]
    rw [affineChartProjY_symm_apply_fst a hpX hz, affineChartProjY_symm_apply_snd a hpX hz]
  have hQ'apply :
      (extChartAt 𝓘(ℂ, ℂ) q') ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = v := by
    rw [hExtCoe', hExtSymm]
    exact chart_transition_eq_Y_V a hpX hpYn b hpX_b hpYn_b hzInOverlap
  have hf_x_a : H.f.eval x_a = z^2 := by
    have h_target : z^2 ∈ (polynomialLocalHomeomorph (H := H) a hpX).target := by
      simpa [affineChartProjY] using hz
    have h_right := (polynomialLocalHomeomorph (H := H) a hpX).right_inv h_target
    have h_act : ((polynomialLocalHomeomorph (H := H) a hpX) : ℂ → ℂ) x_a = H.f.eval x_a := by
      simp [polynomialLocalHomeomorph, x_a]
    rw [h_act] at h_right; exact h_right
  have hx_a_deriv : HasDerivAt
      (fun w : ℂ => (polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
      (2 * z / H.f.derivative.eval x_a) z :=
    affineChartProjY_to_projX_transition_hasDerivAt (H := H) a hpX hz
  have hx_a_inv_deriv : HasDerivAt
      (fun w : ℂ => ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹)
      (-(2 * z / H.f.derivative.eval x_a) / x_a^2) z := by
    have := hx_a_deriv.fun_inv hx_aNZ
    convert this using 1
  have hx_a_inv_pow_deriv : HasDerivAt
      (fun w : ℂ => ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ ^
        (H.f.natDegree / 2))
      ((H.f.natDegree / 2 : ℕ) * x_a⁻¹ ^ ((H.f.natDegree / 2) - 1) *
        (-(2 * z / H.f.derivative.eval x_a) / x_a^2)) z := by
    have := hx_a_inv_deriv.fun_pow (H.f.natDegree / 2)
    convert this using 1
  have hid_deriv : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have hT_deriv : HasDerivAt
      (fun w : ℂ => w * ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ ^
        (H.f.natDegree / 2))
      (1 * x_a⁻¹ ^ (H.f.natDegree / 2) + z * ((H.f.natDegree / 2 : ℕ) *
        x_a⁻¹ ^ ((H.f.natDegree / 2) - 1) *
        (-(2 * z / H.f.derivative.eval x_a) / x_a^2))) z :=
    hid_deriv.fun_mul hx_a_inv_pow_deriv
  have hFderivEq :
      fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 =
        1 * x_a⁻¹ ^ (H.f.natDegree / 2) +
          z * (((H.f.natDegree / 2 : ℕ) : ℂ) * x_a⁻¹ ^ ((H.f.natDegree / 2) - 1) *
            (-(2 * z / H.f.derivative.eval x_a) / x_a^2)) := by
    rw [hExtCoe', hExtSymm]
    have hEqOnSrc : (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) =ᶠ[nhds z]
      (fun w : ℂ => w * ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))⁻¹ ^
        (H.f.natDegree / 2)) := by
      refine eventually_of_mem (hOverlapOpen.mem_nhds hzInOverlap) ?_
      intro w hw
      exact chart_transition_eq_Y_V a hpX hpYn b hpX_b hpYn_b hw
    show fderiv ℂ (fun w => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) z 1 = _
    rw [Filter.EventuallyEq.fderiv_eq hEqOnSrc]
    change deriv (fun w : ℂ => w * ((polynomialLocalHomeomorph (H := H) a hpX).symm
      (w ^ 2))⁻¹ ^ (H.f.natDegree / 2)) z = _
    exact hT_deriv.deriv
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
  have hbb1_target_proj : bb.val.1 ∈
      (polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).source := hbb_src
  have hzInv_in_source : x_a⁻¹ ∈
      (polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).source := by
    rw [← hbb1]; exact hbb1_target_proj
  have hf'_red_NZ : (Polynomial.reverse H.f).derivative.eval x_a⁻¹ ≠ 0 :=
    polynomialLocalHomeomorph_no_critical_in_source
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b hzInv_in_source
  have hv_in_target : v ∈ ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)).target := by
    have h1 : ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)) bb ∈
      ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)).target :=
      OpenPartialHomeomorph.map_source _ hbb_src
    rw [show ((affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b)) bb = bb.val.2 from rfl,
      hbb2] at h1
    exact h1
  have hxb_eq : (polynomialLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).symm (v^2) = x_a⁻¹ := by
    have hv_sq_eq : v^2 = (Polynomial.reverse H.f).eval x_a⁻¹ := by
      show (z * x_a⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = _
      rw [mul_pow]
      have hpow_eq : (x_a⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = x_a⁻¹ ^ H.f.natDegree := by
        rw [← pow_mul]
        congr 1
        have hev : ¬ Odd H.f.natDegree := hf.out
        have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hev
        obtain ⟨m, hm⟩ := heven; omega
      rw [hpow_eq]
      rw [show z^2 = H.f.eval x_a from hf_x_a.symm]
      exact (reverse_eval_inv_eq x_a hx_aNZ).symm
    rw [hv_sq_eq]
    have hLeftInv := (polynomialLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b).left_inv hzInv_in_source
    have hAct : ((polynomialLocalHomeomorph
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX_b) : ℂ → ℂ) x_a⁻¹ =
        (Polynomial.reverse H.f).eval x_a⁻¹ := by
      show (HyperellipticAffineInfinity.reverseData H hf.out).f.eval x_a⁻¹ = _
      rfl
    rw [hAct] at hLeftInv; exact hLeftInv
  have hRHScoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q' v =
      2 * g_inf.eval x_a⁻¹ / (Polynomial.reverse H.f).derivative.eval x_a⁻¹ := by
    show (match Quotient.out q' with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b) v = _
    rw [hQ']
    show hyperellipticAffineInfinityCoeff (H := H) g_inf b v = _
    have h1 : hyperellipticAffineInfinityCoeff (H := H) g_inf b v =
        hyperellipticAffineCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b v := rfl
    rw [h1]
    have h2 : hyperellipticAffineCoeff
        (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b v =
        affineProjYCoeff
          (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpX_b v := by
      show (if hpY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) then
          affineProjXCoeff (H := HyperellipticAffineInfinity.reverseData H hf.out)
            g_inf b hpY v
        else affineProjYCoeff (H := HyperellipticAffineInfinity.reverseData H hf.out)
          g_inf b _ v) = _
      rw [dif_neg hpYn_b]
    rw [h2, affineProjYCoeff_eq_on_target
      (H := HyperellipticAffineInfinity.reverseData H hf.out) g_inf b hpX_b hv_in_target]
    rw [hxb_eq]
    rfl
  have h_revs := reverse_derivative_eval_inv_mul_pow (H := H) x_a hx_aNZ
  rw [hf_x_a] at h_revs
  have h_reflect : g_aff.eval x_a = -(infReverse H g_aff).eval x_a⁻¹ * x_a ^ (H.f.natDegree / 2 - 2) :=
    eval_eq_neg_infReverse_eval_inv_mul_pow H hDeg hx_aNZ
  have hx_a_sq_NZ : x_a^2 ≠ 0 := pow_ne_zero _ hx_aNZ
  have hx_a_N_NZ : x_a^H.f.natDegree ≠ 0 := pow_ne_zero _ hx_aNZ
  have hev : ¬ Odd H.f.natDegree := hf.out
  have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hev
  have hge2 : H.f.natDegree / 2 ≥ 2 := by
    have hd := H.h_degree
    obtain ⟨m, hm⟩ := heven; omega
  have hNcast : (H.f.natDegree : ℂ) = 2 * (H.f.natDegree / 2 : ℕ) := by
    have : H.f.natDegree = 2 * (H.f.natDegree / 2) := by
      obtain ⟨m, hm⟩ := heven; omega
    exact_mod_cast this
  -- Cleared cocycle identity:
  --   gA · fpR · x_a^N = gI · fp · x_a^(N/2) - N · z² · gI · x_a^(N/2 - 1).
  have h_cleared :
      g_aff.eval x_a * (Polynomial.reverse H.f).derivative.eval x_a⁻¹ * x_a^H.f.natDegree =
      (infReverse H g_aff).eval x_a⁻¹ * H.f.derivative.eval x_a *
        x_a^(H.f.natDegree / 2) -
      (H.f.natDegree : ℂ) * z^2 * (infReverse H g_aff).eval x_a⁻¹ *
        x_a^(H.f.natDegree / 2 - 1) := by
    have hp1 : x_a^(H.f.natDegree / 2) = x_a^(H.f.natDegree / 2 - 2) * x_a^2 := by
      rw [← pow_add]; congr 1; omega
    have hp2 : x_a^(H.f.natDegree / 2 - 1) = x_a^(H.f.natDegree / 2 - 2) * x_a := by
      have h_eq : H.f.natDegree / 2 - 1 = (H.f.natDegree / 2 - 2) + 1 := by omega
      rw [h_eq, pow_succ]
    rw [hp1, hp2]
    linear_combination
      g_aff.eval x_a * h_revs +
      ((H.f.natDegree : ℂ) * z^2 * x_a - H.f.derivative.eval x_a * x_a^2) * h_reflect
  -- Helper: x_a⁻¹^(N/2) * x_a^N = x_a^(N/2).
  have h_inv_g_mul : x_a⁻¹^(H.f.natDegree / 2) * x_a^H.f.natDegree =
      x_a^(H.f.natDegree / 2) := by
    have h_split_N : x_a^H.f.natDegree =
        x_a^(H.f.natDegree / 2) * x_a^(H.f.natDegree / 2) := by
      rw [← pow_add]
      congr 1; obtain ⟨m, hm⟩ := heven; omega
    rw [h_split_N, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx_aNZ, one_pow, one_mul]
  -- Helper: x_a⁻¹^(N/2-1) * x_a^(N-2) = x_a^(N/2-1).
  have h_inv_g_pred_mul_Nm2 : x_a⁻¹^(H.f.natDegree / 2 - 1) * x_a^(H.f.natDegree - 2) =
      x_a^(H.f.natDegree / 2 - 1) := by
    have h_split_Nm2 : x_a^(H.f.natDegree - 2) =
        x_a^(H.f.natDegree / 2 - 1) * x_a^(H.f.natDegree / 2 - 1) := by
      rw [← pow_add]
      congr 1; obtain ⟨m, hm⟩ := heven; omega
    rw [h_split_Nm2, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx_aNZ, one_pow, one_mul]
  have h_split_N_in_2 : x_a^H.f.natDegree = x_a^2 * x_a^(H.f.natDegree - 2) := by
    rw [← pow_add]; congr 1; omega
  -- E · fp · x_a^N in cleared form:
  --   E · fp · x_a^N = fp · x_a^(N/2) - N · z² · x_a^(N/2 - 1).
  have hEfpxaN :
      (1 * x_a⁻¹^(H.f.natDegree / 2) + z * (((H.f.natDegree / 2 : ℕ) : ℂ) *
        x_a⁻¹^(H.f.natDegree / 2 - 1) *
        (-(2 * z / H.f.derivative.eval x_a) / x_a^2))) *
      H.f.derivative.eval x_a * x_a^H.f.natDegree =
      H.f.derivative.eval x_a * x_a^(H.f.natDegree / 2) -
        (H.f.natDegree : ℂ) * z^2 * x_a^(H.f.natDegree / 2 - 1) := by
    -- LHS = fp · x_a^N · x_a⁻¹^(N/2) + z · ↑(N/2) · x_a⁻¹^(N/2-1) · (-(2z/fp)/x_a²) · fp · x_a^N.
    -- The second term simplifies via fp/fp = 1 and x_a^N/x_a² = x_a^(N-2).
    rw [show (1 * x_a⁻¹^(H.f.natDegree / 2) + z * (((H.f.natDegree / 2 : ℕ) : ℂ) *
        x_a⁻¹^(H.f.natDegree / 2 - 1) *
        (-(2 * z / H.f.derivative.eval x_a) / x_a^2))) *
      H.f.derivative.eval x_a * x_a^H.f.natDegree =
      H.f.derivative.eval x_a * (x_a⁻¹^(H.f.natDegree / 2) * x_a^H.f.natDegree) +
      (-((((H.f.natDegree / 2 : ℕ) : ℂ) * 2 * z^2) *
        (x_a⁻¹^(H.f.natDegree / 2 - 1) * x_a^(H.f.natDegree - 2)) *
        (H.f.derivative.eval x_a / H.f.derivative.eval x_a) *
        (x_a^2 / x_a^2))) from by
      rw [h_split_N_in_2]; field_simp]
    rw [h_inv_g_mul, h_inv_g_pred_mul_Nm2,
      div_self hf'NZ, div_self hx_a_sq_NZ, mul_one, mul_one]
    rw [hNcast]
    ring
  -- Now derive the cocycle.
  rw [hLHS, hQ'apply, hRHScoeff, hFderivEq, hGluing]
  rw [div_mul_eq_mul_div, div_eq_div_iff hf'NZ hf'_red_NZ]
  refine mul_right_cancel₀ hx_a_N_NZ ?_
  -- Goal: 2 * gA * fpR * x_a^N = (2 * gI * E_explicit * fp) * x_a^N.
  linear_combination
    2 * h_cleared +
    (-2 * (infReverse H g_aff).eval x_a⁻¹) * hEfpxaN

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
