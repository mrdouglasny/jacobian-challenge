/-
# Smooth projective plane curves

A smooth projective plane curve is `X = {[x : y : z] ∈ ℙ² | F(x, y, z) = 0}`
where `F ∈ ℂ[x, y, z]` is a homogeneous polynomial of degree `d ≥ 1`
whose gradient `∇F` has no common zero with `F` on `ℂ³ \ {0}` (smoothness).

**Genus.** For smooth `X` of degree `d ≥ 3`: `g = (d - 1)(d - 2) / 2`
(Plücker formula). For `d = 1` (line) or `d = 2` (conic): `g = 0`.

## Scope of this module (refactored 2026-04-23)

- `HomogeneousPoly n d`: a homogeneous polynomial of degree `d` in
  `n + 1` variables.
- `PlaneCurveData`: `F` with smoothness + `deg F ≥ 1` hypotheses.
- `PlaneCurveAffine`: the affine patch `{F(x, y, 1) = 0}` in `ℂ²`.
- **`PlaneCurve H := OnePoint (PlaneCurveAffine H)`** — real `def` via
  one-point compactification (2026-04-23). This glues the points at
  infinity (where `z = 0`) into a single point, which is correct when
  `X ∩ {z = 0}` is a single projective point, lossy otherwise (the
  atlas work needs to handle this case properly).
- Topology / T2 / compact / connected / nonempty instances are real
  `instance`s via OnePoint infrastructure (+ subsidiary axioms for
  affine-level connectedness and noncompactness).
- `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` stay **axiomatic** (atlas
  construction; classical but nontrivial).
-/
import Mathlib

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open OnePoint

/-- A homogeneous polynomial of degree `d` in `n + 1` variables over `ℂ`. -/
structure HomogeneousPoly (n d : ℕ) where
  /-- The underlying polynomial in `(Fin (n + 1))`-indexed variables. -/
  val : MvPolynomial (Fin (n + 1)) ℂ
  /-- Homogeneity of degree `d`. -/
  homogeneous : val.IsHomogeneous d

/-- Data specifying a smooth projective plane curve `{F = 0} ⊂ ℙ²`. -/
structure PlaneCurveData where
  /-- Degree of the defining polynomial, `≥ 1`. -/
  d : ℕ
  h_deg : 1 ≤ d
  /-- The defining homogeneous polynomial `F ∈ ℂ[x, y, z]` of degree `d`. -/
  F : HomogeneousPoly 2 d
  /-- Smoothness: on `ℂ³ \ {0}`, `F = 0` implies some partial derivative
  is nonzero. -/
  h_smooth : ∀ v : Fin 3 → ℂ, v ≠ 0 → F.val.eval v = 0 →
    (∃ i : Fin 3, (MvPolynomial.pderiv i F.val).eval v ≠ 0)
  /-- Irreducibility: `{F = 0}` is an irreducible curve — the standard meaning of
  a "smooth plane curve". Rules out reducible loci (e.g. `F = xy`, two lines)
  whose affine patch can be disconnected. -/
  h_irreducible : Irreducible F.val
  /-- The curve is **not** the line at infinity `{z = 0}` (equivalently `z ∤ F`).
  Together with irreducibility this guarantees the `z = 1` affine patch is
  nonempty, connected, and noncompact — closing the `F = z` soundness hole
  (where the patch is empty). The third variable `z` is `MvPolynomial.X 2`. -/
  h_not_at_infinity : ¬ (MvPolynomial.X (2 : Fin 3) ∣ F.val)

namespace PlaneCurveData

/-- The genus of a smooth projective plane curve of degree `d`:
`g = (d - 1)(d - 2) / 2` (Plücker). -/
def genus (H : PlaneCurveData) : ℕ := (H.d - 1) * (H.d - 2) / 2

end PlaneCurveData

/-- **Affine plane curve**: the subtype of `ℂ²` cut out by the
dehomogenization `F(x, y, 1) = 0`. -/
def PlaneCurveAffine (H : PlaneCurveData) : Type :=
  { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 }

namespace PlaneCurveAffine

variable {H : PlaneCurveData}

instance : TopologicalSpace (PlaneCurveAffine H) :=
  inferInstanceAs (TopologicalSpace
    { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 })

instance : T2Space (PlaneCurveAffine H) :=
  inferInstanceAs (T2Space
    { p : ℂ × ℂ // H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 })

/-- The affine locus is closed: preimage of `0` under the continuous
map `(x, y) ↦ F(x, y, 1)`. -/
theorem isClosed_carrier (H : PlaneCurveData) :
    IsClosed { p : ℂ × ℂ | H.F.val.eval ![p.1, p.2, (1 : ℂ)] = 0 } := by
  have hcont : Continuous (fun p : ℂ × ℂ =>
      H.F.val.eval ![p.1, p.2, (1 : ℂ)]) := by
    have hvec : Continuous (fun p : ℂ × ℂ => (![p.1, p.2, (1 : ℂ)] : Fin 3 → ℂ)) := by
      refine continuous_pi (fun i => ?_)
      fin_cases i
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_const
    exact (MvPolynomial.continuous_eval H.F.val).comp hvec
  exact isClosed_eq hcont continuous_const

/-- Local compactness inherited via the closed-subtype route. -/
instance : LocallyCompactSpace (PlaneCurveAffine H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### The affine-patch axiom layer — soundness restored 2026-06-04

These three axioms were **false as stated** for a curve lying in the line at
infinity `z = 0` (e.g. `F = z`: the `z = 1` patch `{F(x,y,1)=0} = ∅`, which is not
nonempty, not connected, and — being compact — not noncompact). That hole is now
closed at the **data** level: `PlaneCurveData` carries `h_irreducible` and
`h_not_at_infinity` (`z ∤ F`). For irreducible `F` with `z ∤ F` the curve is not
the line at infinity, it meets the `z = 1` chart, and (being a smooth irreducible
projective curve minus finitely many points at infinity) its affine patch is
genuinely nonempty, connected, and noncompact — so the statements below are
**true** (still axioms = unproven, but sound). Non-vacuous: e.g. the smooth conic
`F = x²+y²+z²` satisfies every field. -/

private abbrev NonZVar : Type := {i : Fin 3 // i ≠ (2 : Fin 3)}

private noncomputable def zAsOption (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Option NonZVar) ℂ :=
  MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 3)).symm F

private noncomputable def zPolynomial (F : MvPolynomial (Fin 3) ℂ) :
    Polynomial (MvPolynomial NonZVar ℂ) :=
  MvPolynomial.optionEquivLeft ℂ NonZVar (zAsOption F)

private noncomputable def affinePolynomial (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial NonZVar ℂ :=
  Polynomial.eval 1 (zPolynomial F)

private lemma exists_eval_eq_zero_of_not_isUnit_mvPolynomial
    {σ : Type*} [Finite σ] (P : MvPolynomial σ ℂ) (hP : ¬ IsUnit P) :
    ∃ x : σ → ℂ, MvPolynomial.eval x P = 0 := by
  let I : Ideal (MvPolynomial σ ℂ) := Ideal.span ({P} : Set (MvPolynomial σ ℂ))
  by_contra hzero
  have : MvPolynomial.zeroLocus ℂ I = (∅ : Set (σ → ℂ)) := by
    ext x
    constructor
    · intro hx
      have : MvPolynomial.aeval x P = 0 := hx P (Ideal.subset_span (by simp))
      have : MvPolynomial.eval x P = 0 := by assumption
      exact (hzero ⟨x, this⟩).elim
    · simp
  have hrad : I.radical = ⊤ := by
    calc
      I.radical = MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
        simp only [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
      _ = MvPolynomial.vanishingIdeal ℂ (∅ : Set (σ → ℂ)) := by rw [this]
      _ = ⊤ := MvPolynomial.vanishingIdeal_empty
  have : I = ⊤ := (Ideal.radical_eq_top).mp hrad
  have : (1 : MvPolynomial σ ℂ) ∈ I := by
    rw [this]
    exact Submodule.mem_top
  rw [Ideal.mem_span_singleton] at this
  exact hP (isUnit_of_dvd_one this)

private lemma affinePolynomial_eval_eq (F : MvPolynomial (Fin 3) ℂ) (x : NonZVar → ℂ) :
    MvPolynomial.eval x (affinePolynomial F) =
      MvPolynomial.eval (fun i : Fin 3 =>
        if h : i = (2 : Fin 3) then (1 : ℂ) else x ⟨i, h⟩) F := by
  unfold affinePolynomial zPolynomial zAsOption
  rw [← Polynomial.eval_one_map (MvPolynomial.eval x)
    ((MvPolynomial.optionEquivLeft ℂ NonZVar)
      ((MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 3)).symm) F))]
  rw [← MvPolynomial.optionEquivLeft_elim_eval]
  rw [MvPolynomial.eval_rename]
  have hfun :
      ((fun o : Option NonZVar ↦ o.elim (1 : ℂ) x) ∘
          (Equiv.optionSubtypeNe (2 : Fin 3)).symm) =
        (fun i : Fin 3 ↦ if h : i = (2 : Fin 3) then (1 : ℂ) else x ⟨i, h⟩) := by
    funext i
    by_cases h : i = (2 : Fin 3) <;> simp [*]
  simp [*]

private lemma optionElim_degree (u : NonZVar →₀ ℕ) (k : ℕ) :
    (u.optionElim k).degree = u.degree + k := by
  simp [Finsupp.degree_eq_sum, Nat.add_comm]

private lemma coeff_affinePolynomial_eq_coeff_zAsOption_zero
    {F : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hF : F.IsHomogeneous d)
    (u : NonZVar →₀ ℕ) (hu : u.degree = d) :
    MvPolynomial.coeff u (affinePolynomial F) =
      MvPolynomial.coeff (u.optionElim 0) (zAsOption F) := by
  unfold affinePolynomial zPolynomial
  rw [Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one, MvPolynomial.coeff_sum]
  trans MvPolynomial.coeff u (((MvPolynomial.optionEquivLeft ℂ NonZVar) (zAsOption F)).coeff 0)
  · refine Finset.sum_eq_single (M := ℂ) (0 : ℕ) ?_ ?_
    · intro i _hi hne
      rw [MvPolynomial.optionEquivLeft_coeff_coeff]
      have : (zAsOption F).IsHomogeneous d := by
        unfold zAsOption
        exact hF.rename_isHomogeneous
      exact this.coeff_eq_zero (by grind [optionElim_degree])
    · simp
  · rw [MvPolynomial.optionEquivLeft_coeff_coeff]

private lemma optionElim_zero_subtypeDomain_eq_mapDomain
    (m : Fin 3 →₀ ℕ) (hmz : m (2 : Fin 3) = 0) :
    (m.subtypeDomain (fun i : Fin 3 => i ≠ (2 : Fin 3))).optionElim 0 =
      m.mapDomain (Equiv.optionSubtypeNe (2 : Fin 3)).symm := by
  ext o
  cases o with simp [Finsupp.mapDomain_equiv_apply, hmz]

private lemma subtypeDomain_degree_eq_of_z_eq_zero
    {F : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hF : F.IsHomogeneous d)
    {m : Fin 3 →₀ ℕ} (hm : m ∈ F.support) (hmz : m (2 : Fin 3) = 0) :
    (m.subtypeDomain (fun i : Fin 3 => i ≠ (2 : Fin 3))).degree = d := by
  have hmdeg : m.degree = d := (hF.degree_eq_sum_deg_support hm).symm
  have hmap := congrArg Finsupp.degree (optionElim_zero_subtypeDomain_eq_mapDomain m hmz)
  rw [optionElim_degree, Nat.add_zero, Finsupp.degree_mapDomain] at hmap
  exact hmap.trans hmdeg

private lemma affinePolynomial_not_isUnit (H : PlaneCurveData) :
    ¬ IsUnit (affinePolynomial H.F.val) := by
  intro hunit
  obtain ⟨c, _hc, hc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := affinePolynomial H.F.val)).mp hunit
  have hcoeff_zero :
      ∀ m ∈ H.F.val.support, m (2 : Fin 3) = 0 → False := by
    intro m hm hmz
    let u : NonZVar →₀ ℕ := m.subtypeDomain (fun i : Fin 3 => i ≠ (2 : Fin 3))
    have hudeg : u.degree = H.d :=
      subtypeDomain_degree_eq_of_z_eq_zero H.F.homogeneous hm hmz
    have hune : u ≠ 0 := by
      intro hzero
      have : u.degree = 0 := by simp [hzero]
      have hd0 : H.d = 0 := hudeg ▸ this
      exact (Nat.not_succ_le_zero 0) (by simpa [hd0] using H.h_deg)
    have hsurvive :
        MvPolynomial.coeff u (affinePolynomial H.F.val) =
          MvPolynomial.coeff m H.F.val := by
      calc
        MvPolynomial.coeff u (affinePolynomial H.F.val)
            = MvPolynomial.coeff (u.optionElim 0) (zAsOption H.F.val) :=
              coeff_affinePolynomial_eq_coeff_zAsOption_zero H.F.homogeneous u hudeg
        _ = MvPolynomial.coeff (m.mapDomain (Equiv.optionSubtypeNe (2 : Fin 3)).symm)
              (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 3)).symm H.F.val) := by
              rw [optionElim_zero_subtypeDomain_eq_mapDomain m hmz]
              rfl
        _ = MvPolynomial.coeff m H.F.val := by
              rw [MvPolynomial.coeff_rename_mapDomain]
              exact (Equiv.optionSubtypeNe (2 : Fin 3)).symm.injective
    have hleft_zero : MvPolynomial.coeff u (affinePolynomial H.F.val) = 0 := by
      rw [hc]
      have h0u : ¬ (0 : NonZVar →₀ ℕ) = u := fun h => hune h.symm
      rw [MvPolynomial.coeff_C]
      simp [h0u]
    have : MvPolynomial.coeff m H.F.val ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    exact this (hsurvive ▸ hleft_zero)
  have :
      H.F.val ∈ Ideal.span (MvPolynomial.X '' ({(2 : Fin 3)} : Set (Fin 3))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    exact ⟨(2 : Fin 3), by simp, by
      by_contra hmz
      exact hcoeff_zero m hm (by simpa using hmz)⟩
  have : H.F.val ∈ Ideal.span ({MvPolynomial.X (2 : Fin 3)} :
        Set (MvPolynomial (Fin 3) ℂ)) := by
    simpa using this
  rw [Ideal.mem_span_singleton] at this
  exact H.h_not_at_infinity this

/-- **Axiom (NOT VERIFIED — sound under `h_irreducible` + `h_not_at_infinity`).**
The `z = 1` affine patch is nonempty: an irreducible `F` with `z ∤ F` dehomogenises
to a nonconstant `F(x,y,1)`, which has a zero over `ℂ`. -/
theorem AX_PlaneCurveAffine_nonempty (H : PlaneCurveData) :
    Nonempty (PlaneCurveAffine H) := by
  obtain ⟨x, hx⟩ :=
    exists_eval_eq_zero_of_not_isUnit_mvPolynomial (affinePolynomial H.F.val)
      (affinePolynomial_not_isUnit H)
  refine ⟨⟨(x ⟨0, by decide⟩, x ⟨1, by decide⟩), ?_⟩⟩
  rw [affinePolynomial_eval_eq H.F.val x] at hx
  have : ![x ⟨0, by decide⟩, x ⟨1, by decide⟩, 1] =
  (fun i : Fin 3 ↦ if h : i = (2 : Fin 3) then 1 else x ⟨i, h⟩) := by
    funext i
    fin_cases i <;> simp
  grind

attribute [instance] AX_PlaneCurveAffine_nonempty

/-- **Axiom (NOT VERIFIED — sound under `h_irreducible` + `h_not_at_infinity`).**
The affine patch is connected: the projective curve is connected (irreducible),
and removing the finitely many points at infinity leaves a connected real surface. -/
axiom AX_PlaneCurveAffine_connected (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_connected

/-- **Axiom (NOT VERIFIED — sound under `h_irreducible` + `h_not_at_infinity`).**
The affine patch is noncompact: by Bézout the degree-`d` curve meets `z = 0` in
`≥ 1` point, so the affine patch is the compact projective curve minus a nonempty
finite set. -/
axiom AX_PlaneCurveAffine_noncompact (H : PlaneCurveData) :
    NoncompactSpace (PlaneCurveAffine H)

attribute [instance] AX_PlaneCurveAffine_noncompact

end PlaneCurveAffine

/-! ### Projective compactification

A smooth plane curve of degree `d` generically meets the line at
infinity `{z = 0}` in **`d` distinct points** (by Bézout). So the
classical smooth projective compactification adds `d` points at
infinity (fewer if the curve is tangent to or contains the infinity
line, but still ≥ 1 for smooth curves).

The one-point compactification `OnePoint (PlaneCurveAffine H)` adds
just **one** point — wrong for any `d ≥ 2`. A unified parity-style
split as we used for `Hyperelliptic` doesn't work cleanly here because
the number of infinity points depends on the curve's intersection with
`{z = 0}`, not just parity.

We therefore **axiomatize** the projective compactification with
properly formulated instances, until the three-affine-chart atlas
construction (dehomogenizing with `x ≠ 0`, `y ≠ 0`, `z ≠ 0` and
gluing) is built explicitly.

Historical note: earlier versions (commits through `63ccce7`) defined
`PlaneCurve H := OnePoint (PlaneCurveAffine H)` as a real def. That
was topologically wrong for any `d ≥ 2`; Codex review 2026-04-23
correctly flagged it. This version is the honest axiom-stub.
-/

/-- The smooth projective plane curve `{F = 0} ⊂ ℙ²` as the projective
zero-locus of `F`.

The vanishing predicate is phrased by existence of a nonzero homogeneous
representative, so it is a predicate on projective points rather than on
Lean's chosen `Projectivization.rep`. For the homogeneous polynomial
`H.F`, this is the classical projective zero-locus. -/
def PlaneCurve (H : PlaneCurveData) : Type :=
  { p : Projectivization ℂ (Fin 3 → ℂ) //
    ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0,
      Projectivization.mk ℂ v hv = p ∧ H.F.val.eval v = 0 }

instance PlaneCurve.instTopologicalSpace (H : PlaneCurveData) :
    TopologicalSpace (PlaneCurve H) := by
  letI : TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
    inferInstanceAs (TopologicalSpace
      (Quotient (projectivizationSetoid ℂ (Fin 3 → ℂ))))
  change TopologicalSpace
    { p : Projectivization ℂ (Fin 3 → ℂ) //
      ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0,
        Projectivization.mk ℂ v hv = p ∧ H.F.val.eval v = 0 }
  infer_instance

-- TODO: prove Hausdorffness for the quotient projective topology.
axiom PlaneCurve.instT2Space (H : PlaneCurveData) : T2Space (PlaneCurve H)
attribute [instance] PlaneCurve.instT2Space

-- TODO: prove compactness via the quotient of the unit sphere, or an explicit
-- finite closed-polydisc projective cover.
axiom PlaneCurve.instCompactSpace (H : PlaneCurveData) :
    CompactSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instCompactSpace

-- TODO: prove connectedness from irreducibility/overlapping affine charts.
axiom PlaneCurve.instConnectedSpace (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instConnectedSpace

/-- **Axiom (re-instated 2026-06-04 after review).** `PlaneCurve H` is nonempty.
This statement is TRUE — a positive-degree (`d ≥ 1`) homogeneous `F` over `ℂ`
always has a nontrivial projective zero (restrict `F` to a line ⊂ ℙ² to get a
nonconstant homogeneous binary form, which has a root). An earlier "discharge"
proved it via `AX_PlaneCurveAffine_nonempty`, which is **FALSE** for `F = z` (see
the flag above), so that proof was unsound and is reverted. Real proof
(projective Nullstellensatz / line restriction) is a tracked follow-up — it must
NOT route through the flagged affine axiom. -/
axiom PlaneCurve.instNonempty (H : PlaneCurveData) : Nonempty (PlaneCurve H)
attribute [instance] PlaneCurve.instNonempty

axiom PlaneCurve.instChartedSpace (H : PlaneCurveData) :
    ChartedSpace ℂ (PlaneCurve H)
attribute [instance] PlaneCurve.instChartedSpace

axiom PlaneCurve.instIsManifold (H : PlaneCurveData) :
    IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H)
attribute [instance] PlaneCurve.instIsManifold

-- TODO (genus_eq): `Jacobians.RiemannSurface.genus (PlaneCurve H) = H.genus`
-- via the Plücker formula discharge.

-- TODO (Pluecker discharge): concrete `AX_PluckerFormula` via
-- Poincaré-residue forms `x^a y^b z^c · resF`.

-- TODO (Fermat curves): `{x^d + y^d + z^d = 0}` as concrete example.

end Jacobians.ProjectiveCurve
