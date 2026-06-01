/-
# The hyperelliptic involution on `HyperellipticEvenProj`

The involution `σ(x, y) = (x, −y)` on the even-degree projective hyperelliptic
curve. It is the key tool for the Liouville-L2 decomposition: a holomorphic
1-form is σ-anti-invariant (`σ*ω = −ω`), which lets one recover the
decomposition `ω = a(x) dx/y`. See `docs/genus-L2-execution-roadmap.md` (Mσ).

This file (Mσ, part 1): the involution as a continuous involutive self-map of
the curve, built by descending `(x,y) ↦ (x,−y)` (on each affine summand)
through the gluing quotient — σ respects the glue `(x,y) ↔ (1/x, y/x^{g+1})`
because negating `y` negates both sides.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace Jacobians.ProjectiveCurve

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData}

/-! ## Summand involutions -/

/-- The hyperelliptic involution on the affine curve: `(x, y) ↦ (x, −y)`. -/
def HyperellipticAffine.invol (a : HyperellipticAffine H) : HyperellipticAffine H :=
  ⟨(a.val.1, -a.val.2), by rw [neg_sq]; exact a.property⟩

@[simp] lemma HyperellipticAffine.invol_val (a : HyperellipticAffine H) :
    (a.invol).val = (a.val.1, -a.val.2) := rfl

@[simp] lemma HyperellipticAffine.invol_invol (a : HyperellipticAffine H) :
    a.invol.invol = a := by
  apply Subtype.ext; simp [HyperellipticAffine.invol]

/-- The involution on the affine-infinity chart: `(t, u) ↦ (t, −u)`. -/
def HyperellipticAffineInfinity.invol (b : HyperellipticAffineInfinity H) :
    HyperellipticAffineInfinity H :=
  ⟨(b.val.1, -b.val.2), by rw [neg_sq]; exact b.property⟩

@[simp] lemma HyperellipticAffineInfinity.invol_val (b : HyperellipticAffineInfinity H) :
    (b.invol).val = (b.val.1, -b.val.2) := rfl

@[simp] lemma HyperellipticAffineInfinity.invol_invol (b : HyperellipticAffineInfinity H) :
    b.invol.invol = b := by
  apply Subtype.ext; simp [HyperellipticAffineInfinity.invol]

/-! ## Involution on the pre-pushout, respecting the glue -/

/-- The involution on the disjoint sum of the two affine charts. -/
def hyperellipticEvenInvolPre (H : HyperellipticData) :
    HyperellipticEvenPre H → HyperellipticEvenPre H :=
  Sum.map HyperellipticAffine.invol HyperellipticAffineInfinity.invol

@[simp] lemma hyperellipticEvenInvolPre_invol (p : HyperellipticEvenPre H) :
    hyperellipticEvenInvolPre H (hyperellipticEvenInvolPre H p) = p := by
  rcases p with a | b <;> simp [hyperellipticEvenInvolPre]

/-- The involution sends glue-related points to glue-related points. -/
lemma hyperellipticEvenInvol_glue (H : HyperellipticData) {p q : HyperellipticEvenPre H}
    (h : HyperellipticEvenGlue H p q) :
    HyperellipticEvenGlue H (hyperellipticEvenInvolPre H p) (hyperellipticEvenInvolPre H q) := by
  rcases p with a | b <;> rcases q with a' | b'
  · exact h.elim
  · simp only [hyperellipticEvenInvolPre, Sum.map_inl, Sum.map_inr, HyperellipticEvenGlue,
      HyperellipticAffine.invol_val, HyperellipticAffineInfinity.invol_val] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, h2, by rw [h3]; ring⟩
  · exact h.elim
  · exact h.elim

/-- The involution respects the `EqvGen` closure of the glue. -/
lemma hyperellipticEvenInvol_eqvGen (H : HyperellipticData) {p q : HyperellipticEvenPre H}
    (h : Relation.EqvGen (HyperellipticEvenGlue H) p q) :
    Relation.EqvGen (HyperellipticEvenGlue H)
      (hyperellipticEvenInvolPre H p) (hyperellipticEvenInvolPre H q) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (hyperellipticEvenInvol_glue H hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-! ## The descended involution on `HyperellipticEvenProj` -/

/-- The hyperelliptic involution `σ : HyperellipticEvenProj H → HyperellipticEvenProj H`,
`(x, y) ↦ (x, −y)`, descended through the gluing quotient. -/
def hyperellipticEvenInvol (H : HyperellipticData) :
    HyperellipticEvenProj H → HyperellipticEvenProj H :=
  Quotient.map (hyperellipticEvenInvolPre H)
    (fun _ _ h => hyperellipticEvenInvol_eqvGen H h)

@[simp] lemma hyperellipticEvenInvol_mk (p : HyperellipticEvenPre H) :
    hyperellipticEvenInvol H (Quotient.mk _ p) =
      Quotient.mk _ (hyperellipticEvenInvolPre H p) := rfl

@[simp] lemma hyperellipticEvenInvol_invol (H : HyperellipticData)
    (q : HyperellipticEvenProj H) :
    hyperellipticEvenInvol H (hyperellipticEvenInvol H q) = q := by
  induction q using Quotient.inductionOn with
  | h p => simp

theorem hyperellipticEvenInvol_involutive (H : HyperellipticData) :
    Function.Involutive (hyperellipticEvenInvol H) :=
  hyperellipticEvenInvol_invol H

/-! ## Continuity -/

theorem HyperellipticAffine.continuous_invol :
    Continuous (HyperellipticAffine.invol (H := H)) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).neg)

theorem HyperellipticAffineInfinity.continuous_invol :
    Continuous (HyperellipticAffineInfinity.invol (H := H)) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).neg)

/-! ## Smoothness on the affine summands -/

lemma HyperellipticAffine.invol_mem_smoothLocusY (a : HyperellipticAffine H)
    (ha : a ∈ HyperellipticAffine.smoothLocusY H) :
    a.invol ∈ HyperellipticAffine.smoothLocusY H := by
  simpa [HyperellipticAffine.smoothLocusY, HyperellipticAffine.invol]
    using neg_ne_zero.mpr ha

lemma HyperellipticAffine.invol_mem_smoothLocusX (a : HyperellipticAffine H)
    (ha : a ∈ HyperellipticAffine.smoothLocusX H) :
    a.invol ∈ HyperellipticAffine.smoothLocusX H := by
  simpa [HyperellipticAffine.smoothLocusX, HyperellipticAffine.invol] using ha

theorem HyperellipticAffine.contMDiffAt_invol (a : HyperellipticAffine H) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω HyperellipticAffine.invol a := by
  classical
  by_cases haY : a ∈ HyperellipticAffine.smoothLocusY H
  · let e := HyperellipticAffine.affineChartProjX (H := H) a haY
    let haY' := HyperellipticAffine.invol_mem_smoothLocusY a haY
    let e' := HyperellipticAffine.affineChartProjX (H := H) a.invol haY'
    have hchart :
        (chartAt ℂ a : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) = e := by
      change HyperellipticAffine.affineChartAt (H := H) a = e
      simp [e, HyperellipticAffine.affineChartAt, haY]
    have hchart' :
        (chartAt ℂ a.invol : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) = e' := by
      change HyperellipticAffine.affineChartAt (H := H) a.invol = e'
      simp [e', HyperellipticAffine.affineChartAt, haY']
    have hx : a ∈ e.source := by
      dsimp [e]
      exact HyperellipticAffine.affineChartProjX_mem_source a haY
    rw [contMDiffAt_iff]
    constructor
    · exact HyperellipticAffine.continuous_invol.continuousAt
    · have hEq :
          (fun z : ℂ => (extChartAt 𝓘(ℂ, ℂ) a.invol)
              (HyperellipticAffine.invol
                ((extChartAt 𝓘(ℂ, ℂ) a).symm z)))
            =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) a) a)]
          (fun z : ℂ => z) := by
        have ht : e.target ∈ 𝓝 (e a) := e.open_target.mem_nhds (e.map_source hx)
        have ht' : e.target ∈ 𝓝 ((extChartAt 𝓘(ℂ, ℂ) a) a) := by
          simpa [extChartAt_coe, hchart, e, modelWithCornersSelf_coe] using ht
        filter_upwards [ht'] with z hz
        have hz0 : z ∈ e.target := hz
        dsimp [e, e'] at hz0
        simp only [extChartAt_coe, extChartAt_coe_symm, hchart, hchart',
          Function.comp_apply, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq]
        change
          ((HyperellipticAffine.invol
            ((HyperellipticAffine.affineChartProjX (H := H) a haY).symm z)).val.1) = z
        simp [HyperellipticAffine.invol,
          HyperellipticAffine.affineChartProjX_symm_apply_fst (H := H) a haY hz0]
      have hAt : ContDiffAt ℂ ω (fun z : ℂ => z)
          ((extChartAt 𝓘(ℂ, ℂ) a) a) := contDiffAt_id
      have hAt' : ContDiffAt ℂ ω
          (fun z : ℂ => (extChartAt 𝓘(ℂ, ℂ) a.invol)
            (HyperellipticAffine.invol ((extChartAt 𝓘(ℂ, ℂ) a).symm z)))
          ((extChartAt 𝓘(ℂ, ℂ) a) a) :=
        hAt.congr_of_eventuallyEq hEq
      simpa [modelWithCornersSelf_coe, Set.range_id] using hAt'.contDiffWithinAt
  · have haY0 : a.val.2 = 0 := by
      simpa [HyperellipticAffine.smoothLocusY] using haY
    have haX : a ∈ HyperellipticAffine.smoothLocusX H :=
      HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H haY0
    let e := HyperellipticAffine.affineChartProjY (H := H) a haX
    let haX' := HyperellipticAffine.invol_mem_smoothLocusX a haX
    let e' := HyperellipticAffine.affineChartProjY (H := H) a.invol haX'
    have haInvNotY : a.invol ∉ HyperellipticAffine.smoothLocusY H := by
      intro h
      apply haY
      simpa [HyperellipticAffine.smoothLocusY, HyperellipticAffine.invol] using h
    have hchart :
        (chartAt ℂ a : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) = e := by
      change HyperellipticAffine.affineChartAt (H := H) a = e
      simp [e, HyperellipticAffine.affineChartAt, haY]
    have hchart' :
        (chartAt ℂ a.invol : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) = e' := by
      change HyperellipticAffine.affineChartAt (H := H) a.invol = e'
      simp [e', HyperellipticAffine.affineChartAt, haInvNotY]
    have hx : a ∈ e.source := by
      dsimp [e]
      exact HyperellipticAffine.affineChartProjY_mem_source a haX
    rw [contMDiffAt_iff]
    constructor
    · exact HyperellipticAffine.continuous_invol.continuousAt
    · have hEq :
          (fun z : ℂ => (extChartAt 𝓘(ℂ, ℂ) a.invol)
              (HyperellipticAffine.invol
                ((extChartAt 𝓘(ℂ, ℂ) a).symm z)))
            =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) a) a)]
          (fun z : ℂ => -z) := by
        have ht : e.target ∈ 𝓝 (e a) := e.open_target.mem_nhds (e.map_source hx)
        have ht' : e.target ∈ 𝓝 ((extChartAt 𝓘(ℂ, ℂ) a) a) := by
          simpa [extChartAt_coe, hchart, e, modelWithCornersSelf_coe] using ht
        filter_upwards [ht'] with z hz
        have hz0 : z ∈ e.target := hz
        dsimp [e, e'] at hz0
        simp only [extChartAt_coe, extChartAt_coe_symm, hchart, hchart',
          Function.comp_apply, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq]
        change
          ((HyperellipticAffine.invol
            ((HyperellipticAffine.affineChartProjY (H := H) a haX).symm z)).val.2) = -z
        simp [HyperellipticAffine.invol,
          HyperellipticAffine.affineChartProjY_symm_apply_snd (H := H) a haX hz0]
      have hAt : ContDiffAt ℂ ω (fun z : ℂ => -z)
          ((extChartAt 𝓘(ℂ, ℂ) a) a) := contDiff_neg.contDiffAt
      have hAt' : ContDiffAt ℂ ω
          (fun z : ℂ => (extChartAt 𝓘(ℂ, ℂ) a.invol)
            (HyperellipticAffine.invol ((extChartAt 𝓘(ℂ, ℂ) a).symm z)))
          ((extChartAt 𝓘(ℂ, ℂ) a) a) :=
        hAt.congr_of_eventuallyEq hEq
      simpa [modelWithCornersSelf_coe, Set.range_id] using hAt'.contDiffWithinAt

theorem HyperellipticAffine.contMDiff_invol :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (HyperellipticAffine.invol (H := H)) :=
  fun a => HyperellipticAffine.contMDiffAt_invol a

theorem HyperellipticAffineInfinity.contMDiff_invol
    [hf : Fact (¬ Odd H.f.natDegree)] :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (HyperellipticAffineInfinity.invol (H := H)) := by
  let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
  change ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (HyperellipticAffine.invol (H := Hrev))
  exact HyperellipticAffine.contMDiff_invol

theorem hyperellipticEvenInvolPre_continuous (H : HyperellipticData) :
    Continuous (hyperellipticEvenInvolPre H) :=
  HyperellipticAffine.continuous_invol.sumMap HyperellipticAffineInfinity.continuous_invol

theorem hyperellipticEvenInvol_continuous (H : HyperellipticData) :
    Continuous (hyperellipticEvenInvol H) :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr
    ((continuous_quotient_mk').comp (hyperellipticEvenInvolPre_continuous H))

end Jacobians.ProjectiveCurve
