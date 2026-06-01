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
import Jacobians.ProjectiveCurve.Hyperelliptic.Even

namespace Jacobians.ProjectiveCurve

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

end Jacobians.ProjectiveCurve
