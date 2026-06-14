/-
# Arc-level Riemann bilinear relations — the linear/Gram collapse

R-lane Brick 1+2 (`docs/planning/R1R2_ROUTE.md` §2, Layer 1–2). This file
reduces the two Hodge fields of `Jacobians.Axioms.PeriodCycleBasis` —

* `R1 : ∀ η ζ, Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0`
* `R2 : ∀ η ≠ 0, 0 < (I * Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re`

— to TWO `g × g` matrix statements about the arc-period blocks of a single
ℂ-basis of holomorphic 1-forms:

* `arc_R1_of_periodMatrix_symm` : `AᵀB = BᵀA  →  R1 field`;
* `arc_R2_of_periodGram_posDef` : `(I•(AᵀB̄ − BᵀĀ)).PosDef  →  R2 field`.

These matrix statements are exactly the output shape of the Kirov port's
proven boundary-word engines (`riemann_R1_of_boundaryWord`,
`riemann_R2_posDef_of_boundaryWord`); the composition lives in
`Jacobians/RiemannSurface/BilinearRelationsBoundaryWord.lean`.

As an unconditional corollary, the R1 field is a **theorem for genus ≤ 1**
(`arc_R1_of_genus_le_one`): the `1 × 1` (or empty) blocks commute, so
isotropy needs no analytic input at all — feeding the elliptic witness
program directly.

Everything here is pure linear algebra over the proven integrability of
analytic-arc integrands (`analyticArc_canonicalIntegrand_intervalIntegrable`);
no axiom is consumed (in particular NOT `AX_PeriodCycleBasis` — circularity
guard, see the route doc §4).
-/
import Submission.Jacobians.RiemannSurface.LoopIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff ComplexOrder
open Jacobians.Axioms
open Jacobians.Layer3 (PeriodVector Q)
open Matrix Finset

/-- The symplectic dual form `Q` vanishes on the diagonal (it is alternating). -/
theorem _root_.Jacobians.Layer3.Q_self {g : ℕ} (φ : PeriodVector g) : Q φ φ = 0 :=
  Finset.sum_eq_zero fun _ _ => by ring

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Linearity of the canonical arc integral over a finite combination of
holomorphic 1-forms (integrability is automatic for analytic arcs). -/
theorem canonicalArcIntegral_sum_smul (γ : AnalyticArc X) {n : ℕ}
    (c : Fin n → ℂ) (f : Fin n → HolomorphicOneForm X) :
    canonicalArcIntegral γ (∑ i, c i • f i) =
      ∑ i, c i * canonicalArcIntegral γ (f i) := by
  classical
  let L : HolomorphicOneForm X →ₗ[ℂ] ℂ :=
    arcPeriodFunctional γ fun form =>
      analyticArc_canonicalIntegrand_intervalIntegrable γ form
  have h1 : canonicalArcIntegral γ (∑ i, c i • f i) = L (∑ i, c i • f i) := rfl
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- The quadruple-sum expansion behind both bilinear collapses: a difference
of products of sums regrouped as coefficient-weighted blocks. -/
private theorem sum_quad_expand {n g : ℕ} (c d : Fin n → ℂ)
    (a b a' b' : Fin g → Fin n → ℂ) :
    (∑ k, ((∑ i, c i * a k i) * (∑ j, d j * b' k j)
        - (∑ i, c i * b k i) * (∑ j, d j * a' k j)))
      = ∑ i, ∑ j, c i * d j * (∑ k, (a k i * b' k j - b k i * a' k j)) := by
  have hk : ∀ k, (∑ i, c i * a k i) * (∑ j, d j * b' k j)
      - (∑ i, c i * b k i) * (∑ j, d j * a' k j)
      = ∑ i, ∑ j, c i * d j * (a k i * b' k j - b k i * a' k j) := by
    intro k
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Finset.mul_sum _ _ _).symm

section Blocks

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {x₀ : X}

/-- The arc-level A-period block of a family of holomorphic 1-forms over a
`Fin (2g)`-indexed loop family: row `i` = α-cycle index, column `j` = form
index, entry `∫_{α_i} f j` (chart-local canonical arc integral — NOT the
`periodMap`/`loopIntegralToH1` pipeline, which depends on the axiom). -/
noncomputable def arcAPeriodMatrix (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  Matrix.of fun i j => canonicalArcIntegral (loops (αEmbed i)).arc (f j)

/-- The arc-level B-period block `∫_{β_i} f j` (same conventions as
`arcAPeriodMatrix`). -/
noncomputable def arcBPeriodMatrix (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  Matrix.of fun i j => canonicalArcIntegral (loops (βEmbed i)).arc (f j)

@[simp]
theorem arcAPeriodMatrix_apply (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) (i j : Fin (genus X)) :
    arcAPeriodMatrix loops f i j = canonicalArcIntegral (loops (αEmbed i)).arc (f j) :=
  rfl

@[simp]
theorem arcBPeriodMatrix_apply (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) (i j : Fin (genus X)) :
    arcBPeriodMatrix loops f i j = canonicalArcIntegral (loops (βEmbed i)).arc (f j) :=
  rfl

/-- The arc-level period Gram (Hermitian) form `I•(AᵀB̄ − BᵀĀ)` of a form
family. Riemann's second bilinear relation is its positive-definiteness
(sign validated at `g = 1`: standard torus ↦ `2·Im τ > 0`, matching the
port's `periodHermitian` convention). -/
noncomputable def arcPeriodGram (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  Complex.I •
    ((arcAPeriodMatrix loops f)ᵀ * (arcBPeriodMatrix loops f).map (starRingEnd ℂ)
      - (arcBPeriodMatrix loops f)ᵀ * (arcAPeriodMatrix loops f).map (starRingEnd ℂ))

/-- `Q` on the arc period vectors of two family members is the corresponding
entry of `AᵀB − BᵀA`. -/
theorem Q_arcPeriodVec_apply (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) (i j : Fin (genus X)) :
    Q (arcPeriodVec loops (f i)) (arcPeriodVec loops (f j))
      = ((arcAPeriodMatrix loops f)ᵀ * arcBPeriodMatrix loops f
          - (arcBPeriodMatrix loops f)ᵀ * arcAPeriodMatrix loops f) i j := by
  simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_sub_distrib]

/-- `Q` against the conjugate arc period vector is the corresponding entry of
`AᵀB̄ − BᵀĀ`. -/
theorem Q_arcPeriodVec_conj_apply (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) (i j : Fin (genus X)) :
    Q (arcPeriodVec loops (f i)) (conjArcPeriodVec loops (f j))
      = ((arcAPeriodMatrix loops f)ᵀ * (arcBPeriodMatrix loops f).map (starRingEnd ℂ)
          - (arcBPeriodMatrix loops f)ᵀ
              * (arcAPeriodMatrix loops f).map (starRingEnd ℂ)) i j := by
  simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_sub_distrib]

/-- Bilinear expansion of `Q` over arc period vectors of finite form
combinations. -/
theorem Q_arcPeriodVec_sum_smul (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    {n : ℕ} (c d : Fin n → ℂ) (f e : Fin n → HolomorphicOneForm X) :
    Q (arcPeriodVec loops (∑ i, c i • f i)) (arcPeriodVec loops (∑ j, d j • e j))
      = ∑ i, ∑ j, c i * d j *
          Q (arcPeriodVec loops (f i)) (arcPeriodVec loops (e j)) := by
  simp only [Q, arcPeriodVec_fst, arcPeriodVec_snd, canonicalArcIntegral_sum_smul]
  exact sum_quad_expand c d
    (fun k i => canonicalArcIntegral (loops (αEmbed k)).arc (f i))
    (fun k i => canonicalArcIntegral (loops (βEmbed k)).arc (f i))
    (fun k j => canonicalArcIntegral (loops (αEmbed k)).arc (e j))
    (fun k j => canonicalArcIntegral (loops (βEmbed k)).arc (e j))

/-- Sesquilinear expansion of `Q` against the conjugate arc period vector of
the SAME combination (the R2 quadratic form). -/
theorem Q_arcPeriodVec_conj_sum_smul (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    {n : ℕ} (c : Fin n → ℂ) (f : Fin n → HolomorphicOneForm X) :
    Q (arcPeriodVec loops (∑ i, c i • f i)) (conjArcPeriodVec loops (∑ j, c j • f j))
      = ∑ i, ∑ j, c i * star (c j) *
          Q (arcPeriodVec loops (f i)) (conjArcPeriodVec loops (f j)) := by
  simp only [Q, arcPeriodVec_fst, arcPeriodVec_snd, conjArcPeriodVec_fst,
    conjArcPeriodVec_snd, canonicalArcIntegral_sum_smul, star_sum, star_mul']
  exact sum_quad_expand c (fun j => star (c j))
    (fun k i => canonicalArcIntegral (loops (αEmbed k)).arc (f i))
    (fun k i => canonicalArcIntegral (loops (βEmbed k)).arc (f i))
    (fun k j => star (canonicalArcIntegral (loops (αEmbed k)).arc (f j)))
    (fun k j => star (canonicalArcIntegral (loops (βEmbed k)).arc (f j)))

/-- **R1 collapse (Brick 1).** If the arc-period blocks of one ℂ-basis of
holomorphic 1-forms satisfy `AᵀB = BᵀA`, then the `R1` field of
`PeriodCycleBasis` holds: `Q` vanishes on the arc period vectors of EVERY
pair of holomorphic 1-forms. -/
theorem arc_R1_of_periodMatrix_symm (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (hsymm : (arcAPeriodMatrix loops fun j => cω j)ᵀ
          * (arcBPeriodMatrix loops fun j => cω j)
        = (arcBPeriodMatrix loops fun j => cω j)ᵀ
          * (arcAPeriodMatrix loops fun j => cω j))
    (η ζ : HolomorphicOneForm X) :
    Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0 := by
  have hδ : ((arcAPeriodMatrix loops fun j => cω j)ᵀ
        * (arcBPeriodMatrix loops fun j => cω j)
      - (arcBPeriodMatrix loops fun j => cω j)ᵀ
        * (arcAPeriodMatrix loops fun j => cω j)) = 0 := sub_eq_zero.mpr hsymm
  have hη : η = ∑ i, cω.equivFun η i • cω i := by
    conv_lhs => rw [← cω.equivFun.symm_apply_apply η]
    rw [cω.equivFun_symm_apply]
  have hζ : ζ = ∑ j, cω.equivFun ζ j • cω j := by
    conv_lhs => rw [← cω.equivFun.symm_apply_apply ζ]
    rw [cω.equivFun_symm_apply]
  rw [hη, hζ, Q_arcPeriodVec_sum_smul]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Q_arcPeriodVec_apply, hδ]
  simp

/-- The block symmetry `AᵀB = BᵀA` is automatic when `genus X ≤ 1`: the
blocks are `1 × 1` (or empty) and commute entrywise. -/
theorem arcPeriodMatrix_symm_of_genus_le_one (hg : genus X ≤ 1)
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (f : Fin (genus X) → HolomorphicOneForm X) :
    (arcAPeriodMatrix loops f)ᵀ * arcBPeriodMatrix loops f
      = (arcBPeriodMatrix loops f)ᵀ * arcAPeriodMatrix loops f := by
  haveI : Subsingleton (Fin (genus X)) :=
    ⟨fun a b => by
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)⟩
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.transpose_apply, Matrix.transpose_apply, mul_comm]

/-- **R1 is a theorem at genus ≤ 1** (given any `Fin (genus X)`-indexed
ℂ-basis of forms): isotropy of the arc period vectors needs no analytic
input below genus 2. Feeds the elliptic (`g = 1`) witness program. -/
theorem arc_R1_of_genus_le_one (hg : genus X ≤ 1)
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (η ζ : HolomorphicOneForm X) :
    Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0 :=
  arc_R1_of_periodMatrix_symm loops cω
    (arcPeriodMatrix_symm_of_genus_le_one hg loops _) η ζ

/-- **R2 is vacuous at genus 0** (given any `Fin (genus X)`-indexed ℂ-basis
of forms): there is no nonzero holomorphic 1-form to test. Companion of
`arc_R1_of_genus_le_one` for the genus-0 witness. -/
theorem arc_R2_of_genus_eq_zero (hg : genus X = 0)
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (η : HolomorphicOneForm X) (hη : η ≠ 0) :
    0 < (Complex.I *
        Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re := by
  exfalso
  apply hη
  haveI : IsEmpty (Fin (genus X)) := by
    rw [hg]
    exact Fin.isEmpty
  have hexp : η = ∑ i, cω.equivFun η i • cω i := by
    conv_lhs => rw [← cω.equivFun.symm_apply_apply η]
    rw [cω.equivFun_symm_apply]
  rw [hexp, Finset.univ_eq_empty, Finset.sum_empty]

/-- **R2 collapse (Brick 2).** If the arc-period Gram form `I•(AᵀB̄ − BᵀĀ)`
of one ℂ-basis of holomorphic 1-forms is positive definite, then the `R2`
field of `PeriodCycleBasis` holds: the Hodge quadratic form is strictly
positive on every nonzero holomorphic 1-form. -/
theorem arc_R2_of_periodGram_posDef (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (hpos : (arcPeriodGram loops fun j => cω j).PosDef)
    (η : HolomorphicOneForm X) (hη : η ≠ 0) :
    0 < (Complex.I *
        Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re := by
  classical
  set f : Fin (genus X) → HolomorphicOneForm X := fun j => cω j with hf
  set c : Fin (genus X) → ℂ := cω.equivFun η with hc
  set N : Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
    (arcAPeriodMatrix loops f)ᵀ * (arcBPeriodMatrix loops f).map (starRingEnd ℂ)
      - (arcBPeriodMatrix loops f)ᵀ * (arcAPeriodMatrix loops f).map (starRingEnd ℂ)
    with hN
  -- the coefficient vector is nonzero
  have hcne : c ≠ 0 := by
    intro h0
    apply hη
    have := congrArg cω.equivFun.symm h0
    rwa [cω.equivFun.symm_apply_apply, map_zero] at this
  have hvne : (star c : Fin (genus X) → ℂ) ≠ 0 := by
    intro h0
    apply hcne
    rw [← star_star c, h0, star_zero]
  -- expand the Hodge quadratic form over the basis blocks
  have hη_eq : η = ∑ i, c i • f i := by
    conv_lhs => rw [← cω.equivFun.symm_apply_apply η]
    rw [cω.equivFun_symm_apply, hc]
  have hexp : Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)
      = ∑ i, ∑ j, c i * star (c j) * N i j := by
    rw [hη_eq, Q_arcPeriodVec_conj_sum_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Q_arcPeriodVec_conj_apply]
  -- identify with the PosDef quadratic form at `v = star c`
  have hdot : star (star c) ⬝ᵥ (arcPeriodGram loops f *ᵥ star c)
      = Complex.I * ∑ i, ∑ j, c i * star (c j) * N i j := by
    rw [arcPeriodGram, ← hN]
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul,
      Pi.star_apply, star_star, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h0 : (0 : ℂ) < star (star c) ⬝ᵥ (arcPeriodGram loops f *ᵥ star c) :=
    hpos.dotProduct_mulVec_pos hvne
  rw [hdot, ← hexp] at h0
  simpa using (Complex.lt_def.mp h0).1

end Blocks

end Jacobians.RiemannSurface
