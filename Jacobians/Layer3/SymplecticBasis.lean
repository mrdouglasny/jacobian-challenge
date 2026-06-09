import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Symplectic bases for alternating forms

This file proves the field version of the Darboux/symplectic-basis theorem for
finite-dimensional vector spaces. It is the axiom-free linear-algebra core of
the Layer 3 `AX_AnalyticCycleBasis` reduction, except for the integral lattice
step needed to upgrade fields to `Z`.
-/

open Function
open LinearMap (BilinForm)
open Module
open Submodule

noncomputable section

namespace Jacobians.Layer3

universe u v

variable {K : Type u} [Field K]

/-- Reindex the direct sum of a new hyperbolic pair with an old symplectic index
as the direct sum attached to `Option ι`. -/
private def sumOptionSymplecticEquiv (ι : Type*) :
    Sum (Option ι) (Option ι) ≃ Sum (Sum (Fin 1) (Fin 1)) (Sum ι ι) where
  toFun
    | Sum.inl none => Sum.inl (Sum.inl 0)
    | Sum.inl (some i) => Sum.inr (Sum.inl i)
    | Sum.inr none => Sum.inl (Sum.inr 0)
    | Sum.inr (some i) => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl (Sum.inl _) => Sum.inl none
    | Sum.inl (Sum.inr _) => Sum.inr none
    | Sum.inr (Sum.inl i) => Sum.inl (some i)
    | Sum.inr (Sum.inr i) => Sum.inr (some i)
  left_inv := by
    rintro (i | i) <;> cases i <;> rfl
  right_inv := by
    rintro ((i | i) | (i | i))
    · fin_cases i
      rfl
    · fin_cases i
      rfl
    · rfl
    · rfl

/-- Reindex after prepending one hyperbolic pair to a `Fin g`-indexed symplectic basis. -/
private def sumFinSuccSymplecticEquiv (g : ℕ) :
    Sum (Fin (g + 1)) (Fin (g + 1)) ≃
      Sum (Sum (Fin 1) (Fin 1)) (Sum (Fin g) (Fin g)) :=
  (Equiv.sumCongr (finSuccEquiv g) (finSuccEquiv g)).trans
    (sumOptionSymplecticEquiv (Fin g))

private theorem exists_symplectic_basis_aux
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : BilinForm K V) (halt : B.IsAlt) (huni : B.Nondegenerate) :
    ∃ (g : ℕ) (e f : Fin g → V),
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (f i) (f j) = 0) ∧
      ∃ b : Basis (Sum (Fin g) (Fin g)) K V,
        (∀ i, b (Sum.inl i) = e i) ∧
        (∀ i, b (Sum.inr i) = f i) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      (B : BilinForm K V) → B.IsAlt → B.Nondegenerate → finrank K V = n →
        ∃ (g : ℕ) (e f : Fin g → V),
          (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
          (∀ i j, B (e i) (e j) = 0) ∧
          (∀ i j, B (f i) (f j) = 0) ∧
          ∃ b : Basis (Sum (Fin g) (Fin g)) K V,
            (∀ i, b (Sum.inl i) = e i) ∧
            (∀ i, b (Sum.inr i) = f i)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ _ B halt huni hdim
      by_cases hzero : finrank K V = 0
      · refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩
        · intro i; exact i.elim0
        · intro i; exact i.elim0
        · intro i; exact i.elim0
        · refine ⟨basisOfFinrankZero (K := K) (V := V)
            (ι := Sum (Fin 0) (Fin 0)) hzero, ?_, ?_⟩
          · intro i; exact i.elim0
          · intro i; exact i.elim0
      · have hpos : 0 < finrank K V := Nat.pos_of_ne_zero hzero
        haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) hpos
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ : ∃ y : V, B v y ≠ 0 := by
          by_contra h
          apply hv
          apply huni.1
          intro y
          by_contra hy'
          exact h ⟨y, hy'⟩
        let w : V := (B v y)⁻¹ • y
        have hvw : B v w = 1 := by
          simp [w, hy]
        have hwv : B w v = -1 := by
          have h := halt.neg_eq v w
          rw [hvw] at h
          simpa using h.symm
        let hyper : Sum (Fin 1) (Fin 1) → V :=
          Sum.elim (fun _ => v) (fun _ => w)
        let hyperDual : Sum (Fin 1) (Fin 1) → Module.Dual K V :=
          Sum.elim (fun _ => B.flip w) (fun _ => -(B.flip v))
        have hhyperLI : LinearIndependent K hyper := by
          refine LinearIndependent.of_pairwise_dual_eq_zero_one hyper hyperDual ?_ ?_
          · intro i j hij
            cases i <;> cases j
            · exfalso
              exact hij (by congr; exact Subsingleton.elim _ _)
            · simp [hyper, hyperDual, halt.self_eq_zero]
            · simp [hyper, hyperDual, halt.self_eq_zero]
            · exfalso
              exact hij (by congr; exact Subsingleton.elim _ _)
          · intro i
            cases i <;> simp [hyper, hyperDual, hvw, hwv]
        let H : Submodule K V := Submodule.span K (Set.range hyper)
        let W : Submodule K V := B.orthogonal H
        have hvH : v ∈ H := Submodule.subset_span ⟨Sum.inl (0 : Fin 1), rfl⟩
        have hwH : w ∈ H := Submodule.subset_span ⟨Sum.inr (0 : Fin 1), rfl⟩
        have hdisj : Disjoint H W := by
          rw [Submodule.disjoint_def]
          intro x hxH hxW
          have hvx : B v x = 0 := hxW v hvH
          have hwx : B w x = 0 := hxW w hwH
          have hH_pair : H = Submodule.span K ({v, w} : Set V) := by
            unfold H hyper
            congr 1
            ext z
            constructor
            · rintro ⟨i, rfl⟩
              cases i <;> simp
            · intro hz
              rcases Set.mem_insert_iff.mp hz with rfl | hz
              · exact ⟨Sum.inl (0 : Fin 1), rfl⟩
              · have : z = w := by simpa using hz
                exact ⟨Sum.inr (0 : Fin 1), this.symm⟩
          rw [hH_pair] at hxH
          rcases Submodule.mem_span_pair.mp hxH with ⟨a, b, rfl⟩
          have hb : b = 0 := by
            simpa [map_add, hvw, halt.self_eq_zero] using hvx
          have ha : a = 0 := by
            simpa [map_add, hwv, halt.self_eq_zero] using hwx
          simp [ha, hb]
        let bH : Basis (Sum (Fin 1) (Fin 1)) K H := Basis.span hhyperLI
        have hbH_left : ((bH (Sum.inl (0 : Fin 1)) : H) : V) = v := by
          change ((Basis.span hhyperLI (Sum.inl (0 : Fin 1)) : H) : V) = v
          rw [Basis.coe_span_apply (hli := hhyperLI) (Sum.inl (0 : Fin 1))]
          rfl
        have hbH_right : ((bH (Sum.inr (0 : Fin 1)) : H) : V) = w := by
          change ((Basis.span hhyperLI (Sum.inr (0 : Fin 1)) : H) : V) = w
          rw [Basis.coe_span_apply (hli := hhyperLI) (Sum.inr (0 : Fin 1))]
          rfl
        have hfinrankH : finrank K H = 2 := by
          rw [Module.finrank_eq_card_basis bH, Fintype.card_sum]
          simp
        have hcompl : IsCompl H W :=
          (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (B := B) (W := H)
            halt.isRefl).2 hdisj
        have horthW : B.orthogonal W = H := by
          simpa [W] using
            (LinearMap.BilinForm.orthogonal_orthogonal (B := B) huni halt.isRefl H)
        have hcomplW : IsCompl W (B.orthogonal W) := by
          simpa [horthW] using hcompl.symm
        let BW : BilinForm K W := B.restrict W
        have haltW : BW.IsAlt := fun x => halt x
        have huniW : BW.Nondegenerate :=
          (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
            (B := B) (W := W) halt.isRefl).2 hcomplW
        have hdimW_lt : finrank K W < n := by
          have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
          have : 2 + finrank K W = n := by
            simpa [hfinrankH, hdim, H, W] using hsum
          omega
        obtain ⟨g, eW, fW, hpairW, heeW, hffW, hbW⟩ :=
          ih (finrank K W) hdimW_lt W BW haltW huniW rfl
        obtain ⟨bW, hbWe, hbWf⟩ := hbW
        let eOpt : Option (Fin g) → V
          | none => v
          | some i => eW i
        let fOpt : Option (Fin g) → V
          | none => w
          | some i => fW i
        let e : Fin (g + 1) → V := fun i => eOpt (finSuccEquiv g i)
        let f : Fin (g + 1) → V := fun i => fOpt (finSuccEquiv g i)
        have hBvW (x : W) : B v x = 0 := x.2 v hvH
        have hBwW (x : W) : B w x = 0 := x.2 w hwH
        have hBWv (x : W) : B x v = 0 := by
          have h := halt.neg_eq v (x : V)
          rw [hBvW x] at h
          simpa using h.symm
        have hBWw (x : W) : B x w = 0 := by
          have h := halt.neg_eq w (x : V)
          rw [hBwW x] at h
          simpa using h.symm
        have hpairOpt :
            ∀ i j : Option (Fin g), B (eOpt i) (fOpt j) =
              if i = j then 1 else 0 := by
          intro i j
          cases i <;> cases j
          · simp [eOpt, fOpt, hvw]
          · simp [eOpt, fOpt, hBvW]
          · simp [eOpt, fOpt, hBWw]
          · simpa using hpairW _ _
        have heeOpt : ∀ i j : Option (Fin g), B (eOpt i) (eOpt j) = 0 := by
          intro i j
          cases i <;> cases j
          · simp [eOpt, halt.self_eq_zero]
          · simp [eOpt, hBvW]
          · simp [eOpt, hBWv]
          · change BW (eW _) (eW _) = 0
            exact heeW _ _
        have hffOpt : ∀ i j : Option (Fin g), B (fOpt i) (fOpt j) = 0 := by
          intro i j
          cases i <;> cases j
          · simp [fOpt, halt.self_eq_zero]
          · simp [fOpt, hBwW]
          · simp [fOpt, hBWw]
          · change BW (fW _) (fW _) = 0
            exact hffW _ _
        let bProd : Basis (Sum (Sum (Fin 1) (Fin 1)) (Sum (Fin g) (Fin g))) K V :=
          (bH.prod bW).map (Submodule.prodEquivOfIsCompl H W hcompl)
        let b : Basis (Sum (Fin (g + 1)) (Fin (g + 1))) K V :=
          bProd.reindex (sumFinSuccSymplecticEquiv g).symm
        refine ⟨g + 1, e, f, ?_, ?_, ?_, ?_⟩
        · intro i j
          simpa [e, f] using hpairOpt (finSuccEquiv g i) (finSuccEquiv g j)
        · intro i j
          simpa [e] using heeOpt (finSuccEquiv g i) (finSuccEquiv g j)
        · intro i j
          simpa [f] using hffOpt (finSuccEquiv g i) (finSuccEquiv g j)
        · refine ⟨b, ?_, ?_⟩
          · intro i
            cases h : finSuccEquiv g i with
            | none =>
                simpa [b, bProd, e, sumFinSuccSymplecticEquiv, sumOptionSymplecticEquiv,
                  h, eOpt] using hbH_left
            | some k =>
                simp [b, bProd, e, sumFinSuccSymplecticEquiv, sumOptionSymplecticEquiv,
                  h, eOpt, hbWe]
          · intro i
            cases h : finSuccEquiv g i with
            | none =>
                simpa [b, bProd, f, sumFinSuccSymplecticEquiv, sumOptionSymplecticEquiv,
                  h, fOpt] using hbH_right
            | some k =>
                simp [b, bProd, f, sumFinSuccSymplecticEquiv, sumOptionSymplecticEquiv,
                  h, fOpt, hbWf]
  exact hP (finrank K V) V B halt huni rfl

end Jacobians.Layer3

/-- Field version of the Darboux theorem for alternating bilinear forms.

This is the fallback version of the intended integral statement: over a field,
a nondegenerate alternating bilinear form on a finite-dimensional vector space
admits a symplectic basis. -/
theorem exists_symplectic_basis
    {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : BilinForm K V) (halt : B.IsAlt) (huni : B.Nondegenerate) :
    ∃ (g : ℕ) (e f : Fin g → V),
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (f i) (f j) = 0) ∧
      ∃ b : Basis (Sum (Fin g) (Fin g)) K V,
        (∀ i, b (Sum.inl i) = e i) ∧
        (∀ i, b (Sum.inr i) = f i) :=
  Jacobians.Layer3.exists_symplectic_basis_aux B halt huni
