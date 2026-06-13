/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
# Index-2 kernel generation (Reidemeister–Schreier, transversal `{1, t}`)

The combinatorial half of the T-GEN covering-space wall, isolated as a
self-contained, Mathlib-only group-theory fact. It is **Fact (1)** of the
hyperelliptic branched-cover route (`CoveringGeneration.lean` docstring,
`docs/planning/TGEN_ROUTE.md` rung L2, sub-point 1).

## Statement

Let `G` be a group, `φ : G →* Q` a homomorphism, `t : G` an element with
`φ t ≠ 1` and `φ t * φ t = 1` (a representative of a nontrivial coset of an
index-2 image), and `S : Set G` a generating set (`Subgroup.closure S = ⊤`)
each of whose members has parity `0` or `φ t` (`∀ s ∈ S, φ s = 1 ∨ φ s = φ t`).
Then the **Schreier generating set**

```
schreierSet φ t S
  = {s          | s ∈ S, φ s = 1}        -- coset rep 1, parity 0
  ∪ {s * t⁻¹    | s ∈ S, φ s = φ t}       -- coset rep 1, parity 1
  ∪ {t * s * t⁻¹| s ∈ S, φ s = 1}         -- coset rep t, parity 0
  ∪ {t * s      | s ∈ S, φ s = φ t}       -- coset rep t, parity 1
  ∪ {t * t}                               -- closes the transversal
```

generates `φ.ker`: `Subgroup.closure (schreierSet φ t S) = φ.ker`
(`closure_schreierSet_eq_ker`).

This is the classical index-2 Reidemeister–Schreier computation with
transversal `{1, t}`. For the hyperelliptic double cover the image group is
`Q = Multiplicative (ZMod 2)`, `φ` is the parity monodromy of the 2-sheeted
cover, and the branch-point lassos all have `φ s = φ t = ofAdd 1`.

## Proof outline

1. `closure_schreierSet_le_ker` — every Schreier generator lies in `φ.ker`
   (direct computation), so `closure (schreierSet …) ≤ φ.ker`.
2. `conj_t_mem` — `closure (schreierSet …)` is invariant under conjugation by
   `t` (checked on each generator family), hence also by `t⁻¹`
   (`conj_tinv_mem`, via `t * t ∈ closure`).
3. `schreierPred` — a bundled `Subgroup.closure_induction` over `S = ⊤`
   proving, for every `g`, that `φ g ∈ {1, φ t}` and: if `φ g = 1` then
   `g ∈ closure (schreierSet …)`; if `φ g = φ t` then
   `t⁻¹ * g ∈ closure (schreierSet …)`. The `mul`/`inv` steps use the
   conjugation invariance of step 2.
4. `ker_le_closure_schreierSet` — a kernel element has parity `1`, so by
   step 3 lands in the closure. Together with step 1 this gives equality.

Mathlib-only imports; sorry-free and axiom-free (the three standard axioms).
-/
import Mathlib

namespace Jacobians.Topology

open Subgroup

variable {G Q : Type*} [Group G] [Group Q]

/-- The Schreier generating set for the index-2 kernel with transversal
`{1, t}`. See the module docstring for the five families. -/
def schreierSet (φ : G →* Q) (t : G) (S : Set G) : Set G :=
  {g | ∃ s ∈ S, φ s = 1 ∧ g = s} ∪
  {g | ∃ s ∈ S, φ s = φ t ∧ g = s * t⁻¹} ∪
  {g | ∃ s ∈ S, φ s = 1 ∧ g = t * s * t⁻¹} ∪
  {g | ∃ s ∈ S, φ s = φ t ∧ g = t * s} ∪
  {t * t}

variable {φ : G →* Q} {t : G} {S : Set G}

theorem mem_schreierSet_1 {s : G} (hs : s ∈ S) (h0 : φ s = 1) :
    s ∈ schreierSet φ t S := by
  rw [schreierSet]; left; left; left; left; exact ⟨s, hs, h0, rfl⟩

theorem mem_schreierSet_2 {s : G} (hs : s ∈ S) (h1 : φ s = φ t) :
    s * t⁻¹ ∈ schreierSet φ t S := by
  rw [schreierSet]; left; left; left; right; exact ⟨s, hs, h1, rfl⟩

theorem mem_schreierSet_3 {s : G} (hs : s ∈ S) (h0 : φ s = 1) :
    t * s * t⁻¹ ∈ schreierSet φ t S := by
  rw [schreierSet]; left; left; right; exact ⟨s, hs, h0, rfl⟩

theorem mem_schreierSet_4 {s : G} (hs : s ∈ S) (h1 : φ s = φ t) :
    t * s ∈ schreierSet φ t S := by
  rw [schreierSet]; left; right; exact ⟨s, hs, h1, rfl⟩

theorem mem_schreierSet_tt : t * t ∈ schreierSet φ t S := by
  rw [schreierSet]; right; rfl

/-- Every element of the Schreier set lies in `φ.ker`. -/
theorem schreierSet_subset_ker (ht2 : φ t * φ t = 1) :
    schreierSet φ t S ⊆ (φ.ker : Set G) := by
  intro g hg
  rw [schreierSet] at hg
  rcases hg with (((((⟨s, _, hs, rfl⟩) | ⟨s, _, hs, rfl⟩) | ⟨s, _, hs, rfl⟩) |
      ⟨s, _, hs, rfl⟩) | rfl)
  · simpa [MonoidHom.mem_ker] using hs
  · simp [MonoidHom.mem_ker, map_mul, map_inv, hs]
  · simp [MonoidHom.mem_ker, map_mul, map_inv, hs]
  · simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, hs]
    rw [ht2]
  · simpa [MonoidHom.mem_ker, map_mul] using ht2

/-- `closure (schreierSet …) ≤ φ.ker`. -/
theorem closure_schreierSet_le_ker (ht2 : φ t * φ t = 1) :
    closure (schreierSet φ t S) ≤ φ.ker :=
  (closure_le _).mpr (schreierSet_subset_ker ht2)

/-- `t * t` lies in the Schreier closure. -/
theorem tt_mem_closure : t * t ∈ closure (schreierSet φ t S) :=
  subset_closure mem_schreierSet_tt

/-- The Schreier closure is invariant under conjugation by `t`: checked on each
generator family (each conjugate is again a product of Schreier generators). -/
theorem conj_t_mem (c : G) (hc : c ∈ closure (schreierSet φ t S)) :
    t * c * t⁻¹ ∈ closure (schreierSet φ t S) := by
  induction hc using closure_induction with
  | mem x hx =>
    rw [schreierSet] at hx
    rcases hx with (((((⟨s, hs, h0, rfl⟩) | ⟨s, hs, h1, rfl⟩) | ⟨s, hs, h0, rfl⟩) |
        ⟨s, hs, h1, rfl⟩) | rfl)
    · -- family 1: `t * s * t⁻¹` is family 3
      exact subset_closure (mem_schreierSet_3 hs h0)
    · -- family 2: `t * (s * t⁻¹) * t⁻¹ = (t * s) * (t * t)⁻¹`
      have e : t * (s * t⁻¹) * t⁻¹ = (t * s) * (t * t)⁻¹ := by group
      rw [e]
      exact mul_mem (subset_closure (mem_schreierSet_4 hs h1))
        (inv_mem tt_mem_closure)
    · -- family 3: `t * (t * s * t⁻¹) * t⁻¹ = (t*t) * s * (t*t)⁻¹`
      have e : t * (t * s * t⁻¹) * t⁻¹ = (t * t) * s * (t * t)⁻¹ := by group
      rw [e]
      have hsc : s ∈ closure (schreierSet φ t S) :=
        subset_closure (mem_schreierSet_1 hs h0)
      exact mul_mem (mul_mem tt_mem_closure hsc) (inv_mem tt_mem_closure)
    · -- family 4: `t * (t * s) * t⁻¹ = (t*t) * (s * t⁻¹)`
      have e : t * (t * s) * t⁻¹ = (t * t) * (s * t⁻¹) := by group
      rw [e]
      exact mul_mem tt_mem_closure
        (subset_closure (mem_schreierSet_2 hs h1))
    · -- `t * (t * t) * t⁻¹ = t * t`
      have e : t * (t * t) * t⁻¹ = t * t := by group
      rw [e]; exact tt_mem_closure
  | one => simp only [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ hx hy =>
    have e : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [e]; exact mul_mem hx hy
  | inv x _ hx =>
    have e : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hx

/-- The Schreier closure is invariant under conjugation by `t⁻¹` (derived from
`conj_t_mem` and `t * t ∈ closure`). -/
theorem conj_tinv_mem (c : G) (hc : c ∈ closure (schreierSet φ t S)) :
    t⁻¹ * c * t ∈ closure (schreierSet φ t S) := by
  have e : t⁻¹ * c * t = (t * t)⁻¹ * (t * c * t⁻¹) * (t * t) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem tt_mem_closure) (conj_t_mem c hc)) tt_mem_closure

/-- The bundled induction invariant: every `g` in `closure S` has parity in
`{1, φ t}`, and the parity decides whether `g` (parity `0`) or `t⁻¹ * g`
(parity `1`) lies in the Schreier closure. -/
private def schreierPred (g : G) : Prop :=
  (φ g = 1 ∨ φ g = φ t) ∧
  (φ g = 1 → g ∈ closure (schreierSet φ t S)) ∧
  (φ g = φ t → t⁻¹ * g ∈ closure (schreierSet φ t S))

private theorem schreierPred_mem
    (hpar : ∀ s ∈ S, φ s = 1 ∨ φ s = φ t) (s : G) (hs : s ∈ S) :
    schreierPred (φ := φ) (t := t) (S := S) s := by
  refine ⟨hpar s hs, ?_, ?_⟩
  · intro hs1
    exact subset_closure (mem_schreierSet_1 hs hs1)
  · intro hst
    -- `t⁻¹ * s = (t * t)⁻¹ * (t * s)` with `t * s` family 4, `t * t` the cap.
    have e : t⁻¹ * s = (t * t)⁻¹ * (t * s) := by group
    rw [e]
    exact mul_mem (inv_mem tt_mem_closure)
      (subset_closure (mem_schreierSet_4 hs hst))

private theorem schreierPred_one (ht : φ t ≠ 1) :
    schreierPred (φ := φ) (t := t) (S := S) 1 := by
  refine ⟨Or.inl (map_one φ), fun _ => one_mem _, fun h => ?_⟩
  exact (ht (h.symm.trans (map_one φ))).elim

private theorem schreierPred_mul (ht : φ t ≠ 1) (ht2 : φ t * φ t = 1)
    (x y : G) (hx : schreierPred (φ := φ) (t := t) (S := S) x)
    (hy : schreierPred (φ := φ) (t := t) (S := S) y) :
    schreierPred (φ := φ) (t := t) (S := S) (x * y) := by
  obtain ⟨hxp, hx0, hx1⟩ := hx
  obtain ⟨hyp, hy0, hy1⟩ := hy
  rcases hxp with hxe | hxe <;> rcases hyp with hye | hye
  · -- (0,0): φ(xy)=1, xy ∈ closure
    have hxy : φ (x * y) = 1 := by rw [map_mul, hxe, hye, one_mul]
    refine ⟨Or.inl hxy, fun _ => ?_, fun h => ?_⟩
    · exact mul_mem (hx0 hxe) (hy0 hye)
    · exact (ht (h.symm.trans hxy)).elim
  · -- (0,φt): φ(xy)=φt, t⁻¹(xy) = (t⁻¹ x t)(t⁻¹ y)
    have hxy : φ (x * y) = φ t := by rw [map_mul, hxe, hye, one_mul]
    refine ⟨Or.inr hxy, fun h => ?_, fun _ => ?_⟩
    · exact (ht (hxy.symm.trans h)).elim
    · have e : t⁻¹ * (x * y) = (t⁻¹ * x * t) * (t⁻¹ * y) := by group
      rw [e]
      exact mul_mem (conj_tinv_mem x (hx0 hxe)) (hy1 hye)
  · -- (φt,0): φ(xy)=φt, t⁻¹(xy) = (t⁻¹ x)(y)
    have hxy : φ (x * y) = φ t := by rw [map_mul, hxe, hye, mul_one]
    refine ⟨Or.inr hxy, fun h => ?_, fun _ => ?_⟩
    · exact (ht (hxy.symm.trans h)).elim
    · have e : t⁻¹ * (x * y) = (t⁻¹ * x) * y := by group
      rw [e]
      exact mul_mem (hx1 hxe) (hy0 hye)
  · -- (φt,φt): φ(xy)=φt*φt=1, xy ∈ closure
    have hxy : φ (x * y) = 1 := by rw [map_mul, hxe, hye, ht2]
    refine ⟨Or.inl hxy, fun _ => ?_, fun h => ?_⟩
    · -- xy = (t (t⁻¹ x) t⁻¹)(t*t)(t⁻¹ y)
      have e : x * y = (t * (t⁻¹ * x) * t⁻¹) * ((t * t) * (t⁻¹ * y)) := by group
      rw [e]
      exact mul_mem (conj_t_mem _ (hx1 hxe))
        (mul_mem tt_mem_closure (hy1 hye))
    · exact (ht (h.symm.trans hxy)).elim

private theorem schreierPred_inv (ht : φ t ≠ 1) (ht2 : φ t * φ t = 1)
    (x : G) (hx : schreierPred (φ := φ) (t := t) (S := S) x) :
    schreierPred (φ := φ) (t := t) (S := S) x⁻¹ := by
  obtain ⟨hxp, hx0, hx1⟩ := hx
  rcases hxp with hxe | hxe
  · have hinv : φ x⁻¹ = 1 := by rw [map_inv, hxe, inv_one]
    refine ⟨Or.inl hinv, fun _ => ?_, fun h => ?_⟩
    · exact inv_mem (hx0 hxe)
    · exact (ht (h.symm.trans hinv)).elim
  · -- φ x⁻¹ = (φ t)⁻¹ = φ t since φ t * φ t = 1
    have hinv : φ x⁻¹ = φ t := by
      rw [map_inv, hxe, inv_eq_of_mul_eq_one_right ht2]
    refine ⟨Or.inr hinv, fun h => ?_, fun _ => ?_⟩
    · exact (ht (hinv.symm.trans h)).elim
    · -- t⁻¹ x⁻¹ = (t⁻¹ (t⁻¹ x)⁻¹ t) · (t*t)⁻¹ = conj_tinv of (t⁻¹ x)⁻¹, times cap.
      have e : t⁻¹ * x⁻¹ = (t⁻¹ * (t⁻¹ * x)⁻¹ * t) * (t * t)⁻¹ := by group
      rw [e]
      exact mul_mem (conj_tinv_mem _ (inv_mem (hx1 hxe))) (inv_mem tt_mem_closure)

/-- **Index-2 kernel generation (`⊇` direction).** Under the standing
hypotheses, `φ.ker ≤ closure (schreierSet φ t S)`: a kernel element has parity
`1`, and the bundled invariant places it in the Schreier closure. -/
theorem ker_le_closure_schreierSet (htop : closure S = ⊤) (ht : φ t ≠ 1)
    (ht2 : φ t * φ t = 1) (hpar : ∀ s ∈ S, φ s = 1 ∨ φ s = φ t) :
    φ.ker ≤ closure (schreierSet φ t S) := by
  intro g hg
  have hgtop : g ∈ closure S := htop ▸ mem_top g
  have hP : schreierPred (φ := φ) (t := t) (S := S) g :=
    closure_induction (fun s hs => schreierPred_mem hpar s hs) (schreierPred_one ht)
      (fun x y _ _ hx hy => schreierPred_mul ht ht2 x y hx hy)
      (fun x _ hx => schreierPred_inv ht ht2 x hx) hgtop
  exact hP.2.1 (MonoidHom.mem_ker.mp hg)

/-- **Index-2 kernel generation (Reidemeister–Schreier).** Let `G` be a group,
`φ : G →* Q`, `t : G` with `φ t ≠ 1` and `φ t * φ t = 1`, and `S` a generating
set each of whose members has parity `0` or `φ t`. Then the Schreier set
generates `φ.ker`.

This is **Fact (1)** of the hyperelliptic branched-cover route: the explicit
generating set of `ker φ = π_*(π₁(X∖T))` for the degree-2 parity monodromy
`φ : π₁(ℙ¹∖B) → ℤ/2`. The Schreier families `t * s` / `s * t⁻¹` lift to the
branch-cut cycles upstairs; `t * t` lifts to the local ramification meridian
(killed by the puncture-fill van Kampen surjection, Fact (2)). -/
theorem closure_schreierSet_eq_ker (htop : closure S = ⊤) (ht : φ t ≠ 1)
    (ht2 : φ t * φ t = 1) (hpar : ∀ s ∈ S, φ s = 1 ∨ φ s = φ t) :
    closure (schreierSet φ t S) = φ.ker :=
  le_antisymm (closure_schreierSet_le_ker ht2)
    (ker_le_closure_schreierSet htop ht ht2 hpar)

end Jacobians.Topology
