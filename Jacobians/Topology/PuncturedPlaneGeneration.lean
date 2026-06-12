/-
# G3/G4 — the generation induction package (statement layer + base case)

Issue #171 B1, `docs/planning/B1_GENERATION_ROUTE.md` rungs **G3/G4**
(binary-split design, third-pass notes).

**The package.** `PuncturedCellSystem T x₀` fixes, for each puncture
`s ∈ T`, a once-punctured cell containing the basepoint together with the
two pins that make the induction true: the cell lasso winds once (in some
orientation) around `s` and zero around every other puncture.  The
winding-level pin alone is FALSE as an induction hypothesis (balanced
presentations of perfect groups — route doc, second pass); the cell-lasso
structure alone does not tie the cell to `s` (a once-punctured cell can
enclose other punctures).  The conjunction is the right inductive object.

**Headline (target)**: for every admissible system, the normal closure of
its cell lassos is all of `π₁(ℂ ∖ T, x₀)`.  This file lands the statement
layer and the degenerate base case `T = ∅`; the binary-split induction
(`fromPath_mem_of_two_open` + `halfPlaneHomeo`/`complCongr` transport) is
the next rung.
-/
import Jacobians.Topology.CoverGeneration
import Jacobians.Topology.CellLassoPower
import Jacobians.Topology.HalfPlaneHomeo

namespace Jacobians.Topology

open Set

local notation "Qmk" => Path.Homotopic.Quotient.mk

/-- **An admissible cell system** on the `T`-punctured plane: for each
puncture a once-punctured cell containing the basepoint, whose lasso winds
once around its own puncture (`winding_self`, either orientation) and zero
around every other (`winding_off`). -/
structure PuncturedCellSystem (T : Finset ℂ)
    (x₀ : {w : ℂ // w ∉ (T : Set ℂ)}) where
  /-- the cell around each puncture -/
  cell : (s : T) → Set {w : ℂ // w ∉ (T : Set ℂ)}
  /-- the puncture of the cell's once-punctured-plane presentation -/
  center : T → ℂ
  /-- the once-punctured presentation -/
  homeo : (s : T) → (cell s) ≃ₜ {w : ℂ // w ≠ center s}
  /-- every cell contains the basepoint -/
  mem_cell : ∀ s, x₀ ∈ cell s
  /-- the lasso winds once (in some orientation) around its own puncture -/
  winding_self : ∀ s : T,
    windingHom (Finset.mem_coe.mpr s.2) x₀
        (cellLasso (homeo s) (mem_cell s)) = Multiplicative.ofAdd 1 ∨
    windingHom (Finset.mem_coe.mpr s.2) x₀
        (cellLasso (homeo s) (mem_cell s)) = Multiplicative.ofAdd (-1)
  /-- the lasso does not wind around any other puncture -/
  winding_off : ∀ s s' : T, s' ≠ s →
    windingHom (Finset.mem_coe.mpr s'.2) x₀
      (cellLasso (homeo s) (mem_cell s)) = 1

namespace PuncturedCellSystem

variable {T : Finset ℂ} {x₀ : {w : ℂ // w ∉ (T : Set ℂ)}}

/-- The lasso classes of the system. -/
noncomputable def lassos (C : PuncturedCellSystem T x₀) : Set (FundamentalGroup _ x₀) :=
  Set.range fun s : T => cellLasso (C.homeo s) (C.mem_cell s)

end PuncturedCellSystem

/-- The empty-puncture plane is simply connected (it is homeomorphic to `ℂ`). -/
theorem subsingleton_fundamentalGroup_compl_empty
    (x₀ : {w : ℂ // w ∉ ((∅ : Finset ℂ) : Set ℂ)}) :
    Subsingleton (FundamentalGroup {w : ℂ // w ∉ ((∅ : Finset ℂ) : Set ℂ)} x₀) := by
  have hcongr : (((∅ : Finset ℂ) : Set ℂ)ᶜ : Set ℂ) = Set.univ := by
    simp
  have φ : {w : ℂ // w ∉ ((∅ : Finset ℂ) : Set ℂ)} ≃ₜ ℂ :=
    (Homeomorph.setCongr hcongr).trans (Homeomorph.Set.univ ℂ)
  have e := pi1MulEquivOfHomeomorph φ x₀
  haveI : SimplyConnectedSpace ℂ := inferInstance
  haveI : Subsingleton (Path.Homotopic.Quotient (φ x₀) (φ x₀)) := inferInstance
  haveI : Subsingleton (FundamentalGroup ℂ (φ x₀)) := by
    refine ⟨fun a b => ?_⟩
    have h : FundamentalGroup.toPath a = FundamentalGroup.toPath b :=
      Subsingleton.elim _ _
    exact congrArg FundamentalGroup.fromPath h
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- **Base case `T = ∅`** of the generation induction: over the unpunctured
plane every subgroup of the (trivial) fundamental group is everything; in
particular the normal closure of the (empty) lasso family is `⊤`. -/
theorem normalClosure_lassos_eq_top_of_empty
    (x₀ : {w : ℂ // w ∉ ((∅ : Finset ℂ) : Set ℂ)})
    (C : PuncturedCellSystem ∅ x₀) :
    Subgroup.normalClosure C.lassos = ⊤ := by
  haveI := subsingleton_fundamentalGroup_compl_empty x₀
  exact Subsingleton.elim _ _

/-- The once-punctured plane in `Finset`-complement form is homeomorphic to
its `≠`-form. -/
noncomputable def singletonComplHomeo (a : ℂ) :
    {w : ℂ // w ∉ (({a} : Finset ℂ) : Set ℂ)} ≃ₜ {w : ℂ // w ≠ a} :=
  Homeomorph.setCongr (s := ((({a} : Finset ℂ) : Set ℂ)ᶜ : Set ℂ))
    (t := {w : ℂ | w ≠ a}) (by ext w; simp)

/-- **Base case `T = {a}`** of the generation induction: over the
once-punctured plane, the normal closure (indeed the plain closure) of any
admissible system's lasso is everything.  No winding computation around the
ambient generator is needed: the whole space is itself an admissible cell,
so `π₁` is cyclic on the universe-cell lasso (G2), and the winding pin
forces the system lasso's exponent to be a unit. -/
theorem normalClosure_lassos_eq_top_of_singleton (a : ℂ)
    (x₀ : {w : ℂ // w ∉ (({a} : Finset ℂ) : Set ℂ)})
    (C : PuncturedCellSystem {a} x₀) :
    Subgroup.normalClosure C.lassos = ⊤ := by
  classical
  -- the universe cell: the whole space presented as a once-punctured plane
  let ψ : (Set.univ : Set {w : ℂ // w ∉ (({a} : Finset ℂ) : Set ℂ)})
      ≃ₜ {w : ℂ // w ≠ a} :=
    (Homeomorph.Set.univ _).trans (singletonComplHomeo a)
  have hx₀univ : x₀ ∈ (Set.univ : Set {w : ℂ // w ∉ (({a} : Finset ℂ) : Set ℂ)}) :=
    Set.mem_univ _
  let u := cellLasso ψ hx₀univ
  -- every element is a power of the universe lasso (π₁ is cyclic on `u`)
  have hcyc : ∀ g : FundamentalGroup _ x₀, ∃ m : ℤ, g = u ^ m := by
    intro g
    obtain ⟨γ, hγ⟩ : ∃ γ : Path x₀ x₀,
        FundamentalGroup.fromPath (Qmk γ) = g :=
      ⟨(FundamentalGroup.toPath g).out,
        congrArg FundamentalGroup.fromPath (Quotient.out_eq _)⟩
    obtain ⟨m, hm⟩ := fromPath_eq_cellLasso_zpow ψ hx₀univ γ
      (fun s => Set.mem_univ _)
    exact ⟨m, by rw [← hγ, hm]⟩
  -- the puncture index and the system's lasso
  have hamem : a ∈ ({a} : Finset ℂ) := Finset.mem_singleton_self a
  let s₀ : ({a} : Finset ℂ) := ⟨a, hamem⟩
  let ℓ := cellLasso (C.homeo s₀) (C.mem_cell s₀)
  have hℓmem : ℓ ∈ C.lassos := ⟨s₀, rfl⟩
  -- the system lasso is a power of the universe lasso
  obtain ⟨n, hn⟩ := hcyc ℓ
  -- winding algebra: the exponent is a unit
  have hwind := C.winding_self s₀
  have hpow : windingHom (Finset.mem_coe.mpr s₀.2) x₀ ℓ
      = Multiplicative.ofAdd (n * Multiplicative.toAdd
          (windingHom (Finset.mem_coe.mpr s₀.2) x₀ u)) := by
    rw [hn, map_zpow]
    conv_lhs => rw [← ofAdd_toAdd (windingHom (Finset.mem_coe.mpr s₀.2) x₀ u)]
    rw [← ofAdd_zsmul, smul_eq_mul]
  have hunit : n = 1 ∨ n = -1 := by
    have hnw : n * Multiplicative.toAdd
        (windingHom (Finset.mem_coe.mpr s₀.2) x₀ u) = 1 ∨
        n * Multiplicative.toAdd
          (windingHom (Finset.mem_coe.mpr s₀.2) x₀ u) = -1 := by
      rcases hwind with h | h
      · left
        have h2 := hpow.symm.trans h
        exact Multiplicative.ofAdd.injective h2
      · right
        have h2 := hpow.symm.trans h
        exact Multiplicative.ofAdd.injective h2
    have : IsUnit n := by
      rcases hnw with h | h
      · exact IsUnit.of_mul_eq_one _ h
      · refine IsUnit.of_mul_eq_one
          (-(Multiplicative.toAdd (windingHom (Finset.mem_coe.mpr s₀.2) x₀ u)))
          ?_
        linarith [h]
    exact Int.isUnit_iff.mp this
  -- closure of the system lasso is everything
  have hclos : Subgroup.closure ({ℓ} : Set (FundamentalGroup _ x₀)) = ⊤ := by
    have hℓu : Subgroup.closure ({ℓ} : Set (FundamentalGroup _ x₀))
        = Subgroup.closure {u} := by
      rcases hunit with h | h
      · rw [hn, h, zpow_one]
      · rw [hn, h, zpow_neg, zpow_one]
        exact Subgroup.closure_singleton_inv u
    rw [hℓu, Subgroup.eq_top_iff']
    intro g
    obtain ⟨m, hm⟩ := hcyc g
    rw [hm]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_singleton _)) _
  -- conclude through `closure ≤ normalClosure`
  rw [eq_top_iff, ← hclos]
  exact le_trans (Subgroup.closure_mono (Set.singleton_subset_iff.mpr hℓmem))
    Subgroup.closure_le_normalClosure

end Jacobians.Topology
