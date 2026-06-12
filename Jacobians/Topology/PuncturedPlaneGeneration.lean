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

end Jacobians.Topology
