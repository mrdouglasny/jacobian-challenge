/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailSurjectivity
import KirovDolbeault.Dolbeault.TailFrameWitness

/-!
# The genus-0 arithmetic atom from the meromorphic-frame residue atom (G0 lane)

The G0 atom `hga : 𝔘.h1Dim 0 = 0` at `kirovGenus X = 0` (`docs/planning/G0_BLOCKER.md`)
through the tail tower, reduced to ONE named analytic input.

## The reduction

With both tail towers landed, the pipeline `TailPairFrame X → PairingSurjective →
TailRiemannRoch X → hga` is **genus-free** (`TailPairFrame.pairingSurjective` and
`TailPairFrame.tailRiemannRoch` take no genus hypothesis).  The only genus-dependent link is
frame EXISTENCE: `nonempty_tailPairFrame_of_kirovGenus_pos` (`TailFrameWitness.lean`) builds
the frame from a nonzero HOLOMORPHIC 1-form, which exists only at `kirovGenus X > 0`.

But the frame form's type is already meromorphic: `TailPairFrame.data` is a
`CanonicalForm17Data X` whose `ω₀` is a `MeromorphicOneForm X` — and
`nonempty_canonicalForm17Data` (`CanonicalFormDifferential.lean`) constructs such a datum
UNCONDITIONALLY (`ω₀ = df` of a nonconstant meromorphic `f`, which exists at every genus).
Its slot family is free as well: `slot p := formCoeff ω₀.toFun p` is meromorphic of exact
order `K p` by the datum's own `order_eq`.  So the ONLY missing frame field at genus 0 is the
pair-frame residue theorem `∑ₚ Res_p(F·ω₀) = 0` for a MEROMORPHIC `ω₀` — isolated here as

* `CanonicalForm17Data.ResidueAtom` — the named atom (the exact `resSum` field shape).

It cannot be factored through the proven Gate-A engine
(`SerreResidueTheorem.residueTheorem_unconditional`): a factorization `F·ω₀ = α·g` with `α`
holomorphic would force `div ω₀ ≥ div h` for some global `h` with `ω₀/h` holomorphic, which
is impossible at genus 0 (`deg div ω₀ = −2 < 0`, no nonzero holomorphic forms exist).  The
engine's whole §5 slit tower is parameterized by `coeffAt (α : HolomorphicOneForms X)`
throughout, so the honest discharge is the engine's meromorphic-frame generalization (or the
trace-to-`ℙ¹` of the plain value trace for `ω₀ = df`) — tracked in
`docs/planning/G0_BLOCKER.md`.

## Main declarations

* `CanonicalForm17Data.ResidueAtom` — the single named analytic input: `∑Res(F·ω₀) = 0` over
  `supp(div F) ∪ supp K`, in planar Laurent coefficients, for every meromorphic `F`.
* `TailPairFrame.ofResidueAtom` — the frame from ANY canonical datum + its atom (genus-free).
* `residueAtom_of_form` / `exists_residueAtom_of_kirovGenus_pos` — satisfiability evidence:
  at `kirovGenus X > 0` the atom is a THEOREM (Gate-A through the residue bridge), so the
  named hypothesis is the standard residue theorem, not a placeholder.
* `tailRiemannRoch_of_residueAtom` — `TailRiemannRoch X` from the atom (any genus).
* `h1Dim_zero_eq_zero_of_residueAtom` — **the G0 deliverable**: the `hga` atom
  `𝔘.h1Dim 0 = 0` at `kirovGenus X = 0`, conditional on the residue atom only.
* `exists_serreDualityData_of_genus_zero_of_residueAtom` — the keystone `g = 0` leg under
  the same single input.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI; Forster,
*Lectures on Riemann Surfaces* (GTM 81), §17.4.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The named atom -/

/-- **The meromorphic-frame residue atom** (the single remaining analytic input of the G0
lane; `docs/planning/G0_BLOCKER.md` discharge shape 1): for the canonical frame `(ω₀, K)` of
the datum, the planar residue sum of `F·ω₀` vanishes over `supp(div F) ∪ supp K`, for every
global meromorphic `F`.  This is verbatim the `TailPairFrame.resSum` field at the canonical
slot family `slot p = formCoeff ω₀.toFun p`.

Mathematically TRUE on every compact Riemann surface (the residue theorem for meromorphic
1-forms, Forster §17.3 / Miranda Ch. VI); a THEOREM at `kirovGenus X > 0`
(`residueAtom_of_form` below, via Gate A).  At genus 0 it is the open analytic atom: the
Gate-A engine is parameterized by a HOLOMORPHIC `ω₀` and no factorization `F·ω₀ = α·g` with
`α` holomorphic exists at genus 0. -/
def CanonicalForm17Data.ResidueAtom (data : CanonicalForm17Data X) : Prop :=
  ∀ F : MeromorphicFunction X,
    ∑ p ∈ F.div.support ∪ data.K.support,
      planarCoeff (-1)
        (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * formCoeff data.ω₀.toFun p ζ)
        ((chartAt (H := ℂ) p) p) = 0

/-! ## The frame from a datum + its atom (genus-free) -/

/-- **The tail pair frame from a canonical datum and its residue atom.**  The slot family is
the coordinate coefficient `formCoeff ω₀.toFun p` of the datum's (meromorphic) frame form —
meromorphic at the chart centre by the form's own meromorphy, of exact order `K p` by the
datum's `order_eq`.  The residue field is the atom verbatim.  No genus hypothesis. -/
def TailPairFrame.ofResidueAtom (data : CanonicalForm17Data X)
    (hres : data.ResidueAtom) : TailPairFrame X where
  data := data
  slot := fun p => formCoeff data.ω₀.toFun p
  slot_mero := fun p => data.ω₀.meromorphic p
  slot_order := fun p => data.order_eq p
  resSum := hres

/-- Frame existence from the residue atom (genus-free). -/
theorem nonempty_tailPairFrame_of_residueAtom
    (h : ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    Nonempty (TailPairFrame X) := by
  obtain ⟨data, hres⟩ := h
  exact ⟨TailPairFrame.ofResidueAtom data hres⟩

/-! ## Satisfiability evidence: the atom is a THEOREM at positive genus -/

/-- **The residue atom holds for the holomorphic-form datum** (Gate A through the residue
bridge): for a nonzero holomorphic `α`, the datum `canonicalDataOfForm α hα` satisfies its
own residue atom — `resSum_planar` at the support `supp(div F) ∪ supp K`, with
`formCoeff (holToMero α).toFun p = coeffAt α p` definitionally. -/
theorem residueAtom_of_form (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    (canonicalDataOfForm α hα).ResidueAtom := by
  intro F
  have h := resSum_planar α F
    (S := F.div.support ∪ (canonicalDataOfForm α hα).K.support) Finset.subset_union_left
  rw [← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rfl

/-- At `kirovGenus X > 0` the residue atom is satisfiable — the named hypothesis of the G0
lane is the standard residue theorem, proven on the positive-genus side of the genus split. -/
theorem exists_residueAtom_of_kirovGenus_pos (hg : 0 < kirovGenus X) :
    ∃ data : CanonicalForm17Data X, data.ResidueAtom := by
  have hex : ∃ α : HolomorphicOneForms X, α ≠ 0 := by
    by_contra hcon
    push Not at hcon
    haveI hsub : Subsingleton (HolomorphicOneForms X) :=
      ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h0 : kirovGenus X = 0 := by
      unfold kirovGenus
      exact Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨α, hα⟩ := hex
  exact ⟨canonicalDataOfForm α hα, residueAtom_of_form α hα⟩

/-! ## The G0 deliverables: `TailRiemannRoch`, the `hga` atom, and the keystone `g = 0` leg -/

/-- **Tail Riemann–Roch from the residue atom** (any genus): the atom builds the frame, and
the frame-only tower (`TailPairFrame.pairingSurjective` → `TailPairFrame.tailRiemannRoch`)
does the rest. -/
theorem tailRiemannRoch_of_residueAtom (data : CanonicalForm17Data X)
    (hres : data.ResidueAtom) : TailRiemannRoch X :=
  (TailPairFrame.ofResidueAtom data hres).tailRiemannRoch

/-- **The G0 atom `hga` from the residue atom**: `h¹(𝒪) = 0` at `kirovGenus X = 0`, at any
locally realizable finite cover — the exact scalar input of
`exists_serreDualityData_of_arithmeticGenus_zero` (`G0_BLOCKER.md`), conditional on the
meromorphic-frame residue atom ONLY. -/
theorem h1Dim_zero_eq_zero_of_residueAtom (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (data : CanonicalForm17Data X) (hres : data.ResidueAtom) (hg0 : kirovGenus X = 0) :
    𝔘.h1Dim (0 : Divisor X) = 0 :=
  h1Dim_zero_eq_zero_of_kirovGenus_zero 𝔘 hR (tailRiemannRoch_of_residueAtom data hres) hg0

/-- The uniform genus identity `h¹(𝒪) = kirovGenus X` from the residue atom (any genus, any
locally realizable cover). -/
theorem h1Dim_zero_eq_kirovGenus_of_residueAtom (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (data : CanonicalForm17Data X) (hres : data.ResidueAtom) :
    𝔘.h1Dim (0 : Divisor X) = kirovGenus X :=
  h1Dim_zero_eq_kirovGenus_of_tailRR 𝔘 hR (tailRiemannRoch_of_residueAtom data hres)

/-- **The keystone `g = 0` leg from the residue atom**: `Nonempty (SerreDualityData 𝔘)` at
`kirovGenus X = 0`, with the `hga` scalar atom supplied by the tail tower under the single
named input. -/
theorem exists_serreDualityData_of_genus_zero_of_residueAtom (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (data : CanonicalForm17Data X) (hres : data.ResidueAtom)
    (hg0 : kirovGenus X = 0) :
    Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_of_genus_zero_of_tailRR 𝔘 hR
    (tailRiemannRoch_of_residueAtom data hres) hg0

/-! ## The genus-uniform frame split

Combining the unconditional positive-genus witness (`TailFrameWitness.lean`) with the atom
route: frame existence — hence `TailRiemannRoch X`, hence `h¹(𝒪) = g` at the canonical cover
— needs the residue atom only in the `kirovGenus X = 0` case. -/

/-- **The genus-split frame existence**: a tail pair frame exists given the residue atom in
the genus-0 case only (`kirovGenus X > 0` is covered by the holomorphic-form witness). -/
theorem nonempty_tailPairFrame_of_genus_split
    (h0 : kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    Nonempty (TailPairFrame X) := by
  rcases Nat.eq_zero_or_pos (kirovGenus X) with hg | hg
  · exact nonempty_tailPairFrame_of_residueAtom (h0 hg)
  · exact nonempty_tailPairFrame_of_kirovGenus_pos hg

/-- **The canonical-cover genus identity under the genus-split input**: `h¹(𝒪) = kirovGenus`
at the canonical chart-disk cover (the Layer-3 flip target), given the residue atom in the
genus-0 case only. -/
theorem h1Dim_zero_chartDiskCover_eq_kirovGenus_of_genus_split
    (h0 : kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    (chartDiskCover (X := X)).toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X := by
  obtain ⟨P⟩ := nonempty_tailPairFrame_of_genus_split h0
  exact h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame' P

end Dolbeault

end Jacobians

end
