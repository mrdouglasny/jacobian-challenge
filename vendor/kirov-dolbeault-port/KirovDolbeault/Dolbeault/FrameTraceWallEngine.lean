/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedMultiplicityBridge
import KirovDolbeault.Dolbeault.FormTraceInftyFibreNF
import KirovDolbeault.Dolbeault.CanonicalFormDifferential

/-!
# The conservation-of-number engine for the plain value trace (T lane)

Frame-free geometric layer for the residual wall `exists_frameTraceFunctionData_df`
(`FrameTrace.lean`): the **plain value trace**

> `valueTrace F f : ℂ → ℂ`,  `valueTrace F f w = ∑_{y ∈ F⁻¹(coe w)} F.holoRepr y`

of a global meromorphic `F` through the branched cover `𝔉 = f.toRiemannSphere`, together with
the local fibre control needed for its analyticity/meromorphy/residue fields:

* **fibre basics** — every preimage of a finite value `coe z` is a non-pole with
  `holoRepr = z` and local degree `≥ 1`;
* **the sheet decomposition** — through the PROVEN multiplicity-patching engine
  (`MultiplicityPatchingData`: pairwise-disjoint sheets + per-sheet conservation + no-escape),
  near any centre value the fibre splits into per-sheet slices, the trace into per-slice sums;
* **slice enumeration by counting** — a slice's local-degree sum is the sheet weight
  `m = localDeg` and each preimage weighs `≥ 1`, so `m` *distinct exhibited preimages* in a
  slice enumerate it exactly (the conservation-of-number step of Miranda §VIII.3, step 1);
* **the regularity bridges** — `localDeg = 1` at a fibre point gives a nonvanishing
  chart-pullback derivative of `f.holoRepr` (feeding the planar-section/IFT machinery), and
  conversely a fibre point off the canonical-divisor support of an `ω₀ = df` datum is
  unramified.

No frame, no residue here: pure cover geometry over the proven engine.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (conservation of number), §17.
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FrameTraceWall

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.ProperMapDegreeSheets Jacobians.MultiplicityPatching
  Jacobians.MultiplicityPatchingConstruct

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The plain value trace and the fibre `Finset` -/

/-- **The plain value trace** of `F` through the cover `𝔉 = f.toRiemannSphere`, read in the
finite chart of `ℂℙ¹`: at `w : ℂ`, the sum of the junk-free values `F.holoRepr` over the fibre
`𝔉⁻¹(coe w)` (a `finsum`, which is the honest finite sum on the finite fibres of a nonconstant
cover and `0` otherwise). -/
def valueTrace (F f : MeromorphicFunction X) : ℂ → ℂ :=
  fun w => ∑ᶠ y ∈ f.toRiemannSphere ⁻¹' {((w : ℂ) : RiemannSphere)}, F.holoRepr y

/-- The fibre of `𝔉 = f.toRiemannSphere` over `w`, as a `Finset` (nonconstant cover). -/
def fibreFinset (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (w : RiemannSphere) : Finset X :=
  (fibre_finite_of_div_ne_zero f hdiv w).toFinset

@[simp] theorem mem_fibreFinset {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0}
    {w : RiemannSphere} {y : X} :
    y ∈ fibreFinset f hdiv w ↔ f.toRiemannSphere y = w := by
  rw [fibreFinset, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]

theorem coe_fibreFinset (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (w : RiemannSphere) :
    (fibreFinset f hdiv w : Set X) = f.toRiemannSphere ⁻¹' {w} :=
  (fibre_finite_of_div_ne_zero f hdiv w).coe_toFinset

/-- The value trace as an honest `Finset` sum over the fibre. -/
theorem valueTrace_eq_sum_fibreFinset (F f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (w : ℂ) :
    valueTrace F f w = ∑ y ∈ fibreFinset f hdiv (((w : ℂ) : RiemannSphere)), F.holoRepr y := by
  rw [valueTrace, ← coe_fibreFinset f hdiv, finsum_mem_coe_finset]

/-! ## Fibre basics over a finite value -/

/-- A preimage of a finite value is a non-pole. -/
theorem nonpole_of_fibre_coe {f : MeromorphicFunction X} {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere)) : 0 ≤ f.orderAtPoint y := by
  by_contra h
  rw [f.toRiemannSphere_of_pole (not_le.mp h)] at hy
  exact OnePoint.infty_ne_coe z hy

/-- A preimage of a finite value reads that value through `holoRepr`. -/
theorem holoRepr_of_fibre_coe {f : MeromorphicFunction X} {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere)) : f.holoRepr y = z :=
  holoRepr_eq_of_fibre_nonpole f hy (nonpole_of_fibre_coe hy)

/-- **Local degree positivity**: a preimage of a finite value has local degree `≥ 1`. -/
theorem one_le_localDeg_of_fibre_coe (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere)) :
    1 ≤ localDeg f (((z : ℂ) : RiemannSphere)) y := by
  obtain ⟨h1, _, heq⟩ :=
    analyticOrderAt_holoRepr_sub_eq_mult f hdiv hy (nonpole_of_fibre_coe hy)
  rw [heq]
  exact_mod_cast h1

/-- **The simple-point regularity bridge**: at a fibre point of local degree `1`, the
chart-pullback derivative of `f.holoRepr` is nonzero (the planar-section/IFT input). -/
theorem holoRepr_pullback_deriv_ne_zero_of_localDeg_eq_one (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere))
    (h1 : localDeg f (((z : ℂ) : RiemannSphere)) y = 1) :
    deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ)) ((chartAt (H := ℂ) y) y) ≠ 0 := by
  have hnp := nonpole_of_fibre_coe hy
  obtain ⟨_, hord, _⟩ := analyticOrderAt_holoRepr_sub_eq_mult f hdiv hy hnp
  rw [h1] at hord
  -- the shifted pullback has a simple zero, so its derivative is nonzero
  have hg_an : AnalyticAt ℂ (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ))
      ((chartAt (H := ℂ) y) y) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  have hgz_an : AnalyticAt ℂ (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ) - z)
      ((chartAt (H := ℂ) y) y) := hg_an.sub analyticAt_const
  have hd : deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ) - z)
      ((chartAt (H := ℂ) y) y) ≠ 0 :=
    Jacobians.Dolbeault.FormTraceInftyFibre.deriv_ne_zero_of_analyticOrderAt_eq_one hgz_an
      (by exact_mod_cast hord)
  rwa [deriv_sub_const] at hd

/-! ## The sheet decomposition of the trace near a centre

Through the PROVEN multiplicity-patching engine: at any centre value `w₀`, the patching datum
`P` provides pairwise-disjoint sheets `P.U x` around the fibre points `P.xs`, an open value
neighbourhood `P.W ∋ w₀`, the per-sheet conservation `∑_{slice} localDeg = P.m x`, fibre
finiteness, and **no escape**.  We re-read these as `Finset` statements about
`fibreFinset f hdiv (coe z)` for `coe z ∈ P.W`. -/

/-- The patching datum of a nonconstant cover at a centre value (the proven engine). -/
def patchAt (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (w₀ : RiemannSphere) : MultiplicityPatchingData f w₀ :=
  (localMultiplicitySheets_of_nonconstant f hdiv w₀).toPatchingData

/-- **The per-sheet slice** of the fibre over `coe z`: the fibre points lying in the sheet
`P.U x`. -/
def slice {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) (x : X) (z : ℂ) : Finset X :=
  (fibreFinset f hdiv (((z : ℂ) : RiemannSphere))).filter (fun y => y ∈ P.U x)

theorem mem_slice {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0}
    {w₀ : RiemannSphere} {P : MultiplicityPatchingData f w₀} {x : X} {z : ℂ} {y : X} :
    y ∈ slice hdiv P x z ↔
      f.toRiemannSphere y = (((z : ℂ) : RiemannSphere)) ∧ y ∈ P.U x := by
  rw [slice, Finset.mem_filter, mem_fibreFinset]

/-- The slice coincides with the patching engine's set-level slice. -/
theorem coe_slice {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) (x : X) (z : ℂ) :
    (slice hdiv P x z : Set X)
      = P.U x ∩ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))} := by
  ext y
  rw [Finset.mem_coe, mem_slice]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  tauto

/-- **The slice conservation count** (`Finset` form of the engine's `sheetMult_eq`). -/
theorem sum_localDeg_slice {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) :
    ∑ y ∈ slice hdiv P x z, localDeg f (((z : ℂ) : RiemannSphere)) y = P.m x := by
  have h := P.sheetMult_eq x hx _ hz
  rw [← h, ← finsum_mem_coe_finset, coe_slice]

/-- **The fibre splits into the slices** (no-escape + disjointness, `Finset` form): for
`coe z ∈ P.W`, any sum over the fibre is the double sum over the per-sheet slices. -/
theorem sum_fibre_eq_sum_slices {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) (g : X → ℂ) :
    ∑ y ∈ fibreFinset f hdiv (((z : ℂ) : RiemannSphere)), g y
      = ∑ x ∈ P.xs, ∑ y ∈ slice hdiv P x z, g y := by
  classical
  rw [← Finset.sum_biUnion ?hdisj]
  · congr 1
    ext y
    simp only [Finset.mem_biUnion, mem_fibreFinset, mem_slice]
    constructor
    · intro hy
      have hyW : y ∈ f.toRiemannSphere ⁻¹' P.W := by
        rw [Set.mem_preimage, hy]; exact hz
      obtain ⟨x, hx, hyU⟩ := Set.mem_iUnion₂.mp (P.preimage_W_subset hyW)
      exact ⟨x, hx, hy, hyU⟩
    · rintro ⟨x, _, hy, _⟩
      exact hy
  · intro x hx x' hx' hne
    intro s hs hs' y hy
    have h1 : y ∈ slice hdiv P x z := hs hy
    have h2 : y ∈ slice hdiv P x' z := hs' hy
    rw [mem_slice] at h1 h2
    exact absurd (Set.mem_inter h1.2 h2.2)
      (Set.disjoint_iff.mp
        (P.U_pairwiseDisjoint x (Finset.mem_coe.mp hx) x' (Finset.mem_coe.mp hx') hne) ·)

/-- **The trace splits into the per-sheet slice sums** near a centre. -/
theorem valueTrace_eq_sum_slices (F f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {w₀ : RiemannSphere}
    (P : MultiplicityPatchingData f w₀) {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) :
    valueTrace F f z = ∑ x ∈ P.xs, ∑ y ∈ slice hdiv P x z, F.holoRepr y := by
  rw [valueTrace_eq_sum_fibreFinset F f hdiv, sum_fibre_eq_sum_slices hdiv P hz]

/-! ## Slice enumeration by counting -/

/-- The slice at the centre value itself is the singleton of its sheet's fibre point. -/
theorem slice_centre_eq_singleton {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere))) {x : X} (hx : x ∈ P.xs) :
    slice hdiv P x c = {x} := by
  ext y
  rw [mem_slice, Finset.mem_singleton]
  constructor
  · rintro ⟨hyfib, hyU⟩
    -- `y` is a fibre point of the centre, so `y ∈ P.xs`; distinct fibre points have
    -- disjoint sheets, and `y` lies in its own sheet, so `y = x`.
    have hyxs : y ∈ P.xs := by
      have : y ∈ (P.xs : Set X) := by rw [P.xs_coe]; exact hyfib
      exact this
    by_contra hne
    exact Set.disjoint_iff.mp (P.U_pairwiseDisjoint y hyxs x hx hne)
      (Set.mem_inter (P.mem_U_self y hyxs) hyU)
  · rintro rfl
    have : y ∈ (P.xs : Set X) := hx
    rw [P.xs_coe] at this
    exact ⟨this, P.mem_U_self y hx⟩

/-- **The sheet weight is the local degree of its fibre point** (read the conservation at the
centre, where the slice is the singleton). -/
theorem patch_m_eq_localDeg {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {c : ℂ} (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere))) {x : X}
    (hx : x ∈ P.xs) :
    P.m x = localDeg f (((c : ℂ) : RiemannSphere)) x := by
  have h := sum_localDeg_slice hdiv P hx P.w₀_mem_W
  rw [slice_centre_eq_singleton hdiv P hx, Finset.sum_singleton] at h
  exact h.symm

/-- **The slice cardinality is bounded by the sheet weight** (each preimage weighs `≥ 1`). -/
theorem slice_card_le {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) :
    ((slice hdiv P x z).card : ℤ) ≤ P.m x := by
  have hone : ∀ y ∈ slice hdiv P x z, (1 : ℤ) ≤ localDeg f (((z : ℂ) : RiemannSphere)) y :=
    fun y hy => one_le_localDeg_of_fibre_coe f hdiv (mem_slice.mp hy).1
  calc ((slice hdiv P x z).card : ℤ)
      = (slice hdiv P x z).card • (1 : ℤ) := by simp
    _ ≤ ∑ y ∈ slice hdiv P x z, localDeg f (((z : ℂ) : RiemannSphere)) y :=
        Finset.card_nsmul_le_sum _ _ _ hone
    _ = P.m x := sum_localDeg_slice hdiv P hx hz

/-- **Slice enumeration**: if `m` distinct exhibited preimages lie in a slice of weight `m`,
they exhaust it (conservation of number). -/
theorem slice_eq_of_exhibited {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) (cand : Finset X)
    (hsub : cand ⊆ slice hdiv P x z) (hcard : P.m x ≤ (cand.card : ℤ)) :
    slice hdiv P x z = cand :=
  (Finset.eq_of_subset_of_card_le hsub (by
    exact_mod_cast le_trans (slice_card_le hdiv P hx hz) hcard)).symm

/-! ## The unramified slice: a single moving preimage

At a sheet of weight `1`, the slice over every nearby value is a single point, and any
exhibited preimage in the sheet *is* that point.  This feeds the planar-section identification:
the section value `chart⁻¹ (s z)` is a preimage in the sheet, hence THE slice point. -/

/-- A slice of weight `1` over a finite value is a singleton consisting of any exhibited
preimage in the sheet. -/
theorem slice_eq_singleton_of_weight_one {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) {w₀ : RiemannSphere}
    (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) (hm : P.m x = 1) {y : X}
    (hyfib : f.toRiemannSphere y = (((z : ℂ) : RiemannSphere))) (hyU : y ∈ P.U x) :
    slice hdiv P x z = {y} :=
  slice_eq_of_exhibited hdiv P hx hz {y}
    (Finset.singleton_subset_iff.mpr (mem_slice.mpr ⟨hyfib, hyU⟩))
    (by rw [hm, Finset.card_singleton]; norm_num)

end Jacobians.Dolbeault.FrameTraceWall

end
