/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.CoboundaryVanish
import KirovDolbeault.Dolbeault.FineResidue.OmegaWitness
import KirovDolbeault.Dolbeault.HoloRep
import KirovDolbeault.Dolbeault.GlobalResidueConstruct

/-!
# R7 — the germ→coefficient descent: `resFunctional` becomes a functional on `cechH1 K`

The descent rung of the fine-sheaf residue ladder (`docs/planning/R6_HANDOFF.md`, "the prize
lap"): connect the **germ-level** Čech complex of the port (`CechComplex.lean`: cochains are
codiscrete germ classes `MGerm`, `cechH1 K = Z¹/B¹` via `submoduleOf`) to the **chart-coefficient**
fine-sheaf residue engine (lanes R0–R5: `resFunctional`, `glueCoeff`,
`resFunctional_eq_zero_of_coboundary`), producing the `resCocycle`/`vanish_coboundary` fields of
the port's isolated Cousin interface `CousinResidueData` (`GlobalResidueConstruct.lean`).

## The three layers

* **Extraction (`cocycleFn`).** A 1-cocycle `c ∈ Z¹(𝒪_K)` on the chart-disk cover assigns to each
  overlap a *codiscrete germ class*; raw representatives carry removable-singularity junk, so the
  extraction goes through the proven `holoFn` limit-repair (`HoloRep.lean`), which returns the
  honest analytic representative.  This needs the overlap germs to be `𝒪`-classes
  (`OmegaDGerm 0`), which holds when no pole of `K` lies on an overlap — the **K-point refinement
  discipline** of `Glue.lean`/`OmegaWitness.lean`, packaged here as `SeparatesPoles 𝔇 K` (poles
  of `K` lie in single cover sets).  Diagonal pairs get the zero function (the cocycle identity
  forces the diagonal germ to vanish).  The extracted family satisfies `SmoothOnOverlaps`,
  `IsOverlapCocycle`, `HolomorphicOnOverlaps`, so `glueCoeff 𝔇 (cocycleFn …) g ∈ oneOneCoeff 𝔇`
  by the R3 glue law, and `resFunctional` applies.

* **Linearity & well-definedness (`resCocycle`).** Different germ representatives agree
  *pointwise on the overlaps* (codiscrete agreement + continuity of the analytic representatives,
  `eq_at_of_toGerm_eq`), and `resFunctional ∘ glueCoeff` only ever reads overlap values
  (`resFunctional_congr_chartImage`), so `c ↦ resFunctional (glueCoeff (cocycleFn c) g)` is a
  ℂ-**linear** functional on `Z¹(𝒪_K)` — the `resCocycle` field.

* **Coboundary vanishing & the liftQ descent.** For a coboundary `δ⁰f` with `f` a 0-cochain of
  `𝒪`-classes (`sections0 0`), the extracted data is exactly the `(w, h)`-shape of R5's
  `resFunctional_eq_zero_of_coboundary`, so the functional kills it
  (`resCocycle_eq_zero_of_holomorphic_coboundary`).  When `K ≤ 0` (in particular `K = 0`, the
  genus-1 canonical divisor) **every** coboundary is of this shape, giving the full
  `vanish_coboundary` field (`resCocycle_vanish_coboundary_of_nonpos`) and hence the descended
  functional on `cechH1 K` (`Submodule.liftQ`, exactly the port's `CousinResidueData.res`
  packaging).  For `K > 0` somewhere (genus ≥ 2), coboundary 0-cochains of `𝒪_K` carry *scalar*
  poles at the K-points (the forms `h·ω₀` are holomorphic, the scalars are not), and their
  vanishing is the residue-theorem leg that needs the (higher-order) Mittag–Leffler tie — a
  genuine R6-class gap, taken as a hypothesis here and recorded in
  `docs/planning/R7_BLOCKER.md`.

## Conditionality on R6 (in flight, separate branch)

`MLTie.lean` is being finished in parallel and is **not imported**.  Its outputs are packaged as
the hypothesis structure `R6Outputs`, whose fields copy the statement shapes of the in-flight
`resFunctional_mlGlue` / `resFunctional_mlCocycle_residue_one` *verbatim* (over local copies of
the ML-datum definitions in the `R6Shape` namespace, same orientation contract
`w i j = p_i − p_j`).  When R6 lands, `R6Outputs` is inhabited by a two-line bridge.  The final
assembly `cousinResidueData_of_descent` builds the port's `CousinResidueData 𝔇.toFiniteCover K`
from the proven `resCocycle` plus the two named open legs (`hvanish`, `hnondeg`).

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.6.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

-- Same permissive transparency as the sibling FineResidue files (the `SmoothCFunctions`
-- coercions of `rhoC` need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### A. Germ classes pin continuous representatives pointwise

`MGerm` identifies functions agreeing off a discrete set.  On a Riemann surface no point is
isolated (`nhdsNE_neBot`), so two representatives that are *continuous* at a point of the open
agree **at** the point: codiscrete agreement gives punctured-neighbourhood agreement, and both
values are the (unique) limits. -/

omit [Nonempty X] in
/-- **Continuous representatives of equal germ classes agree pointwise.**  If the `↥V`-germ
classes of `f, f' : X → ℂ` agree and both are continuous at `x ∈ V`, then `f x = f' x`. -/
theorem eq_at_of_toGerm_eq {V : Opens X} {f f' : X → ℂ}
    (hg : toGerm V (fun v => f v.1) = toGerm V (fun v => f' v.1))
    {x : X} (hx : x ∈ V) (hf : ContinuousAt f x) (hf' : ContinuousAt f' x) :
    f x = f' x := by
  haveI := nhdsNE_neBot x
  rw [toGerm_eq_iff] at hg
  have hev : f =ᶠ[𝓝[≠] x] f' := by
    refine eventually_nhdsNE_of_subtype hx (fun z => f z = f' z) ?_
    filter_upwards [hg ⟨x, hx⟩] with w hw
    exact hw
  have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) := hf.continuousWithinAt.tendsto
  have h2 : Tendsto f (𝓝[≠] x) (𝓝 (f' x)) :=
    (hf'.continuousWithinAt.tendsto).congr' hev.symm
  exact tendsto_nhds_unique h1 h2

/-! ### B. Pole separation and the `𝒪_K ⊆ 𝒪` comparison off the poles -/

omit [Nonempty X] in
/-- Where `K ≤ 0`, sections of `𝒪_K` are sections of `𝒪` (the order bound `≥ −K ≥ 0` is at least
the holomorphy bound). -/
theorem OmegaD_le_zero_of_nonpos {K : Divisor X} {V : Opens X} (hK : ∀ x ∈ V, K x ≤ 0) :
    OmegaD K V ≤ OmegaD (0 : Divisor X) V := by
  rintro f ⟨hmer, hord⟩
  refine ⟨hmer, fun v => le_trans ?_ (hord v)⟩
  have h0 : ((0 : Divisor X) v.1 : ℤ) = 0 := rfl
  have e1 : -(((0 : Divisor X) v.1 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
    rw [h0]; simp
  have e2 : -((K v.1 : ℤ) : WithTop ℤ) = ((-(K v.1) : ℤ) : WithTop ℤ) := rfl
  rw [e1, e2]
  exact_mod_cast neg_nonneg.mpr (hK v.1 v.2)

omit [Nonempty X] in
/-- Germ-class version of `OmegaD_le_zero_of_nonpos`. -/
theorem OmegaDGerm_le_zero_of_nonpos {K : Divisor X} {V : Opens X} (hK : ∀ x ∈ V, K x ≤ 0) :
    OmegaDGerm K V ≤ OmegaDGerm (0 : Divisor X) V :=
  Submodule.map_mono (OmegaD_le_zero_of_nonpos hK)

/-- **The K-point refinement discipline of the chart-disk cover** (the cover constraint recorded
in `Glue.lean` / `OmegaWitness.lean` / `R_LANE_PROGRESS.log`): on every overlap of two *distinct*
cover sets the divisor `K` is non-positive — equivalently, each pole of `K` lies in a single
cover set.  Under this, `𝒪_K`-germs on overlaps are honest `𝒪`-germs, which is what the
`holoFn` extraction consumes.  At `K = 0` (genus 1) every cover qualifies. -/
def SeparatesPoles (K : Divisor X) : Prop :=
  ∀ i j : 𝔇.toFiniteCover.ι, i ≠ j → ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), K x ≤ 0

omit [Nonempty X] in
theorem separatesPoles_of_nonpos {K : Divisor X} (hK : ∀ x, K x ≤ 0) :
    SeparatesPoles 𝔇 K :=
  fun _ _ _ x _ => hK x

/-! ### C. The germ→chart-coefficient extraction -/

variable {K : Divisor X}

omit [Nonempty X] in
/-- Off-diagonal overlap germs of a `Z¹(𝒪_K)`-cocycle are `𝒪`-classes (pole separation). -/
theorem cocycle_pair_mem_zero (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι}
    (hij : i ≠ j) :
    (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (i, j)
      ∈ OmegaDGerm (0 : Divisor X) (𝔇.U i ⊓ 𝔇.U j) :=
  OmegaDGerm_le_zero_of_nonpos (fun x hx => hsep i j hij x hx) (c.2.2 (i, j))

/-- **The germ→chart-coefficient extraction**: the scalar overlap family of a Čech 1-cocycle
`c ∈ Z¹(𝒪_K)` on the chart-disk cover.  Off the diagonal it is the canonical analytic
representative (`holoFn`, the limit-repair that discards codiscrete junk) of the overlap germ
`c (i,j)`; on the diagonal it is `0` (the value the cocycle identity forces).  Values off the
overlaps are junk and never consumed (the R1/R2 membership-guarded discipline). -/
noncomputable def cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i j => if h : i = j then 0 else holoFn (cocycle_pair_mem_zero 𝔇 hsep c h)

omit [Nonempty X] in
@[simp] theorem cocycleFn_diag (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) (j : 𝔇.toFiniteCover.ι) :
    cocycleFn 𝔇 hsep c j j = 0 := by
  simp [cocycleFn]

omit [Nonempty X] in
/-- The extraction reads back the germ on its own overlap (off-diagonal). -/
theorem toGerm_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι}
    (hij : i ≠ j) :
    toGerm (𝔇.U i ⊓ 𝔇.U j) (fun v => cocycleFn 𝔇 hsep c i j v.1)
      = (c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (i, j) := by
  simp only [cocycleFn, dif_neg hij]
  exact toGerm_holoFn _

omit [Nonempty X] in
/-- The extraction reads back the *restricted* germ on any sub-open of its overlap. -/
theorem toGerm_cocycleFn_restrict (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι}
    (hij : i ≠ j) {V : Opens X} (hV : V ≤ 𝔇.U i ⊓ 𝔇.U j) :
    toGerm V (fun v => cocycleFn 𝔇 hsep c i j v.1)
      = rawRestrictG hV ((c : 𝔇.toFiniteCover.toFiniteFamily.Cochain1) (i, j)) := by
  rw [← toGerm_cocycleFn 𝔇 hsep c hij, rawRestrictG_coe]
  rfl

omit [Nonempty X] in
/-- The extraction is real-smooth at every point of its overlap. -/
theorem contMDiffAt_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (cocycleFn 𝔇 hsep c i j) x := by
  by_cases h : i = j
  · simp only [cocycleFn, dif_pos h]
    exact contMDiffAt_const
  · simp only [cocycleFn, dif_neg h]
    exact holoFn_contMDiffAt _ hx

omit [Nonempty X] in
/-- The extraction is continuous at every point of its overlap. -/
theorem continuousAt_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) {i j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) :
    ContinuousAt (cocycleFn 𝔇 hsep c i j) x :=
  (contMDiffAt_cocycleFn 𝔇 hsep c hx).continuousAt

omit [Nonempty X] in
/-- **The extraction is smooth on overlaps** (R2 input predicate). -/
theorem smoothOnOverlaps_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    SmoothOnOverlaps 𝔇 (cocycleFn 𝔇 hsep c) :=
  fun _ _ _ hx => contMDiffAt_cocycleFn 𝔇 hsep c hx

omit [Nonempty X] in
/-- **The extraction is holomorphic on overlaps** (R3 input predicate): the analytic
representative's own-chart analyticity (`holoFn_chart_analyticAt`) relocated to the cover chart
(`analyticAt_chart_change_to`). -/
theorem holomorphicOnOverlaps_cocycleFn (hsep : SeparatesPoles 𝔇 K)
    (c : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K)) :
    HolomorphicOnOverlaps 𝔇 (cocycleFn 𝔇 hsep c) := by
  intro i j x hx
  by_cases h : i = j
  · simp only [cocycleFn, dif_pos h, Pi.zero_apply]
    exact differentiableAt_const _
  · simp only [cocycleFn, dif_neg h]
    have ha := holoFn_chart_analyticAt (cocycle_pair_mem_zero 𝔇 hsep c h) hx
    exact (analyticAt_chart_change_to (mem_chartSource_of_mem_U 𝔇 hx.1) ha).differentiableAt
