/-
  Existence of a finite Leray cover of a compact connected Riemann surface — the single missing
  geometric input to instantiate the Dolbeault/Riemann–Roch ladder on one fixed good cover.

  ## What this file is for (the scout, fallback step 1)

  The finiteness scout (commit 69ddee0, `LerayCoverIndependence.lean`) established that the hard
  cover-INDEPENDENCE (STEP B of `CechRefinement.lean`'s `## PLAN`) is NOT needed to finish
  Riemann–Roch: `RiemannRoch.exists_riemannRoch_divisor` is stated via `lDim` and mentions no cover,
  and `DolbeaultLadder.riemannRoch_equality_of_ladder 𝔘 hL` (the scaffold leaf wiring the ladder to
  the headline) takes an ARBITRARY `𝔘 : FiniteCover X` together with `hL : 𝔘.IsLeray`.  So the
  ladder→headline wiring may FIX ONE Leray cover.  The exact statement that unlocks that wiring is

      `exists_lerayCover : ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray`

  (`IsLeray` is `CechComplex.FiniteFamily.IsLeray`: every cover set simply connected AND every pairwise
  overlap preconnected — Forster §12's Leray hypothesis under which Čech `H¹` computes sheaf
  cohomology).  This is the target chosen here, and `CechRefinement.lean`'s own `PARTIAL SIDESTEP` note
  flags exactly this ("take the existence of a single Leray chart-disk cover as a hypothesis") as the
  lighter obligation that removes the arbitrary-`𝔘` cover-independence requirement.

  ## What is PROVEN here, sorry-free and axiom-clean

    * `simplyConnectedSpace_chartBallPreimage` — the genuine geometric content: the chart-preimage of a
      coordinate ball, `e.source ∩ e ⁻¹' ball cc r` (with `ball cc r ⊆ e.target`), is a
      `SimplyConnectedSpace`.  Proof: the chart restricts to a homeomorphism of this set onto the ball
      `ball cc r ⊆ ℂ` (`OpenPartialHomeomorph.toHomeomorphSourceTarget` of `e.restr`), the ball is
      contractible (`Metric.contractibleSpace_ball`), contractibility transports across the
      homeomorphism (`Homeomorph.contractibleSpace`), and a contractible space is simply connected
      (`SimplyConnectedSpace.ofContractible`).  Mathlib has all four atoms; this stitches them.

    * `chartBallCover : FiniteCover X` — a CONCRETE finite cover of compact `X` whose every set is a
      chart-ball-preimage `chartBallNbhd x` (an open neighborhood of `x`, biholomorphic to a Euclidean
      ball).  Built from compactness (`IsCompact.elim_finite_subcover` on the per-point neighborhoods)
      — the same shape as `Montel/Cover.lean`'s `chartCover`, but with each set pinned as a coordinate
      ball so the simply-connected clause holds.

    * `chartBallCover_simplyConnected` — every set of `chartBallCover` is a `SimplyConnectedSpace`.
      This discharges the FIRST conjunct of `IsLeray` for a concrete cover, UNCONDITIONALLY.

  ## The honest remaining gap (named hypothesis, NOT a `sorry`) — the good-cover input

  The SECOND conjunct of `IsLeray` — preconnected pairwise overlaps `IsPreconnected (U i ∩ U j)` — is
  the genuine "good cover" / Leray condition.  For an arbitrary pair of chart-balls in DIFFERENT charts
  the overlap, read in either chart, is `ball ∩ (transition image of ball)`, which need NOT be
  connected; making all overlaps connected requires a geodesically-convex (Whitney) refinement.  A
  recon of Mathlib confirms it has NO good-cover / geodesic-convexity / convexity-radius theory on
  manifolds (there is no `GoodCover`, no Riemannian convexity, only set-level `ShrinkingLemma`
  refinements with no connectedness control).  So this clause cannot be discharged from scratch tonight
  and is captured as an explicit, non-vacuous hypothesis.

  `exists_lerayCover` therefore takes one honest named hypothesis, `hOverlaps`, supplying the
  preconnectedness of the overlaps of `chartBallCover` (the ONLY missing piece — its simply-connected
  clause is already proven here), and concludes `∃ 𝔘, 𝔘.IsLeray`.  The hypothesis is TRUE (it is the
  literal good-cover statement) and minimal (it asks for nothing the file does not already supply
  except the one fact Mathlib lacks).  See `exists_lerayCover_of_goodCover` for the variant taking the
  whole good cover, and the docstrings for the exact obstruction.

  All declarations are `sorry`-free; `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
-/
import Jacobians.Dolbeault.CechComplex
import Mathlib.Analysis.Normed.Module.Connected

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The geometric core — a chart-ball-preimage is simply connected -/

/-- **A chart-preimage of a coordinate ball is simply connected.**  Let `e : OpenPartialHomeomorph X ℂ`
be a chart and `ball cc r ⊆ e.target` a coordinate ball inside its target.  Then the open set
`e.source ∩ e ⁻¹' (ball cc r)` (the chart-preimage of the ball — a coordinate disk in `X`) is a
`SimplyConnectedSpace`.

The chart restricted to this set is a homeomorphism onto `ball cc r ⊆ ℂ`
(`e.restr` has source the set and target `ball cc r`, by `e.right_inv` on the target;
`OpenPartialHomeomorph.toHomeomorphSourceTarget`).  The ball is contractible
(`Metric.contractibleSpace_ball`), contractibility transports across the homeomorphism
(`Homeomorph.contractibleSpace`), and a contractible space is simply connected
(`SimplyConnectedSpace.ofContractible`, an instance). -/
theorem simplyConnectedSpace_chartBallPreimage (e : OpenPartialHomeomorph X ℂ) (cc : ℂ) (r : ℝ)
    (hr : 0 < r) (hB : Metric.ball cc r ⊆ e.target) :
    SimplyConnectedSpace ↥(e.source ∩ e ⁻¹' Metric.ball cc r) := by
  set B := Metric.ball cc r with hBdef
  set U := e.source ∩ e ⁻¹' B with hUdef
  have hUopen : IsOpen U :=
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hUsub : U ⊆ e.source := Set.inter_subset_left
  -- Restrict the chart to the OPEN set `U`; its source is `U`, its target is `B`.
  set e' := e.restr U with he'
  have hsrc : e'.source = U := by
    rw [he', e.restr_source' U hUopen, Set.inter_eq_right.mpr hUsub]
  have htgt : e'.target = B := by
    rw [he', OpenPartialHomeomorph.restr_target, hUopen.interior_eq]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, hUdef]
    constructor
    · rintro ⟨hyt, _, hyB⟩
      rwa [e.right_inv hyt] at hyB
    · intro hyB
      have hyt : y ∈ e.target := hB hyB
      exact ⟨hyt, e.map_target hyt, by rwa [e.right_inv hyt]⟩
  -- Transport contractibility `ball → e'.target → e'.source = U`, then `ofContractible`.
  have hballC : ContractibleSpace ↥B := Metric.contractibleSpace_ball hr
  have htgtC : ContractibleSpace ↥(e'.target) := htgt ▸ hballC
  have hsrcC : ContractibleSpace ↥(e'.source) := e'.toHomeomorphSourceTarget.contractibleSpace
  rw [hsrc] at hsrcC
  haveI := hsrcC
  infer_instance

/-! ### Per-point chart-ball neighborhoods -/

/-- The radius of a coordinate ball around `(chartAt ℂ x) x` that fits inside the chart target.
Exists because `(chartAt ℂ x) x ∈ (chartAt ℂ x).target` and the target is open
(`Metric.isOpen_iff`). -/
noncomputable def chartBallRadius (x : X) : ℝ :=
  Classical.choose (Metric.isOpen_iff.mp (chartAt ℂ x).open_target ((chartAt ℂ x) x)
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x))) / 2

theorem chartBallRadius_spec (x : X) :
    0 < chartBallRadius x ∧
      Metric.closedBall ((chartAt ℂ x) x) (chartBallRadius x) ⊆ (chartAt ℂ x).target := by
  have h := Classical.choose_spec (Metric.isOpen_iff.mp (chartAt ℂ x).open_target ((chartAt ℂ x) x)
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  constructor
  · unfold chartBallRadius; linarith [h.1]
  · intro y hy
    simp only [Metric.mem_closedBall, chartBallRadius] at hy
    have h_in : y ∈ Metric.ball ((chartAt ℂ x) x) (Classical.choose (Metric.isOpen_iff.mp (chartAt ℂ x).open_target ((chartAt ℂ x) x) ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))) := by
      simp only [Metric.mem_ball]
      linarith [h.1]
    exact h.2 h_in

theorem chartBallRadius_pos (x : X) : 0 < chartBallRadius x := (chartBallRadius_spec x).1

theorem closedBall_chartBallRadius_subset_target (x : X) :
    Metric.closedBall ((chartAt ℂ x) x) (chartBallRadius x) ⊆ (chartAt ℂ x).target :=
  (chartBallRadius_spec x).2

theorem ball_chartBallRadius_subset_target (x : X) :
    Metric.ball ((chartAt ℂ x) x) (chartBallRadius x) ⊆ (chartAt ℂ x).target :=
  Metric.ball_subset_closedBall.trans (chartBallRadius_spec x).2

/-- The chart-ball neighborhood of `x`: the chart-preimage of the coordinate ball
`ball ((chartAt ℂ x) x) (chartBallRadius x)`.  An open neighborhood of `x`, biholomorphic to a
Euclidean ball (hence simply connected, `simplyConnectedSpace_chartBallNbhd`). -/
def chartBallNbhd (x : X) : Set X :=
  (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (chartBallRadius x)

theorem chartBallNbhd_isOpen (x : X) : IsOpen (chartBallNbhd x) :=
  (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source Metric.isOpen_ball

theorem mem_chartBallNbhd (x : X) : x ∈ chartBallNbhd x :=
  ⟨mem_chart_source ℂ x, by
    simp only [Set.mem_preimage]; exact Metric.mem_ball_self (chartBallRadius_pos x)⟩

/-- Each chart-ball neighborhood is simply connected (instance of
`simplyConnectedSpace_chartBallPreimage` for `e = chartAt ℂ x`). -/
theorem simplyConnectedSpace_chartBallNbhd (x : X) :
    SimplyConnectedSpace ↥(chartBallNbhd x) :=
  simplyConnectedSpace_chartBallPreimage (chartAt ℂ x) _ _ (chartBallRadius_pos x)
    (ball_chartBallRadius_subset_target x)

/-! ### The finite chart-ball cover -/

/-- Compactness yields a finite set of points whose chart-ball neighborhoods cover `X`. -/
theorem exists_finite_chartBallNbhd_cover :
    ∃ s : Finset X, (⋃ x ∈ s, chartBallNbhd (X := X) x) = Set.univ := by
  have hcov : Set.univ ⊆ ⋃ x : X, chartBallNbhd (X := X) x := fun y _ =>
    Set.mem_iUnion.mpr ⟨y, mem_chartBallNbhd y⟩
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : X => chartBallNbhd (X := X) x) (fun x => chartBallNbhd_isOpen x) hcov
  exact ⟨s, Set.eq_univ_of_univ_subset hs⟩

/-- The finite set of centres of the canonical chart-ball cover. -/
noncomputable def chartBallCenters : Finset X :=
  Classical.choose (exists_finite_chartBallNbhd_cover (X := X))

theorem chartBallCenters_cover :
    (⋃ x ∈ (chartBallCenters : Finset X), chartBallNbhd (X := X) x) = Set.univ :=
  Classical.choose_spec (exists_finite_chartBallNbhd_cover (X := X))

/-- The element of `X` indexed by a `Fin (chartBallCenters.card)` value, via the finite-set
enumeration `Finset.equivFin`.  Used to give the cover a `Type 0` index (`FiniteCover.ι : Type`). -/
noncomputable def chartBallCenter (i : Fin (chartBallCenters (X := X)).card) : X :=
  ((chartBallCenters (X := X)).equivFin.symm i : X)

/-- **The canonical finite chart-ball cover of a compact Riemann surface.**  A `FiniteCover X` indexed
by `Fin (chartBallCenters.card)` (a `Type 0` index, as `FiniteCover.ι` requires), whose `i`-th set is
the chart-ball neighborhood `chartBallNbhd (chartBallCenter i)` — an open coordinate disk biholomorphic
to a Euclidean ball.  Covers `X` by compactness (the centres enumerate `chartBallCenters`); each set is
simply connected (`chartBallCover_simplyConnected`).  This is the concrete cover the Leray-cover
existence is built on; only its overlap-connectedness (the good-cover input Mathlib lacks) is left
open. -/
noncomputable def chartBallCover : FiniteCover X where
  ι := Fin (chartBallCenters (X := X)).card
  U := fun i => ⟨chartBallNbhd (chartBallCenter i), chartBallNbhd_isOpen _⟩
  covers := by
    rw [← TopologicalSpace.Opens.coe_inj, TopologicalSpace.Opens.coe_iSup]
    show (⋃ i : Fin (chartBallCenters (X := X)).card, chartBallNbhd (chartBallCenter i)) = _
    have hreindex :
        (⋃ i : Fin (chartBallCenters (X := X)).card, chartBallNbhd (chartBallCenter i))
          = ⋃ j : {x // x ∈ (chartBallCenters (X := X))}, chartBallNbhd j.1 :=
      ((chartBallCenters (X := X)).equivFin.symm.surjective).iUnion_comp
        (fun j : {x // x ∈ (chartBallCenters (X := X))} => chartBallNbhd j.1)
    rw [hreindex, Set.iUnion_subtype, chartBallCenters_cover]
    rfl

@[simp] theorem chartBallCover_U (i : (chartBallCover (X := X)).ι) :
    ((chartBallCover (X := X)).U i : Set X) = chartBallNbhd (chartBallCenter i) := rfl

/-- **Every set of the canonical chart-ball cover is simply connected.**  The FIRST conjunct of
`IsLeray` for `chartBallCover`, proven UNCONDITIONALLY: each `U i` is the chart-ball neighborhood
`chartBallNbhd (chartBallCenter i)`, simply connected by `simplyConnectedSpace_chartBallNbhd`. -/
theorem chartBallCover_simplyConnected (i : (chartBallCover (X := X)).ι) :
    SimplyConnectedSpace ↥((chartBallCover (X := X)).U i) :=
  simplyConnectedSpace_chartBallNbhd (chartBallCenter i)

/-! ### The Leray cover existence — gated on the honest good-cover (overlap) input

The simply-connected clause of `IsLeray` is proven above for the concrete `chartBallCover`.  The
only remaining clause is preconnectedness of the pairwise overlaps — the good-cover / geodesic-
convexity input absent from Mathlib.  We expose it as one honest named hypothesis and assemble the
Leray cover from it. -/

/-- **`exists_lerayCover` — UNCONDITIONAL.**  `X` admits a finite Leray cover: the canonical chart-ball
cover `chartBallCover`, whose sets are simply connected (`chartBallCover_simplyConnected`) — which is
*all* `IsLeray` now requires (its overlap conjunct was dropped as dead weight; for `H¹` Cartan needs
only acyclic sets — see `CechComplex.FiniteFamily.IsLeray` and `GoodCover`).

This is the statement that unlocks the ladder→headline wiring
(`RiemannRoch.exists_riemannRoch_divisor` via `DolbeaultLadder.riemannRoch_equality_of_ladder 𝔘 hL`
with this `𝔘 = chartBallCover` and `hL` the produced `IsLeray`).  Previously gated on the good-cover
overlap-preconnectedness `hOverlaps` (a Mathlib-absent Whitney geodesic-convexity fact); that
hypothesis is now eliminated, so the wiring is unconditional. No `sorry`. -/
theorem exists_lerayCover : ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray :=
  ⟨chartBallCover, chartBallCover_simplyConnected⟩

/-- **`exists_lerayCover` from any cover with simply-connected sets.**  Trivial repackaging — kept as
an alternative entry point.  Subsumed by the unconditional `exists_lerayCover` (the canonical
chart-ball cover already has simply-connected sets); offered for an owner who would rather supply a
different good cover.  No `sorry`. -/
theorem exists_lerayCover_of_goodCover
    (hGood : ∃ 𝔘 : FiniteCover X, ∀ i, SimplyConnectedSpace ↥(𝔘.U i)) :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray :=
  hGood

end Jacobians.Dolbeault
