/-
# Hyperelliptic `PeriodCycleBasis` witness assembly (milestones M2/M3)

Assembles the branch-cut loop constructions of `CycleLoops.lean` into a
conditional witness for `AX_PeriodCycleBasis` on the odd hyperelliptic
curve, with every remaining gap an **explicit named hypothesis** (never a
`sorry`, never a new axiom).

## The bundle

`BranchCutSystem H h` packages `2g` closed square-root-lifted cycles
(classically: circles around branch-point pairs — a-cycles at indices
`0 … g−1` through `αEmbed`, b-cycles at `g … 2g−1` through `βEmbed`,
respecting the `arcPeriodVec` LAYOUT CONTRACT of
`Jacobians/Axioms/PeriodCycleBasis.lean`) together with connector arcs
rebasing them at a common affine basepoint. `BranchCutSystem.loop`
produces the `Fin (2g)`-indexed family of based `AnalyticLoop`s.

## The named-hypothesis boundary (what the SVK/covering package supplies)

* `isBasis` + `tie` — the classes of the `2g` loops form a ℤ-basis of
  `H₁`: covering-space theory for the double cover of `ℙ¹` minus the
  branch locus (π₁ of a punctured sphere is free → SVK package), plus the
  analytic-genus comparison `2 · genus = rank H₁`.
* `hR1`/`hR2` — Riemann bilinear relations for the cycle periods. By
  `loop_period_eq` these are statements about **explicit interval
  integrals in the x-plane** (`∫₀¹ coeff·x′`), the classical branch-cut
  period relations; dischargeable per-form via the boundary-word engine
  (Kirov port) or direct computation once the form layer (#167 `OddForm`)
  exposes coefficients.

`nonempty_periodCycleBasis_of_branchCutSystem` then inhabits
`PeriodCycleBasis (HyperellipticOdd H h) (base)` — the hyperelliptic
analogue of the elliptic witness (`Elliptic/Witnesses.lean`), with the
H₁ half as hypotheses instead of the axiom-wrap used there.

See `docs/planning/HYP_CB_BLOCKER.md` for the per-gap discharge analysis.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.CycleLoops
import Jacobians.Axioms.PeriodCycleBasis

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface
open Jacobians.Axioms
open Jacobians.Layer3 (Q)

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- A system of `2g` closed branch-cut cycles on the odd hyperelliptic curve,
rebased at a common affine basepoint by connector arcs.

Index layout: the `Fin (2 * genus …)` index respects the
`αEmbed`/`βEmbed` split of `arcPeriodVec` — indices `0 … g−1` are the
a-cycles, `g … 2g−1` the b-cycles. -/
structure BranchCutSystem (H : HyperellipticData) (h : Odd H.f.natDegree) where
  /-- The common basepoint on the affine curve (necessarily `y ≠ 0` for the
  connectors' branch data to exist; not separately recorded). -/
  base : HyperellipticAffine H
  /-- The closed cycle data: classically, circles around branch-point pairs. -/
  cycle : Fin (2 * genus (HyperellipticOdd H h)) → SqrtArcData H
  /-- Each cycle's base arc is closed. -/
  cycle_closed_x : ∀ i, (cycle i).x 1 = (cycle i).x 0
  /-- Each cycle's branch is closed after a full turn (trivial square-root
  monodromy around an even number of branch points — the monodromy input). -/
  cycle_closed_y : ∀ i, (cycle i).y 1 = (cycle i).y 0
  /-- Connector arcs from the basepoint to each cycle's starting point. -/
  connector : Fin (2 * genus (HyperellipticOdd H h)) → SqrtArcData H
  /-- Connectors start at the common basepoint. -/
  connector_start : ∀ i, (connector i).toAffine 0 = base
  /-- Connectors end at their cycle's starting point. -/
  connector_end : ∀ i, (connector i).toAffine 1 = (cycle i).toAffine 0

namespace BranchCutSystem

variable (S : BranchCutSystem H h)

/-- The common basepoint, on the compact curve. -/
def basePoint : HyperellipticOdd H h := HyperellipticOdd.coe S.base

/-- The conjugated arc `σᵢ ⬝ γᵢ ⬝ σᵢ⁻¹` of the `i`-th cycle. -/
noncomputable def loopArc (i : Fin (2 * genus (HyperellipticOdd H h))) :
    AnalyticArc (HyperellipticOdd H h) :=
  AnalyticArc.conjugate ((S.connector i).toOddArc h) ((S.cycle i).toOddArc h)
    (by
      change ((S.connector i).toOdd h) 1 = ((S.cycle i).toOdd h) 0
      unfold SqrtArcData.toOdd
      rw [S.connector_end i])
    (by
      change ((S.cycle i).toOdd h) 1 = ((S.cycle i).toOdd h) 0
      unfold SqrtArcData.toOdd
      rw [Subtype.ext (Prod.ext (S.cycle_closed_x i) (S.cycle_closed_y i) :
        ((S.cycle i).toAffine 1).val = ((S.cycle i).toAffine 0).val)])

/-- The `i`-th based loop of the system: the `i`-th cycle rebased at the
common basepoint along its connector. -/
noncomputable def loop (i : Fin (2 * genus (HyperellipticOdd H h))) :
    AnalyticLoop (HyperellipticOdd H h) S.basePoint where
  arc := S.loopArc i
  start_eq := by
    have h0 : (S.loopArc i).extend 0 = ((S.connector i).toOdd h) 0 := by
      simp [loopArc, AnalyticArc.conjugate, AnalyticArc.trans_extend_zero]
    rw [h0]
    change HyperellipticOdd.coe ((S.connector i).toAffine 0) = S.basePoint
    rw [S.connector_start i]
    rfl
  end_eq := by
    have h1 : (S.loopArc i).extend 1 = ((S.connector i).toOdd h) 0 := by
      simp [loopArc, AnalyticArc.conjugate, AnalyticArc.trans_extend_one,
        AnalyticArc.reverse_extend_one]
    rw [h1]
    change HyperellipticOdd.coe ((S.connector i).toAffine 0) = S.basePoint
    rw [S.connector_start i]
    rfl

/-- **M3 period reduction.** The canonical period of the `i`-th based loop
equals the explicit x-plane integral over the bare cycle: connectors cancel
(`canonicalArcIntegral_conjugate`) and the sqrt-lift integrand collapses to
`coeff · x′` (`canonicalArcIntegral_toOddArc`). For the hyperelliptic forms
`x^k dx / y` this is the classical branch-cut period integral. -/
theorem loop_period_eq (i : Fin (2 * genus (HyperellipticOdd H h)))
    (form : HolomorphicOneForm (HyperellipticOdd H h)) :
    canonicalArcIntegral (S.loop i).arc form =
      ∫ r in (0 : ℝ)..1,
        form.coeff (((S.cycle i).toOdd h) r) ((S.cycle i).x r) *
          deriv (S.cycle i).x r := by
  change canonicalArcIntegral (S.loopArc i) form = _
  unfold loopArc
  rw [canonicalArcIntegral_conjugate]
  exact (S.cycle i).canonicalArcIntegral_toOddArc h form

/-- The arc-level period vector of the system in computable form: every
entry of `arcPeriodVec` over the system's loops is an explicit x-plane
interval integral (a-periods through `αEmbed`, b-periods through `βEmbed`,
per the layout contract). -/
theorem arcPeriodVec_loop_fst (form : HolomorphicOneForm (HyperellipticOdd H h))
    (i : Fin (genus (HyperellipticOdd H h))) :
    (arcPeriodVec S.loop form).1 i =
      ∫ r in (0 : ℝ)..1,
        form.coeff (((S.cycle (αEmbed i)).toOdd h) r) ((S.cycle (αEmbed i)).x r) *
          deriv (S.cycle (αEmbed i)).x r := by
  rw [arcPeriodVec_fst]
  exact S.loop_period_eq (αEmbed i) form

theorem arcPeriodVec_loop_snd (form : HolomorphicOneForm (HyperellipticOdd H h))
    (i : Fin (genus (HyperellipticOdd H h))) :
    (arcPeriodVec S.loop form).2 i =
      ∫ r in (0 : ℝ)..1,
        form.coeff (((S.cycle (βEmbed i)).toOdd h) r) ((S.cycle (βEmbed i)).x r) *
          deriv (S.cycle (βEmbed i)).x r := by
  rw [arcPeriodVec_snd]
  exact S.loop_period_eq (βEmbed i) form

end BranchCutSystem

/-- **Conditional hyperelliptic witness for `AX_PeriodCycleBasis`.** Given a
branch-cut system and the named H₁/bilinear hypotheses (see the module
docstring for their discharge routes), the odd hyperelliptic curve admits a
`PeriodCycleBasis` at the system's basepoint.

This is the hyperelliptic analogue of `ellipticCycleBasis`, with the
covering-theoretic content as hypotheses instead of the axiom-wrap used at
genus 1. No sorries; the hypotheses are the M2 gap awaiting the SVK /
covering package. -/
theorem nonempty_periodCycleBasis_of_branchCutSystem
    (S : BranchCutSystem H h)
    (isBasis : Module.Basis (Fin (2 * genus (HyperellipticOdd H h))) ℤ
      (H1 (HyperellipticOdd H h) S.basePoint))
    (tie : ∀ i, isBasis i = loopToHomology (S.loop i))
    (hR1 : ∀ η ζ : HolomorphicOneForm (HyperellipticOdd H h),
      Q (arcPeriodVec S.loop η) (arcPeriodVec S.loop ζ) = 0)
    (hR2 : ∀ η : HolomorphicOneForm (HyperellipticOdd H h), η ≠ 0 →
      0 < (Complex.I * Q (arcPeriodVec S.loop η)
        (conjArcPeriodVec S.loop η)).re) :
    Nonempty (PeriodCycleBasis (HyperellipticOdd H h) S.basePoint) :=
  ⟨⟨S.loop, isBasis, tie, hR1, hR2⟩⟩

end Jacobians.ProjectiveCurve
