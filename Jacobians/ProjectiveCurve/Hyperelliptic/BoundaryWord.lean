/-
# P10 — the hyperelliptic boundary-word witness (issue #172, G-D half)

Route note: `docs/planning/P10_BW_HYPERELLIPTIC_ROUTE.md`. Instantiates
the polynomial boundary-word engine
(`Jacobians/RiemannSurface/BoundaryWordPolynomial.lean`) for the odd
hyperelliptic family over a `BranchCutSystem`, extending the merged
g = 1 witness (`BoundaryWordElliptic.lean`, #225) to every genus.

Contents:

* `aPeriodIntegral` / `bPeriodIntegral` + the entry lemmas
  `arcAPeriodMatrix_branchCut` / `arcBPeriodMatrix_branchCut` — the g×g
  block bookkeeping: every entry of the arc-period blocks over the
  branch-cut loops is an explicit x-plane interval integral
  (`∫₀¹ coeff·x′`, via the proven M3 reduction `loop_period_eq`);
* `R1Word` / `R2GramWord` — the two named WALLS, the classical
  branch-cut period relations in finitary matrix form (`R1Word` also in
  entrywise integral form via `r1Word_iff_integrals`: zero manifold and
  zero contour content);
* `hyperellipticArcBoundaryWordData` — THE per-genus datum
  `ArcBoundaryWordDataInterior S.loop cω`: 7 of 9 fields proven by the
  engine, the walls carried as hypotheses (never sorries, no axioms);
* `hyperelliptic_periodGram_posDef` — R2 positive-definiteness DERIVED
  (not assumed) from the Gram word, via the port's interior Green
  positivity;
* `nonempty_periodCycleBasis_of_branchCutSystem_boundaryWord` — the
  upgraded conditional witness: the ∀-forms `hR1`/`hR2` slots of
  `nonempty_periodCycleBasis_of_branchCutSystem` replaced by the
  finitary walls + a form basis; the H₁ slots (`isBasis`, `tie`) stay
  named hypotheses exactly as in #225's `ellipticPeriodCycleBasisOfH1`
  (the G-C gap, `docs/planning/HYP_CB_BLOCKER.md`).
-/
import Jacobians.RiemannSurface.BoundaryWordPolynomial
import Jacobians.ProjectiveCurve.Hyperelliptic.CycleBasisWitness

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff ComplexOrder
open Jacobians.RiemannSurface
open Jacobians.RiemannSurface.BoundaryWordPolynomial
open Jacobians.Axioms
open Polynomial Matrix

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

namespace BranchCutSystem

variable (S : BranchCutSystem H h)

/-! ### The explicit x-plane period integrals and the g×g entry lemmas -/

/-- The explicit x-plane A-period integral: the `i`-th a-cycle of the
system against the `j`-th basis form. Pure interval integral — no
manifold content survives the M3 reduction. -/
noncomputable def aPeriodIntegral
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (i j : Fin (genus (HyperellipticOdd H h))) : ℂ :=
  ∫ r in (0 : ℝ)..1,
    (cω j).coeff (((S.cycle (αEmbed i)).toOdd h) r) ((S.cycle (αEmbed i)).x r) *
      deriv (S.cycle (αEmbed i)).x r

/-- The explicit x-plane B-period integral (b-cycle slots, through
`βEmbed`). -/
noncomputable def bPeriodIntegral
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (i j : Fin (genus (HyperellipticOdd H h))) : ℂ :=
  ∫ r in (0 : ℝ)..1,
    (cω j).coeff (((S.cycle (βEmbed i)).toOdd h) r) ((S.cycle (βEmbed i)).x r) *
      deriv (S.cycle (βEmbed i)).x r

/-- **A-block entry lemma** (g×g generalization of the 1×1
`arcAPeriodMatrix_elliptic`): every entry of the arc-A-period block over
the branch-cut loops is the explicit x-plane integral. -/
theorem arcAPeriodMatrix_branchCut
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (i j : Fin (genus (HyperellipticOdd H h))) :
    arcAPeriodMatrix S.loop (fun m => cω m) i j = S.aPeriodIntegral cω i j := by
  rw [arcAPeriodMatrix_apply]
  exact S.loop_period_eq (αEmbed i) (cω j)

/-- **B-block entry lemma**: same, through `βEmbed`. -/
theorem arcBPeriodMatrix_branchCut
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (i j : Fin (genus (HyperellipticOdd H h))) :
    arcBPeriodMatrix S.loop (fun m => cω m) i j = S.bPeriodIntegral cω i j := by
  rw [arcBPeriodMatrix_apply]
  exact S.loop_period_eq (βEmbed i) (cω j)

/-! ### The two named walls (the analytic content left open) -/

/-- **WALL HBW-R1 (NOT YET DISCHARGED — named hypothesis, not an
axiom).** Riemann's first bilinear relation for the branch-cut period
blocks, in finitary matrix form: `AᵀB = BᵀA` over the system's loops and
a chosen form basis. By `r1Word_iff_integrals` this is a family of
identities between explicit x-plane interval integrals. Discharge
routes: the geometric slit-chart boundary word (Route K) or the
classical per-branch-pair computation (route note, Decision 3). -/
def R1Word
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h))) : Prop :=
  (arcAPeriodMatrix S.loop fun m => cω m)ᵀ * (arcBPeriodMatrix S.loop fun m => cω m)
    = (arcBPeriodMatrix S.loop fun m => cω m)ᵀ
      * (arcAPeriodMatrix S.loop fun m => cω m)

/-- **WALL HBW-R2 (NOT YET DISCHARGED — named hypothesis, not an
axiom).** The R2 Gram word for a curve-tuned polynomial family `P`: the
conjugated period combination equals the box boundary form of the
polynomial cut data (the general-g form of the g = 1 orientation-constant
identity `elliptic_word_R2_lhs` + `boundaryForm_const_linear`).
Satisfiable exactly when the period Gram is positive-definite Hermitian
(Cholesky tuning of `P` — route note, Decision 1). -/
def R2GramWord
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (P : Fin (genus (HyperellipticOdd H h)) → Polynomial ℂ) : Prop :=
  ∀ i j,
    ((arcAPeriodMatrix S.loop fun m => cω m)ᵀ
          * (arcBPeriodMatrix S.loop fun m => cω m).map (starRingEnd ℂ)
        - (arcBPeriodMatrix S.loop fun m => cω m)ᵀ
          * (arcAPeriodMatrix S.loop fun m => cω m).map (starRingEnd ℂ)) i j
      = - Jacobians.boundaryForm (fun z => ((P j).derivative).eval z)
          (fun z => (P i).eval z)

/-- **The R1 wall has zero manifold content**: `R1Word` is equivalent to
the entrywise family of identities between the explicit x-plane interval
integrals — the classical statement that branch-cut a/b-periods
commute. -/
theorem r1Word_iff_integrals
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h))) :
    S.R1Word cω ↔ ∀ i j,
      (∑ k, S.aPeriodIntegral cω k i * S.bPeriodIntegral cω k j)
        = ∑ k, S.bPeriodIntegral cω k i * S.aPeriodIntegral cω k j := by
  rw [R1Word, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, S.arcAPeriodMatrix_branchCut cω,
    S.arcBPeriodMatrix_branchCut cω]

/-- **The R2 wall has zero manifold content on its period side**:
`R2GramWord` is equivalent to the entrywise family of identities between
the explicit x-plane interval integrals and the polynomial box boundary
forms. -/
theorem r2GramWord_iff_integrals
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (P : Fin (genus (HyperellipticOdd H h)) → Polynomial ℂ) :
    S.R2GramWord cω P ↔ ∀ i j,
      (∑ k, S.aPeriodIntegral cω k i * (starRingEnd ℂ) (S.bPeriodIntegral cω k j))
          - ∑ k, S.bPeriodIntegral cω k i * (starRingEnd ℂ) (S.aPeriodIntegral cω k j)
        = - Jacobians.boundaryForm (fun z => ((P j).derivative).eval z)
            (fun z => (P i).eval z) := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply,
    S.arcAPeriodMatrix_branchCut cω, S.arcBPeriodMatrix_branchCut cω]

/-! ### The datum and its consumers -/

/-- **The hyperelliptic boundary-word witness datum** (the per-genus
extension of `ellipticArcBoundaryWordData`): for any branch-cut system,
form basis, and curve-tuned polynomial family with linearly independent
derivatives, the two walls assemble to the full interior comparison
datum. Seven of the nine fields are proven by the polynomial engine,
uniformly in the genus; no sorries, no axioms. -/
noncomputable def hyperellipticArcBoundaryWordData
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (P : Fin (genus (HyperellipticOdd H h)) → Polynomial ℂ)
    (hind : LinearIndependent ℂ fun j => (P j).derivative)
    (hR1 : S.R1Word cω) (hR2 : S.R2GramWord cω P) :
    ArcBoundaryWordDataInterior S.loop cω :=
  polyArcBoundaryWordData S.loop cω P hind hR1 hR2

/-- **R2 positive-definiteness, DERIVED**: the branch-cut period Gram is
positive definite, from the Gram word via the port's interior Green
positivity (not assumed anywhere). -/
theorem periodGram_posDef_of_words
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (P : Fin (genus (HyperellipticOdd H h)) → Polynomial ℂ)
    (hind : LinearIndependent ℂ fun j => (P j).derivative)
    (hR1 : S.R1Word cω) (hR2 : S.R2GramWord cω P) :
    (arcPeriodGram S.loop fun m => cω m).PosDef :=
  (S.hyperellipticArcBoundaryWordData cω P hind hR1 hR2).periodGram_posDef

end BranchCutSystem

/-- **Upgraded conditional hyperelliptic witness.** Replaces the
∀-quantified `hR1`/`hR2` slots of
`nonempty_periodCycleBasis_of_branchCutSystem` by the finitary matrix
walls of the boundary-word route (+ a form basis and polynomial tuning
data); the basis expansion to all forms is done by the boundary-word
interior pipeline. The H₁ slots remain the G-C named hypotheses, exactly
as in the g = 1 corollary `ellipticPeriodCycleBasisOfH1`. -/
theorem nonempty_periodCycleBasis_of_branchCutSystem_boundaryWord
    (S : BranchCutSystem H h)
    (isBasis : Module.Basis (Fin (2 * genus (HyperellipticOdd H h))) ℤ
      (H1 (HyperellipticOdd H h) S.basePoint))
    (tie : ∀ i, isBasis i = loopToHomology (S.loop i))
    (cω : Module.Basis (Fin (genus (HyperellipticOdd H h))) ℂ
      (HolomorphicOneForm (HyperellipticOdd H h)))
    (P : Fin (genus (HyperellipticOdd H h)) → Polynomial ℂ)
    (hind : LinearIndependent ℂ fun j => (P j).derivative)
    (hR1 : S.R1Word cω) (hR2 : S.R2GramWord cω P) :
    Nonempty (PeriodCycleBasis (HyperellipticOdd H h) S.basePoint) :=
  ⟨periodCycleBasisOfBoundaryWordInterior isBasis tie
    (S.hyperellipticArcBoundaryWordData cω P hind hR1 hR2)⟩

end Jacobians.ProjectiveCurve
