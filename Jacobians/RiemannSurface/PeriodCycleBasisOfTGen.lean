/-
# `AX_PeriodCycleBasis` pinned to T-GEN — the conditional constructor

This file expresses the content of `AX_PeriodCycleBasis`
(`Jacobians.Axioms.PeriodCycleBasis`, the challenge's last
challenge-critical axiom) **in terms of T-GEN**
(`AnalyticLoopsGenerateH1`), which the topology lane has already reduced
to the classical approximation theorems `{Whitney, Grauert}`.

The constructor `periodCycleBasis_of_tgen` assembles a full
`PeriodCycleBasis X x₀` from:

1. **T-GEN** — `AnalyticLoopsGenerateH1 x₀`: the classes of
   piecewise-analytic loops ℤ-span `H1 X x₀`;
2. **K-LITE / TR-DISC** — `[DiscreteTopology (loopPeriodLattice x₀ b)]`,
   supplied as an instance hypothesis (the named output of the
   discreteness lane, `PeriodDiscreteness.lean`);
3. **the rank residuals** — `[Module.Finite ℤ (H1 X x₀)]`,
   `[Module.Free ℤ (H1 X x₀)]`, and `finrank ℤ (H1 X x₀) ≤ 2g`
   (T-FG + torsion-freeness + T-RANK≤), which combine with (1)+(2) to
   give period-injectivity via `h1PeriodInjective_of_finrank_le`;
4. **R1/R2 matrix conditions** for the **extracted** loop family — the
   block symmetry `AᵀB = BᵀA` and the Gram positive-definiteness
   `(I•(AᵀB̄ − BᵀĀ)).PosDef` of the chosen ℂ-basis of holomorphic
   1-forms, supplied as predicates over the produced loops.

The three H₁ fields (`loops` / `isBasis` / `loops_to_basis`) come from
`H1Composite.exists_h1LoopBasis_of_periodInjective`; the two Hodge
fields (`R1` / `R2`) come from the `BilinearRelations.lean` linear/Gram
collapse fed by the matrix hypotheses.

**No axiom is introduced and `AX_PeriodCycleBasis` appears in NO closure
of this file** (the circularity guard: we build a `PeriodCycleBasis`
*term*, we never invoke `AX_PeriodCycleBasis`).

## The residual set

After this wiring, `Nonempty (PeriodCycleBasis X x₀)` reduces to:

| Residual | Status |
|----------|--------|
| `AnalyticLoopsGenerateH1 x₀` (T-GEN) | reduced to `{Whitney, Grauert}` (topology lane) |
| `[DiscreteTopology (loopPeriodLattice x₀ b)]` (TR-DISC) | named residual (discreteness lane) |
| `[Module.Finite ℤ (H1 X x₀)]` (T-FG) | named residual; necessary for `isBasis` |
| `[Module.Free ℤ (H1 X x₀)]` (torsion-freeness) | named residual; necessary for `isBasis` |
| `finrank ℤ (H1 X x₀) ≤ 2g` (T-RANK≤) | named residual |
| R1 block symmetry `AᵀB = BᵀA` | **unproven in general** (proven g ≤ 1, ell/hyperell) |
| R2 Gram `PosDef` | **unproven in general** (proven for ell/hyperell witnesses) |

The first five collapse, given T-GEN + TR-DISC, to the single
period-injectivity statement KER-0 (`h1Free_finite_rank_of_periodInjective`
+ `h1PeriodInjective_of_finrank_le`). The last two are the genuine
analytic content of the Riemann bilinear relations and are NOT supplied
by any general lemma — they remain explicit named hypotheses.

A `_of_periodInjective` variant folds residuals 2–5 into the single KER-0
hypothesis. A `genus ≤ 1` corollary discharges R1 (and, at `g = 0`, R2)
entirely, leaving only `{T-GEN, KER-0, R2-matrix}` (resp. `{T-GEN, KER-0}`
at `g = 0`).
-/
import Jacobians.RiemannSurface.BilinearRelations
import Jacobians.RiemannSurface.H1Composite

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff ComplexOrder
open Jacobians.Axioms (PeriodCycleBasis loopToHomology arcPeriodVec conjArcPeriodVec)
open Jacobians.Layer3 (Q)
open Matrix

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {x₀ : X}

/-! ## The R1/R2 matrix conditions as predicates over a loop family

The Hodge fields of `PeriodCycleBasis` are stated over the *bundled*
loops' own arc periods, so the matrix conditions discharging them must be
phrased for the **extracted** loop family — not a pre-chosen one. The
two `Prop`-valued predicates below capture exactly the inputs of the
`BilinearRelations.lean` collapse. -/

/-- **R1 matrix condition** for a loop family over a ℂ-basis of forms:
the arc-period blocks satisfy `AᵀB = BᵀA`. Discharges the `R1` field via
`arc_R1_of_periodMatrix_symm`. Proven for `genus ≤ 1`
(`arcPeriodMatrix_symm_of_genus_le_one`); otherwise the analytic content
of Riemann's first relation (boundary-word engine for specific witnesses). -/
def ArcR1Matrix (loops : Fin (2 * genus X) → Jacobians.RiemannSurface.AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) : Prop :=
  (arcAPeriodMatrix loops fun j => cω j)ᵀ * (arcBPeriodMatrix loops fun j => cω j)
    = (arcBPeriodMatrix loops fun j => cω j)ᵀ * (arcAPeriodMatrix loops fun j => cω j)

/-- **R2 matrix condition** for a loop family over a ℂ-basis of forms:
the arc-period Gram form `I•(AᵀB̄ − BᵀĀ)` is positive definite.
Discharges the `R2` field via `arc_R2_of_periodGram_posDef`. The analytic
content of Riemann's second relation (Hodge positivity; boundary-word
engine for specific witnesses). -/
def ArcR2Matrix (loops : Fin (2 * genus X) → Jacobians.RiemannSurface.AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) : Prop :=
  (arcPeriodGram loops fun j => cω j).PosDef

/-! ## The conditional constructor -/

variable (x₀)

/-- **`AX_PeriodCycleBasis` from T-GEN + KER-0 + R1/R2 (matrix form).**
The conditional constructor pinning the challenge's last
challenge-critical axiom to T-GEN.

Given
* T-GEN (`hgen : AnalyticLoopsGenerateH1 x₀`),
* KER-0 (`hker`: developing-value period-injectivity on `H1 X x₀`), and
* the R1/R2 matrix conditions for the chosen ℂ-basis `cω` holding on the
  loop family **extracted** by the H₁ composite (`hR1` / `hR2`, supplied
  as predicates over that family),

produces a full `PeriodCycleBasis X x₀`. The H₁ fields come from
`exists_h1LoopBasis_of_periodInjective`; R1/R2 from the
`BilinearRelations.lean` linear/Gram collapse.

No axiom is consumed; `AX_PeriodCycleBasis` is not invoked. -/
theorem periodCycleBasis_of_tgen_of_periodInjective
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [DiscreteTopology (loopPeriodLattice x₀ b)]
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hker : ∀ v : H1 X x₀,
      Jacobians.Layer3.devValPeriodVec x₀ b v = 0 → v = 0)
    (hR1 : ∀ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
        (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
        (∀ i, isB i = loopToHomology (loops i)) → ArcR1Matrix loops cω)
    (hR2 : ∀ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
        (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
        (∀ i, isB i = loopToHomology (loops i)) → ArcR2Matrix loops cω) :
    Nonempty (PeriodCycleBasis X x₀) := by
  obtain ⟨loops, isB, htie⟩ :=
    exists_h1LoopBasis_of_periodInjective x₀ b hgen hker
  refine ⟨⟨loops, isB, htie, ?_, ?_⟩⟩
  · intro η ζ
    exact arc_R1_of_periodMatrix_symm loops cω (hR1 loops isB htie) η ζ
  · intro η hη
    exact arc_R2_of_periodGram_posDef loops cω (hR2 loops isB htie) η hη

/-- **`AX_PeriodCycleBasis` from T-GEN + the topology-lane residuals +
R1/R2 (matrix form).** The flip's full composition shape on every field:

  T-GEN + K-LITE (TR-DISC) + T-FG + `Module.Free ℤ H1` + T-RANK(≤)
    ⟹ KER-0 ⟹ H₁ fields;  R1/R2-matrix ⟹ Hodge fields.

KER-0 is derived from the rank residuals by
`h1PeriodInjective_of_finrank_le`; everything else is as in
`periodCycleBasis_of_tgen_of_periodInjective`. -/
theorem periodCycleBasis_of_tgen
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [DiscreteTopology (loopPeriodLattice x₀ b)]
    [Module.Finite ℤ (H1 X x₀)] [Module.Free ℤ (H1 X x₀)]
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hrank : Module.finrank ℤ (H1 X x₀) ≤ 2 * genus X)
    (hR1 : ∀ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
        (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
        (∀ i, isB i = loopToHomology (loops i)) → ArcR1Matrix loops cω)
    (hR2 : ∀ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
        (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
        (∀ i, isB i = loopToHomology (loops i)) → ArcR2Matrix loops cω) :
    Nonempty (PeriodCycleBasis X x₀) :=
  periodCycleBasis_of_tgen_of_periodInjective x₀ b cω hgen
    (h1PeriodInjective_of_finrank_le x₀ b hgen hrank) hR1 hR2

/-! ## Genus ≤ 1 corollaries: R1 (and R2 at g = 0) drop out

At `genus ≤ 1` the R1 block symmetry is automatic
(`arcPeriodMatrix_symm_of_genus_le_one`), so it need not be supplied. At
`genus = 0` the R2 field is vacuous (`arc_R2_of_genus_eq_zero`), so the
whole axiom reduces to `{T-GEN, KER-0}`. -/

/-- **R1 is free at `genus ≤ 1`.** The conditional constructor with the R1
hypothesis discharged by `arcPeriodMatrix_symm_of_genus_le_one`; only
R2-matrix remains besides `{T-GEN, KER-0}`. -/
theorem periodCycleBasis_of_tgen_of_periodInjective_genus_le_one
    (hg : genus X ≤ 1)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [DiscreteTopology (loopPeriodLattice x₀ b)]
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hker : ∀ v : H1 X x₀,
      Jacobians.Layer3.devValPeriodVec x₀ b v = 0 → v = 0)
    (hR2 : ∀ (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
        (isB : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)),
        (∀ i, isB i = loopToHomology (loops i)) → ArcR2Matrix loops cω) :
    Nonempty (PeriodCycleBasis X x₀) :=
  periodCycleBasis_of_tgen_of_periodInjective x₀ b cω hgen hker
    (fun loops _ _ =>
      show ArcR1Matrix loops cω from arcPeriodMatrix_symm_of_genus_le_one hg loops _) hR2

/-- **R1 and R2 are free at `genus = 0`.** The constructor reduces to
exactly `{T-GEN, KER-0}`: the genus-0 surface has the empty basis and
both Riemann relations are vacuous/automatic. -/
theorem periodCycleBasis_of_tgen_of_periodInjective_genus_zero
    (hg : genus X = 0)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    [DiscreteTopology (loopPeriodLattice x₀ b)]
    (hgen : AnalyticLoopsGenerateH1 x₀)
    (hker : ∀ v : H1 X x₀,
      Jacobians.Layer3.devValPeriodVec x₀ b v = 0 → v = 0) :
    Nonempty (PeriodCycleBasis X x₀) := by
  obtain ⟨loops, isB, htie⟩ :=
    exists_h1LoopBasis_of_periodInjective x₀ b hgen hker
  exact ⟨⟨loops, isB, htie,
    fun η ζ => arc_R1_of_genus_le_one (by omega) loops cω η ζ,
    fun η hη => arc_R2_of_genus_eq_zero hg loops cω η hη⟩⟩

end

end Jacobians.RiemannSurface
