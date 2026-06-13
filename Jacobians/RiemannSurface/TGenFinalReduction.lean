/-
# T-GEN final reduction: composing the four conditional reductions

This module performs the **final composition** of the four proven, axiom-free
conditional reductions of the topological residual **T-GEN**
(`AnalyticLoopsGenerateH1`) into a single headline theorem. It introduces no new
mathematics and no new axiom: it threads three existing modules together with
elementary `Path.Homotopic` algebra, leaving exactly **two** named classical
hypotheses as explicit arguments.

## The reduction chain (all links proved elsewhere, sorry-free, standard-3)

```
continuous loop  p : Path x₀ x₀
   │  SmoothLoopApproxHyp        (Whitney: continuous ⇝ smooth, rel endpoints)
   ▼
smooth path  δ : Path x₀ x₀  with  IsSmoothPath 𝓘(ℂ) δ
   │  RECONCILE (this file): IsSmoothPath 𝓘(ℂ) δ ≡ IsSmoothCurve δ.extend  (defeq)
   ▼
smooth curve  δ.extend : ℝ → X  with  IsSmoothCurve δ.extend
   │  SmoothLoopAnalyticApprox   (Grauert: smooth ⇝ real-analytic, rel endpoints)
   ▼
AnalyticLoop  δₐ  with  loopToPath δₐ  ≃  curveToPath δ.extend  =  δ
   │  Path.Homotopic.trans  with  δ ≃ p  (from SmoothLoopApproxHyp)
   ▼
loopToPath δₐ  ≃  p          ⟹  ContinuousLoopHasAnalyticRep x₀   (= AAW)
   │  analyticLoopsGenerateH1_of_analyticRep  (AnalyticApproxGeneration.lean)
   ▼
AnalyticLoopsGenerateH1 x₀   (= T-GEN)
```

## The key reconciliation (honest assessment)

The SMOOTH lane (`SmoothLoopApprox.lean`) outputs `IsSmoothPath 𝓘(ℂ) δ`, defined
as `∀ r, ContDiffAt ℝ ∞ (fun u => extChartAt 𝓘(ℂ) (δ.extend r) (δ.extend u)) r`.
The ANALYTIC lane (`SmoothAnalyticLoop.lean`) consumes `IsSmoothCurve γ`, defined
as `∀ r, ContDiffAt ℝ ∞ (fun u => extChartAt 𝓘(ℂ) (γ r) (γ u)) r`.

Taking `γ := δ.extend` makes these two predicates **definitionally identical**:
same moving-chart readout `extChartAt 𝓘(ℂ)`, same parametrisation domain `ℝ`
(`δ.extend : ℝ → X`), same smoothness order `∞ : ℕ∞ω`, same pointwise-at-every-`r`
quantifier. The reconciliation `isSmoothPath_iff_isSmoothCurve_extend` below holds
**by `Iff.rfl`** — there is *no* gap, no order mismatch, no `[0,1]`-vs-`ℝ`
mismatch, no endpoint bookkeeping. The two lanes were designed against the same
moving-chart convention precisely so this junction is free.

The only non-`rfl` bookkeeping is that `curveToPath δ.extend` and `δ` are equal as
paths (`curveToPath_extend_eq`, via `Path.extend_extends'`), which lets the two
homotopies compose.

## Main results

* `isSmoothPath_iff_isSmoothCurve_extend` — the (defeq) reconciliation.
* `curveToPath_extend_eq` — `curveToPath δ.extend … = δ`.
* `analyticLoopsGenerateH1_of_smoothApprox_analyticApprox` — **the headline**:
  `SmoothLoopApproxHyp X → (∀ x₀, SmoothLoopAnalyticApprox x₀) →
  AnalyticLoopsGenerateH1 x₀`, i.e. **T-GEN reduces to {Whitney, Grauert}**,
  fully formalized, sorry-free, no new axiom.

No new axiom; nothing depends on `AX_PeriodCycleBasis`.
-/
import Jacobians.RiemannSurface.AnalyticApproxGeneration
import Jacobians.RiemannSurface.SmoothAnalyticLoop
import Jacobians.RiemannSurface.SmoothLoopApprox

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open unitInterval
open Jacobians.Axioms (loopToPath)

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ### The reconciliation: `IsSmoothPath 𝓘(ℂ) δ ≡ IsSmoothCurve δ.extend` -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- **The key reconciliation, by `rfl`.** The SMOOTH lane's output predicate
`IsSmoothPath 𝓘(ℂ) δ` is *definitionally* the ANALYTIC lane's input predicate
`IsSmoothCurve δ.extend`: both unfold to
`∀ r, ContDiffAt ℝ ∞ (fun u => extChartAt 𝓘(ℂ) (δ.extend r) (δ.extend u)) r`.
There is no parametrisation, order, or endpoint mismatch — the two lanes share the
moving-chart smoothness convention by design, so this junction is free. -/
theorem isSmoothPath_iff_isSmoothCurve_extend {x₀ : X} (δ : Path x₀ x₀) :
    IsSmoothPath 𝓘(ℂ) δ ↔ IsSmoothCurve δ.extend :=
  Iff.rfl

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
/-- The path underlying the *curve* `δ.extend` (its restriction to `unitInterval`)
is the path `δ` itself. Holds by `Path.ext` from `Path.extend_extends'`. Lets the
ANALYTIC-lane homotopy (`loopToPath δₐ ≃ curveToPath δ.extend`) compose with the
SMOOTH-lane homotopy (`δ ≃ p`). -/
theorem curveToPath_extend_eq {x₀ : X} (δ : Path x₀ x₀) :
    curveToPath (X := X) δ.extend.continuous (Path.extend_zero δ)
        (by rw [Path.extend_zero, Path.extend_one]) = δ := by
  ext t
  exact Path.extend_extends' δ ⟨t.val, t.2⟩

/-! ### The headline composition -/

/-- **T-GEN reduces to {Whitney, Grauert}.**

The general-`X` discharge of the topological residual **T-GEN**
(`AnalyticLoopsGenerateH1`) down to exactly two classical, Mathlib-absent
approximation theorems supplied as explicit hypotheses:

* `hsmooth : SmoothLoopApproxHyp X` — every continuous loop is homotopic rel
  endpoints to a smooth one (1-dimensional Whitney smooth approximation);
* `hanalytic : ∀ x₀, SmoothLoopAnalyticApprox x₀` — every smooth loop is homotopic
  rel endpoints to a real-analytic one (Grauert/Whitney–Bruhat real-analytic
  approximation).

The proof composes the four landed reductions: SMOOTH (`SmoothLoopApproxHyp`)
produces a smooth `δ`; the (defeq) reconciliation reads `IsSmoothPath 𝓘(ℂ) δ` as
`IsSmoothCurve δ.extend`; ANALYTIC (`SmoothLoopAnalyticApprox`) produces a
homotopic `AnalyticLoop`; chaining the two homotopies with `Path.Homotopic.trans`
yields `ContinuousLoopHasAnalyticRep x₀` (= AAW); and
`analyticLoopsGenerateH1_of_analyticRep` (the AAW ⟹ T-GEN reduction, itself the K0
keystone bridge) closes it.

Sorry-free, no new axiom, independent of `AX_PeriodCycleBasis`: the entire content
beyond the two named hypotheses is `Path.Homotopic` algebra plus the defeq
junction. -/
theorem analyticLoopsGenerateH1_of_smoothApprox_analyticApprox {x₀ : X}
    (hsmooth : SmoothLoopApproxHyp (H := ℂ) (IM := 𝓘(ℂ)) X)
    (hanalytic : ∀ y : X, SmoothLoopAnalyticApprox y) :
    AnalyticLoopsGenerateH1 x₀ := by
  apply analyticLoopsGenerateH1_of_analyticRep
  -- Goal: ContinuousLoopHasAnalyticRep x₀, i.e. every loop has an analytic rep.
  intro p
  -- SMOOTH: a smooth path δ homotopic to p.
  obtain ⟨δ, hδsmooth, hpδ⟩ := hsmooth (x₀ := x₀) p
  -- RECONCILE (defeq): IsSmoothPath 𝓘(ℂ) δ is IsSmoothCurve δ.extend.
  have hcurve : IsSmoothCurve δ.extend :=
    (isSmoothPath_iff_isSmoothCurve_extend δ).mp hδsmooth
  -- Endpoint facts for the curve δ.extend.
  have hclosed : δ.extend 1 = δ.extend 0 := by rw [Path.extend_zero, Path.extend_one]
  have hsrc : δ.extend 0 = x₀ := Path.extend_zero δ
  -- ANALYTIC: a homotopic AnalyticLoop δₐ.
  obtain ⟨δₐ, hδₐ⟩ :=
    hanalytic x₀ δ.extend δ.extend.continuous hcurve hclosed hsrc
  refine ⟨δₐ, ?_⟩
  -- hδₐ : loopToPath δₐ ≃ curveToPath δ.extend …  ;  rewrite curveToPath = δ.
  rw [curveToPath_extend_eq δ] at hδₐ
  -- Chain: loopToPath δₐ ≃ δ ≃ p   (hpδ : p ≃ δ, so δ ≃ p via symm).
  exact hδₐ.trans hpδ.symm

end

end Jacobians.RiemannSurface
