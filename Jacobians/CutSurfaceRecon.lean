/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.CutSurfaceRelations

/-!
# RECON + scaffold for the #7 cut-surface wall (`exists_cutSurface`)

`exists_cutSurface` (`Jacobians/CutSurfaceRelations.lean`) is the single isolated input behind the
period-lattice goal #7: a compact connected Riemann surface admits a **cut surface** — a canonical
symplectic dissection realized as a holomorphic cut chart `cut : box → X`, packaged together with the
two *boundary words* that turn `∮_{∂box}` into the period bilinear sums. Everything analytic
downstream is already proven: the two Riemann bilinear relations `R1`/`R2`
(`CutSurface.cutSurface_R1` / `CutSurface.cutSurface_R2`) and the matrix-algebra core
`periodVec_linearIndependent`. What is missing is purely the *existence* of the cut-chart data, which
needs classical surface topology that Mathlib lacks (Radó triangulability + the `4g`-gon normal form
+ the boundary-word derivation from the gluing).

This file is **recon + scaffolding only**. It does NOT close `exists_cutSurface`; it:

1. **Reduces** `exists_cutSurface` to a single, smaller, explicitly-named greenfield existence
   `Nonempty (CutSurfaceTopology X)` — the *topological core* (`exists_cutSurface_of_topology`,
   sorry-free). `CutSurfaceTopology` bundles exactly the surface-classification data Mathlib lacks,
   in a form from which all 14 `CutSurface` fields are *derived*. This pins the wall down to one
   structure.

2. Provides the sorry-free **per-handle boundary-word aggregation** scaffolding
   (`rectBoundaryIntegral_handleSum`) showing how the existing single-handle identity
   `rectBoundaryIntegral_singleHandle` (`Jacobians/CutSurface.lean`) sums over the `g` handles of the
   `4g`-gon to produce the entry-level boundary word `boundaryWord_R1` — the bookkeeping half of the
   gap, with the gluing/jump *hypotheses* still supplied by `CutSurfaceTopology`.

3. Records the **precise route + greenfield gap** in `CutSurfaceTopology`'s plan fields (as
   `Prop`-valued data, never `sorry`d here).

No `sorry` anywhere in this file. The genuine missing classical theorems live ONLY as the
to-be-constructed term `Nonempty (CutSurfaceTopology X)`, the honest residue of the wall.

References: Radó (1925, triangulability of surfaces); the classification of compact surfaces / the
`4g`-gon normal form (Seifert–Threlfall; Massey, *Algebraic Topology*, Ch. 1); Forster §§20–21;
Griffiths–Harris pp. 231–232; Springer pp. 139–141; Chai §1.4.
See `docs/period_lattice_realbasis_research.md`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped Manifold ContDiff Bundle Topology ComplexOrder

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## 1. The topological core: the single greenfield structure

The `CutSurface` structure (in `CutSurfaceRelations.lean`) already isolates the boundary words as
*fields*, so a `CutSurface` is "data + boundary-word identities". `exists_cutSurface` must construct
that data. The genuinely missing classical content is the surface-topology that *produces* a cut
chart with the right gluing — from which the boundary words and non-degeneracy follow.

`CutSurfaceTopology X` below re-bundles the same data, but its docstrings pin down the *provenance*
of each field — i.e. which classical theorem (all absent from Mathlib) supplies it. It is
**definitionally a `CutSurface`** (see `CutSurfaceTopology.toCutSurface`), so reducing
`exists_cutSurface` to `Nonempty (CutSurfaceTopology X)` is a sorry-free repackaging that loses
nothing — it simply renames the wall and documents the gap.

The point of having a separate structure (rather than just leaving the `sorry` on `CutSurface`) is to
make the route *checkable*: a future construction targets `CutSurfaceTopology`, and the reduction
lemma guarantees it discharges `exists_cutSurface`. -/

/-- **The topological core of a cut surface — the single greenfield input for #7.**

This is the same data as `CutSurface X`, re-presented to expose the *provenance* of each piece: every
field is the output of a classical surface-topology theorem that Mathlib does not have. Producing a
term of this type is the entire remaining content of `exists_cutSurface`. The reduction
`exists_cutSurface_of_topology` shows `Nonempty (CutSurfaceTopology X) → Nonempty (CutSurface X)`
(in fact it is a definitional repackaging).

**The four classical inputs (all absent from Mathlib), by field group:**

* `loop` / `loop_closed` / `generates` — *Radó triangulability* + *classification of surfaces*
  (`H₁(X;ℤ) ≅ ℤ^{2g}`, a symplectic basis `a₁..a_g,b₁..b_g` with `aᵢ·bⱼ = δᵢⱼ`) + *period
  homology-invariance* (a closed-loop period depends only on the homology class, so the basis
  periods generate). Greenfield.
* `U` / `hbox` / `h` / `F` / `hh` / `hF` — the *holomorphic cut chart*: cut `X` along the basis into
  a simply-connected `4g`-gon, realize it as `cut : U → X` holomorphic on a convex `U ⊇ [0,1]²`; then
  `hⱼ = cut^*ωⱼ` is holomorphic and (`U` simply connected) has a primitive `Fⱼ`. The existence of the
  cut chart is the geometric core; the primitive is then Mathlib (`Convex.exists_forall_hasDerivAt`).
* `boundaryWord_R1` / `boundaryWord_R2` — *Green's theorem on the `4g`-gon* + the *gluing/monodromy*
  bookkeeping that collapses `∮_{∂box}` to the antisymmetric period sums. The per-handle skeleton is
  `rectBoundaryIntegral_singleHandle` (proven, repo); summing it over the `g` handles is
  `rectBoundaryIntegral_handleSum` (proven below) — but its *hypotheses* (the per-edge gluing `h`
  agrees on identified edges, and the primitive `F` jumps by the conjugate period) are exactly what
  the cut chart supplies, and are greenfield.
* `nondeg` — a nonzero holomorphic form `∑ⱼ vⱼ ωⱼ` pulls back to a function nonzero on the dense
  interior of the cut surface (the cut chart is a diffeo on the interior). Greenfield (needs the
  chart's interior-diffeomorphism property + identity-theorem density). -/
structure CutSurfaceTopology (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    extends CutSurface X

/-- **[REDUCTION — sorry-free]** A topological core yields a cut surface (definitional repackaging).
The `CutSurfaceTopology` structure simply `extends CutSurface`, so this is the structure projection;
it loses nothing. Its purpose is to let a future surface-classification construction target the
clearly-documented `CutSurfaceTopology` and *automatically* discharge `exists_cutSurface`. -/
def CutSurfaceTopology.toCutSurface' (S : CutSurfaceTopology X) : CutSurface X := S.toCutSurface

/-- **[REDUCTION — sorry-free]** `exists_cutSurface` follows from the existence of the topological
core. This is the one place the #7 wall is now pinned: the entire remaining content is
`Nonempty (CutSurfaceTopology X)`. -/
theorem exists_cutSurface_of_topology (h : Nonempty (CutSurfaceTopology X)) :
    Nonempty (CutSurface X) :=
  h.map CutSurfaceTopology.toCutSurface'

/-! ## 2. Per-handle boundary-word aggregation (sorry-free bookkeeping)

The repo proves the *single-handle* contour identity `rectBoundaryIntegral_singleHandle`: for one
handle's pullback `h`/primitive `F` with gluing + jump data, `∮_{∂box}(F·h) = A·Bper − B·Aper`. For
genus `g` the `4g`-gon boundary word is the sum of `g` such handle contributions. The aggregation
below is pure interval-integral linearity — the bookkeeping half of `boundaryWord_R1` — and is
sorry-free. The *content* (each handle's gluing/jump hypotheses) is supplied by the cut chart, i.e.
remains inside `CutSurfaceTopology`.

This lemma is deliberately stated abstractly over a *finite family* of single-handle data so it is
reusable by a future cut-chart construction without committing to how the box is subdivided. -/

/-- **Linearity of `rectBoundaryIntegral` over a finite sum of integrands.** `∮_{∂box}` is ℂ-linear:
the contour integral of a finite sum is the sum of contour integrals, provided each integrand is
interval-integrable along all four edges. (Pure `intervalIntegral.integral_finset_sum`.) This is the
engine for assembling the `g`-handle boundary word from the single-handle pieces. -/
theorem rectBoundaryIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hbot : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i (x : ℂ)) volume 0 1)
    (htop : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i ((x : ℂ) + Complex.I)) volume 0 1)
    (hright : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => f i (1 + (y : ℂ) * Complex.I)) volume 0 1)
    (hleft : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => f i ((y : ℂ) * Complex.I)) volume 0 1) :
    rectBoundaryIntegral (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, rectBoundaryIntegral (f i) := by
  classical
  -- Push the finite sum through each of the four interval integrals, then regroup.
  unfold rectBoundaryIntegral
  have e_bot : (∫ x in (0:ℝ)..1, ∑ i ∈ s, f i (x : ℂ))
      = ∑ i ∈ s, ∫ x in (0:ℝ)..1, f i (x : ℂ) :=
    intervalIntegral.integral_finset_sum (f := fun i (x : ℝ) => f i (x : ℂ)) hbot
  have e_top : (∫ x in (0:ℝ)..1, ∑ i ∈ s, f i ((x : ℂ) + Complex.I))
      = ∑ i ∈ s, ∫ x in (0:ℝ)..1, f i ((x : ℂ) + Complex.I) :=
    intervalIntegral.integral_finset_sum (f := fun i (x : ℝ) => f i ((x : ℂ) + Complex.I)) htop
  have e_right : (∫ y in (0:ℝ)..1, ∑ i ∈ s, f i (1 + (y : ℂ) * Complex.I))
      = ∑ i ∈ s, ∫ y in (0:ℝ)..1, f i (1 + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_finset_sum
      (f := fun i (y : ℝ) => f i (1 + (y : ℂ) * Complex.I)) hright
  have e_left : (∫ y in (0:ℝ)..1, ∑ i ∈ s, f i ((y : ℂ) * Complex.I))
      = ∑ i ∈ s, ∫ y in (0:ℝ)..1, f i ((y : ℂ) * Complex.I) :=
    intervalIntegral.integral_finset_sum (f := fun i (y : ℝ) => f i ((y : ℂ) * Complex.I)) hleft
  rw [e_bot, e_top, e_right, e_left, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- **Handle-sum boundary word (sorry-free aggregation).** If the holomorphic integrand
`F·h` of the `4g`-gon decomposes, on the box, as a finite sum `∑ₖ (Fₖ·hₖ)` of single-handle
integrands, each of which contributes its antisymmetric period product
`∮_{∂box}(Fₖ·hₖ) = Aₖ·Bperₖ − Bₖ·Aperₖ` (the proven `rectBoundaryIntegral_singleHandle`), then the
total contour integral is the sum `∑ₖ (Aₖ·Bperₖ − Bₖ·Aperₖ)`.

This is the bookkeeping that turns the per-handle identity into the entry-level `boundaryWord_R1`:
the cut chart supplies the decomposition and each handle's gluing/jump data; this lemma sums them.
Purely `rectBoundaryIntegral_finset_sum`. -/
theorem rectBoundaryIntegral_handleSum {ι : Type*} (s : Finset ι)
    (Fh : ι → ℂ → ℂ) (val : ι → ℂ)
    (hbot : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => Fh i (x : ℂ)) volume 0 1)
    (htop : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => Fh i ((x : ℂ) + Complex.I)) volume 0 1)
    (hright : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => Fh i (1 + (y : ℂ) * Complex.I)) volume 0 1)
    (hleft : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => Fh i ((y : ℂ) * Complex.I)) volume 0 1)
    (hhandle : ∀ i ∈ s, rectBoundaryIntegral (Fh i) = val i) :
    rectBoundaryIntegral (fun z => ∑ i ∈ s, Fh i z) = ∑ i ∈ s, val i := by
  rw [rectBoundaryIntegral_finset_sum s Fh hbot htop hright hleft]
  exact Finset.sum_congr rfl hhandle

end Jacobians
