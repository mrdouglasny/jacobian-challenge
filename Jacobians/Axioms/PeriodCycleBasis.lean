/-
`AX_PeriodCycleBasis`: every compact connected Riemann surface admits a
**piecewise-real-analytic ℤ-basis of `H_1` satisfying Riemann's bilinear
relations arc-level** — the D1 merged restatement (2026-06-10) of the former
`AX_AnalyticCycleBasis + AX_RBR1 + AX_RBR2`.

# Statement (informal)

For `X` a compact, connected, T2, complex 1-manifold of genus `g`, there
exist `2g` piecewise-real-analytic loops
    `α_1, …, α_g, β_1, …, β_g : unitInterval → X`
based at `x₀ : X`, whose homology classes form a ℤ-basis of `H_1(X, ℤ)`,
and whose own canonical arc periods satisfy Riemann's bilinear relations:

  R1 (isotropy / Stokes):    `Q(P(η), P(ζ)) = 0`   for all holomorphic
      1-forms `η, ζ`, where `P(η) = ((∫_{α_i} η)_i, (∫_{β_i} η)_i)` and
      `Q((a,b),(a',b')) = ∑_k a_k b'_k − b_k a'_k`;
  R2 (Hodge positivity):     `0 < Re (i · Q(P(η), conj P(η)))` for `η ≠ 0`.

Formally: `Nonempty (PeriodCycleBasis X x₀)` where `PeriodCycleBasis`
packages the loops, the basis property, the Hurewicz tie, and R1/R2.

# Design history (D1, 2026-06-10)

This axiom **merges** three prior axioms (audit:
`docs/planning/CYCLEBASIS_ALTERNATIVES.md` §1, owner-approved D1,
deep-think endorsed 2026-06-10):

* `AX_AnalyticCycleBasis` — same `loops`/`isBasis`/`loops_to_basis` fields;
  its `symplectic` field (intersection-form values on the basis) had **zero
  proof consumers** and is dropped, removing the `Axioms.intersectionForm`
  type-dependency from every Buzzard headline.
* `AX_RBR1` / `AX_RBR2` (Layer-3 Phase C, DT-vetted 2026-06-09) — previously
  quantified over *every* basis of the old structure, with the dropped
  symplectic field as their satisfiability guard (a `GL(2g,ℤ) ∖ Sp(2g,ℤ)`
  re-indexing violates them). Restating R1/R2 **arc-level over the bundled
  loops' own `canonicalArcIntegral`s** makes the bundle self-guarding: each
  witness carries its own bilinear relations, and the Layer-3 engine consumes
  them on the same `Classical.choice` witness that defines `loopIntegralToH1`
  (the `loopIntegralToH1_loop` pattern), dissolving the global-choice trap.

The merged statement is verbatim "every compact Riemann surface has a
canonical homology basis satisfying Riemann's bilinear relations"
(Griffiths–Harris Ch. 2 §2; Forster §§20–21). It is **strictly implied by
the previous axiom set** (instantiate the old RBR1/RBR2 at the chosen
symplectic basis and rewrite periods through `loopIntegralToH1_loop`), so
satisfiability is inherited from the 2026-06-09 per-axiom DT vettings of all
three — weaker-or-equal, never stronger.

# Why we assume this / why it is true

See the discharge analysis in `docs/planning/CYCLEBASIS_ALTERNATIVES.md`:
the loops + basis come from any dissection of the surface (4g-gon model /
branched-cover slit sheets), R1 from Stokes on the cut surface, R2 from the
Hodge norm `i∫_X η ∧ η̄ > 0`. The recommended general-X discharge route is
the branched-cover construction over an RR-supplied meromorphic function
(post-keystone), with R1/R2 through the Kirov port's proven boundary-word
engine (`riemann_R1_of_boundaryWord`, `riemann_R2_posDef_of_boundaryWord`).

# Vetting

**Standard. Sources: DT (deep-think, 2026-06-10 — design review of this
merged restatement), inheriting the 2026-06-09 per-axiom DT vettings of
`AX_AnalyticCycleBasis`, `AX_RBR1`, `AX_RBR2` (each SATISFIABLE/FAITHFUL,
RBR2 sign verified on the genus-1 torus).**
  - Non-vacuous: `g = 0` gives the empty basis with R1/R2 vacuous
    (`projectiveLineCycleBasis` is a concrete axiom-light witness); `g = 1`
    has the classical A/B cycles with `R2 = Im(ω₂/ω₁) > 0` after orienting.
  - **Index-split alignment guard (DT finding 5).** `arcPeriodVec` is
    defined *explicitly* through `αEmbed`/`βEmbed` so that the first
    component is the `g` A-periods and the second the `g` B-periods —
    exactly the layout `Q` expects. The `@[simp]` lemmas
    `arcPeriodVec_fst`/`arcPeriodVec_snd` pin this contract in the kernel.
  - Not circular: does not reference `periodMap`/`loopIntegralToH1` (which
    are *defined from* the chosen witness downstream), only the chart-local
    canonical arc integral.

# Relationship to other axioms

Subsumes (as before) `AX_H1FreeRank2g` (now a theorem). The intersection
form (`Axioms/IntersectionForm.lean`) is **no longer referenced**: it and
its two law axioms remain in the build as non-critical Part-3 documentation
debt (owner decision D2: keep), and drop out of every headline closure.

# References

* P. Griffiths & J. Harris, *Principles of Algebraic Geometry*, Ch. 2 §2.
* O. Forster, *Lectures on Riemann Surfaces*, §§19–21.
* D. Mumford, *Tata Lectures on Theta I*, Ch. II §2.
-/
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Genus
import Jacobians.RiemannSurface.CanonicalArcIntegral
import Jacobians.Layer3.RiemannBilinear

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface
open Jacobians.Layer3 (PeriodVector Q)

/-- The `α`-cycle embedding: `Fin (genus X)` → `Fin (2 * genus X)` mapping
`i ↦ i` (the first `g` indices). -/
noncomputable def αEmbed {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (i : Fin (genus X)) : Fin (2 * genus X) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- The `β`-cycle embedding: `Fin (genus X)` → `Fin (2 * genus X)` mapping
`i ↦ g + i` (the last `g` indices). -/
noncomputable def βEmbed {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (i : Fin (genus X)) : Fin (2 * genus X) :=
  ⟨genus X + i.val, by have := i.isLt; omega⟩

/-- The underlying topological path of an analytic loop. -/
def loopToPath {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {x₀ : X} (loop : AnalyticLoop X x₀) : Path x₀ x₀ where
  toFun := loop.arc.toFun
  continuous_toFun := loop.arc.continuous_toFun
  source' := by
    simpa [AnalyticArc.toFun] using loop.start_eq
  target' := by
    simpa [AnalyticArc.toFun] using loop.end_eq

/-- The first-homology class of an analytic loop (Hurewicz:
loop ↦ [loop] ∈ H₁). -/
noncomputable def loopToHomology {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {x₀ : X} (loop : AnalyticLoop X x₀) : H1 X x₀ :=
  Additive.ofMul (Abelianization.of
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopToPath loop))))

/-- The **arc-level period vector** of a holomorphic 1-form `η` over a
`Fin (2g)`-indexed family of analytic loops.

**LAYOUT CONTRACT (index-split alignment).** The first component is the `g`
A-periods — canonical arc integrals over `loops (αEmbed i)`, i.e. indices
`0 … g−1` — and the second component is the `g` B-periods — integrals over
`loops (βEmbed i)`, i.e. indices `g … 2g−1`. This matches the layout of the
Layer-3 symplectic dual form `Q ((a, b), (a', b')) = ∑ₖ aₖ b'ₖ − bₖ a'ₖ`
exactly: `Q (arcPeriodVec …) (arcPeriodVec …)` is `∑ Aₖ B'ₖ − Bₖ A'ₖ`.
The `@[simp]` lemmas `arcPeriodVec_fst` / `arcPeriodVec_snd` pin this
contract; do not re-derive the projections by hand. -/
noncomputable def arcPeriodVec {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {x₀ : X}
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) : PeriodVector (genus X) :=
  (fun i => canonicalArcIntegral (loops (αEmbed i)).arc η,
    fun i => canonicalArcIntegral (loops (βEmbed i)).arc η)

/-- The entrywise complex-conjugate arc-level period vector (same
α/β layout contract as `arcPeriodVec`). -/
noncomputable def conjArcPeriodVec {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {x₀ : X}
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) : PeriodVector (genus X) :=
  (fun i => star (canonicalArcIntegral (loops (αEmbed i)).arc η),
    fun i => star (canonicalArcIntegral (loops (βEmbed i)).arc η))

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {x₀ : X}

/-- Layout pin: the FIRST component of `arcPeriodVec` is the A-periods,
indexed through `αEmbed`. -/
@[simp]
theorem arcPeriodVec_fst (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (arcPeriodVec loops η).1 i = canonicalArcIntegral (loops (αEmbed i)).arc η :=
  rfl

/-- Layout pin: the SECOND component of `arcPeriodVec` is the B-periods,
indexed through `βEmbed`. -/
@[simp]
theorem arcPeriodVec_snd (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (arcPeriodVec loops η).2 i = canonicalArcIntegral (loops (βEmbed i)).arc η :=
  rfl

@[simp]
theorem conjArcPeriodVec_fst (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (conjArcPeriodVec loops η).1 i = star ((arcPeriodVec loops η).1 i) :=
  rfl

@[simp]
theorem conjArcPeriodVec_snd (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (conjArcPeriodVec loops η).2 i = star ((arcPeriodVec loops η).2 i) :=
  rfl

/-- The data of a piecewise-real-analytic ℤ-basis of `H_1(X, ℤ)` whose
representing loops satisfy Riemann's bilinear relations **arc-level**.

The basis is indexed by `Fin (2 * genus X)` directly, with the split into
α-cycles and β-cycles handled by `αEmbed` / `βEmbed`; `arcPeriodVec`
realizes that split as the `(A-periods, B-periods)` layout consumed by the
Layer-3 form `Q` (see the layout contract on `arcPeriodVec`).

(D1 merged restatement, 2026-06-10 — replaces `AnalyticCycleBasis`; the
intersection-form `symplectic` field was dropped as proof-unconsumed, with
R1/R2 carried per-witness instead of as basis-quantified axioms.) -/
structure PeriodCycleBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) where
  /-- The `2g` piecewise-real-analytic loops based at `x₀`. -/
  loops : Fin (2 * genus X) → AnalyticLoop X x₀
  /-- The ordered ℤ-basis of `H_1(X, ℤ)` represented by `loops`. -/
  isBasis : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)
  /-- The basis vector at index `i` is the homology class of `loops i`
  (the Hurewicz tie — the anti-vacuity pin). -/
  loops_to_basis : ∀ i : Fin (2 * genus X), isBasis i = loopToHomology (loops i)
  /-- **First Riemann bilinear relation (isotropy / Stokes), arc-level.**
  The arc period vectors of any two holomorphic 1-forms over these loops
  are isotropic for the symplectic dual form `Q`. Equivalently
  `∫_X η ∧ ζ = 0` (the wedge of two `(1,0)`-forms vanishes on a curve). -/
  R1 : ∀ η ζ : HolomorphicOneForm X,
    Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0
  /-- **Second Riemann bilinear relation (Hodge positivity), arc-level.**
  For every nonzero holomorphic 1-form `η`,
  `i · Q(arc period η, conj arc period η)` is a strictly positive real.
  Equivalently `i ∫_X η ∧ η̄ > 0` (the Hodge norm). -/
  R2 : ∀ η : HolomorphicOneForm X, η ≠ 0 →
    0 < (Complex.I * Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re

/-- **Axiom.** Every compact connected Riemann surface admits a
piecewise-real-analytic ℤ-basis of `H_1(X, ℤ)` whose loops satisfy
Riemann's bilinear relations arc-level.

See the file header for the merge history (D1), satisfiability inheritance,
proof sketches, and references. Rating: Standard. Sources: DT (2026-06-10
design vet of the merged restatement) + DT (2026-06-09 per-axiom vets of
the three merged predecessors). -/
axiom AX_PeriodCycleBasis {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Nonempty (PeriodCycleBasis X x₀)

end Jacobians.Axioms
