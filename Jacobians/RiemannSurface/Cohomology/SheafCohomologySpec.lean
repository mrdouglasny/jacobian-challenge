/-
# Faithfulness acceptance suite for the sheaf-cohomology axiom cluster

Buzzard's challenge pins the *top* of the tower (`Jacobian`, `ofCurve`) with
independent target theorems (`genus_eq_zero_iff_homeo`, `ofCurve_inj`) that a
degenerate definition would fail. This file applies the **same strategy one
layer down**: it states the acceptance criteria a candidate definition of
`H0`/`H1`/`LineBundle`/`canonicalDivisor` (sheaf cohomology of a divisor on a
compact Riemann surface) must satisfy to be *faithful* — i.e. to genuinely
compute `H⁰(X, 𝒪(D))` and `H¹(X, 𝒪(D))` rather than collapse to a stub.

**Contract.** Each declaration below is a `Prop`-valued statement (no proof — it
is a *target*, like a Buzzard `sorry`). The cluster is faithful **iff every one
of these becomes provable** once the axioms are replaced by real `def`s. They are
deliberately *independent* of `AX_RiemannRoch`/`AX_SerreDuality` (those are
restated here only as backbone consistency checks): the discriminating power is
in the **non-vacuity anchors** (§1) and the **concrete computations** (§3), which
a token/degenerate definition (`H0 := ℂ`, `H1 := PUnit`, `LineBundle := PUnit`)
provably *cannot* satisfy.

**Why this is the right gate.** Per `DEFINITIONS_AUDIT.md`, the kernel never
checks that a `def` *means* what it should. The recipes for this cluster (see
`docs/planning/PHASE_3_INFRA_PLAN.md` §A) propose token discharges that would
lower the axiom count while voiding the dimension content. This suite is the
machine-checkable test that separates a faithful discharge from a hollow one: a
discharge PR for `H0`/`H1` must turn the §1/§3 targets into theorems, or it is a
regression, not progress.

**The recursion (Buzzard, downward).**
- *Top* — already pinned: `genus ProjectiveLine = 0`, `genus (Elliptic …) = 1`
  (axiom-free theorems).
- *Middle* — this file: `H0`/`H1` pinned by Riemann–Roch + Serre + vanishing +
  monotonicity + the canonical-degree/holomorphic-differential identities, all
  referencing the already-pinned `genus`.
- *Bottom* — §3: those abstract pins bottom out in **explicit ℂ-dimensions on
  `ProjectiveLine` and `Elliptic`** (`h⁰(𝒪(n·p)) = n+1` on ℙ¹, etc.), which
  reduce to decidable arithmetic. A degenerate definition fails here first.

## References
Forster, *Lectures on Riemann Surfaces*, Ch. II §16 (𝒪(D)); Ch. III §16–17
(Riemann–Roch, Serre). Mumford, *Algebraic Geometry I*, Ch. II.
-/
import Jacobians.RiemannSurface.Cohomology.LineBundle
import Jacobians.RiemannSurface.Genus
import Jacobians.ProjectiveCurve.Line

namespace Jacobians.RiemannSurface.Cohomology.SheafCohomologySpec

open scoped Manifold ContDiff
open Jacobians.Axioms Jacobians.RiemannSurface

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## §1. Non-vacuity anchors — a degenerate `H0`/`H1` fails these -/

/-- **A1 (global functions are constants).** On a compact connected Riemann
surface, the global sections of the trivial bundle `𝒪(0)` are exactly the
constants: `H⁰(X, 𝒪(0)) ≅ ℂ`. This is the foundational non-vacuity witness — the
sheaf-cohomology analogue of `localOrder_pow`. A `def H0 := ℂ` passes this one
test but fails A2/A3/§3; a `def H0 := PUnit` fails it outright. -/
def globalFunctions_eq_constants : Prop :=
  Nonempty (H0 (LineBundle.ofDivisor (0 : Divisor X)) ≃ₗ[ℂ] ℂ)

/-- **A2 (no sections in negative degree).** If `deg D < 0` then `𝒪(D)` has no
nonzero global sections: `H⁰(X, 𝒪(D))` is trivial. A constant-valued `H0`
(`:= ℂ`) fails this — it would exhibit a section of every degree. -/
def noSections_of_negativeDegree (D : Divisor X) : Prop :=
  Divisor.deg X D < 0 → Subsingleton (H0 (LineBundle.ofDivisor D))

/-- **A3 (H¹ vanishing in high degree).** If `deg D > 2g − 2` then
`H¹(X, 𝒪(D))` vanishes. Pins `H1` against being a fixed nonzero stub. -/
def H1_vanishing_of_largeDegree (D : Divisor X) : Prop :=
  2 * (genus X : ℤ) - 2 < Divisor.deg X D → Subsingleton (H1 (LineBundle.ofDivisor D))

/-! ## §2. Structural pins — the divisor/genus/canonical interplay -/

/-- **S1 (canonical degree).** `deg K_X = 2g − 2`. -/
def canonicalDivisor_degree : Prop :=
  Divisor.deg X (canonicalDivisor X) = 2 * (genus X : ℤ) - 2

/-- **S2 (holomorphic differentials).** `H⁰(X, 𝒪(K)) ≅ ℂ^g`: the space of global
holomorphic 1-forms has dimension equal to the genus. This recursively pins `H0`
to the *already-pinned* `genus` — a degenerate `H0` would break the genus link. -/
def holomorphicDifferentials_dim : Prop :=
  Nonempty (H0 (LineBundle.ofDivisor (canonicalDivisor X)) ≃ₗ[ℂ] (Fin (genus X) → ℂ))

/-- **S3 (sections grow with the divisor).** Adding an effective point `p` to `D`
can only enlarge the sections: there is an injective ℂ-linear inclusion
`H⁰(𝒪(D)) ↪ H⁰(𝒪(D + p))`. A constant `H0` has no such nontrivial inclusion
structure. -/
def sections_monotone (D : Divisor X) (p : X) : Prop :=
  ∃ f : H0 (LineBundle.ofDivisor D) →ₗ[ℂ]
        H0 (LineBundle.ofDivisor (D + FreeAbelianGroup.of p)),
    Function.Injective f

/-! ## §2b. Backbone consistency — restatements of the existing axioms.
These follow from `AX_RiemannRoch`/`AX_SerreDuality` *now*; a faithful `def`
must keep them as theorems (they are necessary, not sufficient — hence §1/§3). -/

/-- **B1 (Riemann–Roch + finiteness).** `h⁰(D) − h¹(D) = deg D + 1 − g`, AND
both spaces are finite-dimensional. The finiteness is **asserted, not assumed**:
gating it behind `[FiniteDimensional …]` instances (as an earlier draft did) made
the equation vacuously true for a degenerate definition with infinite-dimensional
`H⁰`/`H¹` — a correct sheaf cohomology of a coherent sheaf on a compact manifold
is always finite-dimensional (Cartan–Serre), so a faithful `def` must prove it.
*(Loophole flagged by Gemini-3.1-Pro review, 2026-06-04.)* -/
def riemannRoch (D : Divisor X) : Prop :=
  FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))
    ∧ FiniteDimensional ℂ (H1 (LineBundle.ofDivisor D))
    ∧ (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
        (Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ)
      = Divisor.deg X D + 1 - (genus X : ℤ)

/-- **B2 (Serre duality).** `H¹(𝒪(D)) ≅ H⁰(𝒪(K − D))^*`. -/
def serreDuality (D : Divisor X) : Prop :=
  Nonempty (H1 (LineBundle.ofDivisor D) ≃ₗ[ℂ]
    Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D))))

/-! ## §3. Concrete teeth — explicit dimensions on `ProjectiveLine` (genus 0).
These do **not** follow from the abstract axioms: they require the definition to
actually *compute* on a known curve. A degenerate `H0` gives the wrong number and
fails here first. (Elliptic genus-1 analogues are the obvious successors.) -/

open Jacobians.ProjectiveCurve in
/-- **C1 (ℙ¹ section count).** On `ProjectiveLine` (genus 0),
`H⁰(𝒪(n·p)) ≅ ℂ^{n+1}` — the degree-`≤ n` polynomials. The single most
discriminating test: a degenerate `H0` cannot produce a space whose dimension
tracks `n`. -/
def projectiveLine_H0_dim (p : ProjectiveLine) (n : ℕ) : Prop :=
  Nonempty (H0 (LineBundle.ofDivisor ((n : ℤ) • FreeAbelianGroup.of p))
    ≃ₗ[ℂ] (Fin (n + 1) → ℂ))

open Jacobians.ProjectiveCurve in
/-- **C2 (ℙ¹ H¹ vanishing).** On `ProjectiveLine`, `H¹(𝒪(D)) = 0` whenever
`deg D ≥ −1` (genus-0 vanishing). -/
def projectiveLine_H1_vanishing (D : Divisor ProjectiveLine) : Prop :=
  -1 ≤ Divisor.deg ProjectiveLine D → Subsingleton (H1 (LineBundle.ofDivisor D))

/-! ## §4. The deepest pin (documented target — needs manifold-meromorphic API)

Gemini-3.1-Pro review (2026-06-04) identified the single most important *missing*
pin: the dimension-counting tests above are all satisfiable, in principle, by an
abstract ℂ-vector-space construction *disconnected from functions on `X`*. The
genuine content of `H⁰(X, 𝒪(D))` is that it **is** the space of meromorphic
functions `f` on `X` with `div f + D ≥ 0`:
```
∃ emb : H0 (𝒪 D) →ₗ[ℂ] (X → ℂ), Function.Injective emb ∧
  ∀ s, MeromorphicOnManifold (emb s) ∧ ∀ x, -(coeff D x) ≤ orderAt (emb s) x
```
This is **not yet stateable faithfully**: Mathlib's `meromorphicOrderAt` is for
functions on a normed field `𝕜 → E`, not on a manifold `X`; the chart-local
meromorphic order (and the divisor-coefficient `coeff D x`) are exactly the
`sheafOfDivisor` infrastructure a real `H0` discharge must build (see
`docs/planning/PHASE_3_INFRA_PLAN.md` §A.3). So this pin is **part of the
`sheafOfDivisor` milestone's own acceptance**: the build that defines `H0`
faithfully will, in the same stroke, make this statement expressible and true.
Recorded here as the binding final criterion — a discharge that proves §1–§3 but
cannot exhibit this embedding is dimension-correct but *not* `𝒪(D)`. -/

/-! ## The suite

`SheafCohomologyFaithful` bundles the generic pins (quantified over every compact
connected Riemann surface) with the concrete `ProjectiveLine` computations. A
discharge of the `H0`/`H1`/`LineBundle`/`canonicalDivisor` cluster is **accepted
as faithful** exactly when this `Prop` is proved. -/
def SheafCohomologyFaithful : Prop :=
  (∀ (Y : Type u) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
      [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y],
      globalFunctions_eq_constants Y
        ∧ canonicalDivisor_degree Y
        ∧ holomorphicDifferentials_dim Y
        ∧ (∀ D : Divisor Y, noSections_of_negativeDegree Y D)
        ∧ (∀ D : Divisor Y, H1_vanishing_of_largeDegree Y D)
        ∧ (∀ (D : Divisor Y) (p : Y), sections_monotone Y D p)
        ∧ (∀ D : Divisor Y, riemannRoch Y D)
        ∧ (∀ D : Divisor Y, serreDuality Y D))
    ∧ (∀ (p : Jacobians.ProjectiveCurve.ProjectiveLine) (n : ℕ),
        projectiveLine_H0_dim p n)
    ∧ (∀ D : Divisor Jacobians.ProjectiveCurve.ProjectiveLine,
        projectiveLine_H1_vanishing D)

end Jacobians.RiemannSurface.Cohomology.SheafCohomologySpec
