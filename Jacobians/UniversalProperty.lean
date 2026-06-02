import Mathlib -- compiles with Mathlib v4.30.0

/-!
# The Jacobian / Albanese universal property

Buzzard's Jacobian Challenge (`Jacobians/Challenge.lean`) pins the Jacobian
*operationally* — via functoriality of `pushforward`/`pullback`, the degree
identity `pushforward f ∘ pullback f = deg f • id`, Abel injectivity
(`ofCurve_inj`), and the genus-0 homeomorphism — but it never states the
*categorical* universal property that characterizes `(Jacobian X, ofCurve x₀)`
up to unique isomorphism. This file supplies that pin.

`IsJacobian x₀ J aj` says: `aj : X → J` is a holomorphic map from the pointed
compact connected Riemann surface `(X, x₀)` into a complex torus `J`, sending
`x₀ ↦ 0`, and *universal* among such maps — every pointed holomorphic map
`f : X → A` to a complex torus factors **uniquely** through `aj` by a holomorphic
group homomorphism. This is the Albanese universal property specialized to a
curve (where Albanese = Jacobian).

## Main definitions

* `Jacobians.IsJacobian` — the universal property, as a `Prop`-valued structure.

## Design notes

* A *complex torus* is encoded as a **compact connected complex Lie group**
  (`CompactSpace`, `ConnectedSpace`, `ChartedSpace ℂ`, `IsManifold 𝓘(ℂ) ω`,
  `AddGroup`, `LieAddGroup 𝓘(ℂ) ω`). Commutativity is **not** assumed: a compact
  connected complex Lie group is automatically abelian, so `AddGroup` suffices.
* Uniqueness is stated as `∃!` over bundled homomorphisms `J →+ A` together with
  a holomorphicity conjunct; `AddMonoidHom` extensionality plus the fact that
  `aj '' X` topologically generates `J` make this the morphism-level uniqueness
  that yields a *biholomorphic group isomorphism* between any two instances
  (categoricity).
* Basepoint discipline: `f x₀ = 0` is a hypothesis on the test map and
  `φ 0 = 0` is free from `AddMonoidHom`, so the factorization is automatically
  pointed.

The open goal `IsJacobian x₀ (Jacobian X) (ofCurve x₀)` — that Buzzard's concrete
`Jacobian`/`ofCurve` satisfy this property — is the categoricity theorem that
would close the def-degeneracy gap categorically; it is not proved here.

## Vetting

Statement vetted **2026-06-02** (cross-model, per the project axiom/statement
protocol): **Gemini** (gemini-3-pro-preview) — *Sound*: correct categorical UP,
categoricity holds, genus-0 boundary correct (`J = {0}` is the right answer by
Liouville), basepoint handling correct; flagged `AddCommGroup` as redundant →
relaxed to `AddGroup`. **Codex** — flagged the missing Hausdorff hypothesis on the
curve and the target tori; `[T2Space]` added to `X`, `J`, `A` to match Buzzard's
API and exclude non-Hausdorff pathologies from the universally-quantified target.

## References

* Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 1 & 11
  (the Albanese / universal property).
* Arbarello–Cornalba–Griffiths–Harris, *Geometry of Algebraic Curves I*,
  Ch. I (the Jacobian of a curve and Abel–Jacobi).
-/

open scoped Manifold ContDiff Topology

namespace Jacobians

/-- **The Jacobian / Albanese universal property.**

`IsJacobian x₀ J aj` holds when `aj : X → J` is a holomorphic map from the
pointed compact connected Riemann surface `(X, x₀)` to a complex torus `J`
(compact connected complex Lie group) with `aj x₀ = 0`, *universal* among such:
every pointed holomorphic map `f : X → A` to a complex torus factors uniquely
through `aj` by a holomorphic group homomorphism. This characterizes
`(J, aj)` up to unique isomorphism. -/
structure IsJacobian
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (J : Type*) [TopologicalSpace J] [T2Space J] [CompactSpace J] [ConnectedSpace J]
    [ChartedSpace ℂ J] [AddGroup J] [IsManifold 𝓘(ℂ) ω J] [LieAddGroup 𝓘(ℂ) ω J]
    (aj : X → J) : Prop where
  /-- The Abel–Jacobi map is holomorphic. -/
  aj_holo : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω aj
  /-- It sends the basepoint to the identity of the torus. -/
  aj_base : aj x₀ = 0
  /-- Universal property: every pointed holomorphic map `f : X → A` to a complex
  torus factors uniquely through `aj` by a holomorphic group homomorphism. -/
  universal :
    ∀ {A : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
      [ChartedSpace ℂ A] [AddGroup A] [IsManifold 𝓘(ℂ) ω A] [LieAddGroup 𝓘(ℂ) ω A]
      (f : X → A), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → f x₀ = 0 →
      ∃! φ : J →+ A, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (φ : J → A) ∧ ∀ x, f x = φ (aj x)

end Jacobians
