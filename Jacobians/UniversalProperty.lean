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

* A *complex torus* of complex dimension `n` is encoded as a **compact connected
  complex Lie group modeled on `Fin n → ℂ`** (`CompactSpace`, `ConnectedSpace`,
  `ChartedSpace (Fin n → ℂ)`, `IsManifold 𝓘(ℂ, Fin n → ℂ) ω`, `AddGroup`,
  `LieAddGroup 𝓘(ℂ, Fin n → ℂ) ω`). The Jacobian `J` has dimension `g` (its genus);
  the universal property quantifies over targets `A` of **any** dimension `m`. The
  curve `X` itself is a 1-dimensional manifold, modeled on `ℂ` (`𝓘(ℂ)`).
  Commutativity is **not** assumed: a compact connected complex Lie group is
  automatically abelian, so `AddGroup` suffices.
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
would close the def-degeneracy gap categorically; it is not proved here. The proof
plan (lemma DAG, vetted-axiom leaves, effort) is in
`docs/universal-property-proof-plan.md`. One prerequisite instance is still missing
for the goal to typecheck: `ConnectedSpace (Jacobian X)` (true — a torus is
connected — but not provided by Buzzard's API).

## Vetting

Statement vetted **2026-06-02** (cross-model, per the project axiom/statement
protocol): **Gemini** (gemini-3-pro-preview) — *Sound*: correct categorical UP,
categoricity holds, genus-0 boundary correct (`J = {0}` is the right answer by
Liouville), basepoint handling correct; flagged `AddCommGroup` as redundant →
relaxed to `AddGroup`; `[T2Space]` added to `X`, `J`, `A` (a complex torus is
Hausdorff; matches Buzzard's API). **Codex** — flagged that the original statement
modeled `J` and the target on `ChartedSpace ℂ` (1-dimensional), so it only
typechecked for genus-1 Jacobians; **fixed** by parametrizing the model spaces as
`Fin g → ℂ` (for `J`) and `Fin m → ℂ` (for targets `A`), so it now applies to the
genus-`g` Jacobian for all `g`.

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
    {g : ℕ} (J : Type*) [TopologicalSpace J] [T2Space J] [CompactSpace J] [ConnectedSpace J]
    [ChartedSpace (Fin g → ℂ) J] [AddGroup J]
    [IsManifold 𝓘(ℂ, Fin g → ℂ) ω J] [LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω J]
    (aj : X → J) : Prop where
  /-- The Abel–Jacobi map is holomorphic. -/
  aj_holo : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin g → ℂ) ω aj
  /-- It sends the basepoint to the identity of the torus. -/
  aj_base : aj x₀ = 0
  /-- Universal property: every pointed holomorphic map `f : X → A` to a complex
  torus (of any dimension `m`) factors uniquely through `aj` by a holomorphic
  group homomorphism. -/
  universal :
    ∀ {m : ℕ} {A : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
      [ChartedSpace (Fin m → ℂ) A] [AddGroup A]
      [IsManifold 𝓘(ℂ, Fin m → ℂ) ω A] [LieAddGroup 𝓘(ℂ, Fin m → ℂ) ω A]
      (f : X → A), ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin m → ℂ) ω f → f x₀ = 0 →
      ∃! φ : J →+ A, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (φ : J → A) ∧
        ∀ x, f x = φ (aj x)

end Jacobians
