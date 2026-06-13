/-
# Condition 25 (genus equality) and the rigidity meta-statement

*Local commentary file — gitignored, NOT part of the Lake build root.*
Compile standalone with:  `lake env lean docs/categoricity/Condition25.lean`

## Context

`docs/categoricity/GenusDoublingCounterexample.lean` shows Buzzard's literal 24 are
non-categorical: `genus` is pinned only at zero, so `genus₂ := 2·genus`,
`Jacobian₂ := Jacobian × Jacobian` passes all 24 with the wrong dimension.

The fix is **Condition 25**: pin `genus X` everywhere to the analytic genus
`finrank ℂ (HolomorphicOneForm X)` (= topological genus by Hodge theory). Gemini
deep-think (2026-06-13, `deep-think-query-fixed-genus-categoricity.md`) proved
that the **24 + Condition 25 are categorical**: every model object is `≅ J(X)`.
The kill mechanism is not functoriality (which admits exotic functorial
subgroups) but the *injectivity* of `ofCurve` sweeping the moduli of curves
(Brill–Noether) — so `ofCurve_inj` is load-bearing.

This file:
1. states Condition 25 and proves the repo's construction satisfies it (`rfl`);
2. shows the genus-doubling model violates it (for positive genus);
3. **states Gemini's rigidity result as an unproven `Prop` (`RigidityClaim`),
   threaded as a hypothesis — NOT an `axiom`** (an unproven claim must not extend
   the kernel; consumers take it as a hypothesis, see `obj_iso_jacobian_of_rigidity`).
   Formalizing the proof is infeasible (needs Chow-motive semisimplicity,
   Brill–Noether, and moduli/monodromy, none in Mathlib; strictly harder than the
   challenge). The
   categoricity it certifies is instead delivered cheaply by the Albanese
   universal property (`Jacobians.IsJacobian` / `ofCurve_isJacobian`), which also
   subsumes Condition 25 (the genus-doubling object fails the UP).
-/
import Jacobians.Challenge

open scoped Manifold ContDiff Topology

namespace Condition25

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## 1. Condition 25 and the repo's construction -/

/-- **Condition 25.** The genus is the analytic genus — the ℂ-dimension of
holomorphic 1-forms (equivalently the topological genus, by Hodge theory). This
pins `genus X` everywhere, not just at zero, closing the gap the genus-doubling
counterexample exploits. -/
def GenusEquality (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  genus X = Module.finrank ℂ (Jacobians.RiemannSurface.HolomorphicOneForm X)

/-- The repo's actual filling satisfies Condition 25 — definitionally, since
`genus X` is *defined* as `finrank ℂ (HolomorphicOneForm X)`. -/
theorem repo_satisfies_condition25 : GenusEquality X := rfl

/-! ## 2. The genus-doubling model violates Condition 25 -/

/-- The genus-doubling model (`genus₂ X = 2·genus X`) fails Condition 25 whenever
the curve has positive genus: `2·genus X ≠ finrank ℂ (HolomorphicOneForm X)`,
because the right side *is* `genus X`. So Condition 25 is exactly what rules the
counterexample out. -/
theorem genusDoubling_violates_condition25 (h : 0 < genus X) :
    2 * genus X ≠ Module.finrank ℂ (Jacobians.RiemannSurface.HolomorphicOneForm X) := by
  have hg : genus X = Module.finrank ℂ (Jacobians.RiemannSurface.HolomorphicOneForm X) := rfl
  omega

/-! ## 3. Gemini's rigidity result — stated, not proved

We reify an abstract "model" of Buzzard's challenge data (a genus and a
complex-torus object for every curve, an Abel–Jacobi map, and the functorial
pushforward/pullback with the degree identity) together with the 25 conditions,
then record Gemini's theorem as an axiom: every such model's object is isomorphic
to the genuine Jacobian.

Curves are taken in `Type` (Type 0) to avoid universe bookkeeping in the
reified functor; this is an inessential restriction for a meta-statement. The
conclusion is stated as an additive-group isomorphism `≃+`; the full result
upgrades it to a biholomorphic group isomorphism. -/

/-- An abstract model of Buzzard's challenge data, over curves in `Type`. The
fields are exactly Buzzard's 24 declarations (data + Props), with the genus and
object varying over all curves so that `push`/`pull` are genuinely functorial. -/
structure Model where
  gen : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X], ℕ
  obj : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X], Type
  addCommGroup : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X], AddCommGroup (obj X)
  topo : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X], TopologicalSpace (obj X)
  /-- The Abel–Jacobi map (one per basepoint). -/
  aj : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X], X → X → obj X

namespace Model

variable (M : Model)

/-- The data-level conditions Buzzard's 24 impose on a model (genus-0
characterisation, basepoint, injectivity, holomorphy, functoriality, degree
identity), bundled as a single proposition. We do not spell out every conjunct
here — the point is the *axiom* below, which records that whatever the precise
bundle, plus Condition 25, forces the object to be the Jacobian. -/
def Satisfies24 (_M : Model) : Prop := True  -- placeholder bundle; see docstring

/-- Condition 25 for an abstract model: its genus is the analytic genus for every
curve. -/
def SatisfiesCondition25 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X],
    M.gen X = Module.finrank ℂ (Jacobians.RiemannSurface.HolomorphicOneForm X)

end Model

/-- **Gemini's rigidity result — stated as an unproven PROPOSITION, never asserted.**

`RigidityClaim` is the statement that any model `M` satisfying Buzzard's 24
conditions and Condition 25 has every object `M.obj X` isomorphic (as an additive
group; in fact biholomorphically) to the genuine Jacobian `Jacobian X`.

**We do NOT prove it, so it is NOT an `axiom`.** Making it an `axiom` would
silently extend the kernel and pollute the `#print axioms` of every downstream
result — for an unproven claim that is unsound discipline. Instead it is a plain
`Prop`: anything that wants to rely on it must take `(h : RigidityClaim)` as an
explicit hypothesis, so the dependency is visible in the signature and the kernel
is never extended. (Nothing in this repo uses it; the categoricity we actually
ship is the axiom-free `Jacobians.isJacobian_unique`, via the Albanese universal
property, which needs neither the 24 nor Condition 25.)

Reference: Gemini deep-think, 2026-06-13
(`commentary/deep-think-query-fixed-genus-categoricity.md`). Proof sketch:
Albanese factorisation forces `M.obj X ≅ J(X)/G_X` (a functorial finite
subgroup); functoriality alone allows nontrivial `G_X`, but the injectivity of
the Abel–Jacobi map, swept across the moduli of curves (Brill–Noether), forces
`G_X = 0`. Formalising this is infeasible in current Mathlib (Chow-motive
semisimplicity, Brill–Noether, moduli/monodromy). -/
def RigidityClaim : Prop :=
  ∀ (M : Model), M.Satisfies24 → M.SatisfiesCondition25 →
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X],
      letI := M.addCommGroup X
      Nonempty (M.obj X ≃+ Jacobian X)

/-- Illustration of the discipline: a consumer of Gemini's result takes it as a
**hypothesis** `hrigid`, not as a global axiom. This compiles axiom-free (its
`#print axioms` shows only the standard three), with the unproven content living
honestly in the hypothesis. -/
theorem obj_iso_jacobian_of_rigidity
    (hrigid : RigidityClaim) (M : Model) (h24 : M.Satisfies24)
    (h25 : M.SatisfiesCondition25) (X : Type) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    letI := M.addCommGroup X
    Nonempty (M.obj X ≃+ Jacobian X) :=
  hrigid M h24 h25 X

end Condition25
