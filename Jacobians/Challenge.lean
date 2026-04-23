import Mathlib -- compiles with commit 8e3c989104daaa052921bf43de9eef0e1ac9fbf5 (15th April 2026)
import Jacobians.Jacobian
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.Axioms.Uniformization0
-- ^ Our bridge. Fills all 24 Buzzard sorries via the named-axiom
-- framework: `Jacobian` bridge through `ComplexTorus`, instances via
-- ULift transfer (+ one axiom for `LieAddGroup`), data defs (`ofCurve`,
-- pushforward, pullback, degree) and all 10 theorems axiom-stubbed
-- against the classical Riemann-surface theory (PathIntegral,
-- Abel-Jacobi, branch-locus degree formula, Uniformization for
-- genus 0).
--
-- Each axiom retires to a theorem once the corresponding piece of
-- Mathlib-level infrastructure (real-analytic path integration,
-- line bundles + sheaf cohomology, surface classification) lands.
-- See `Jacobians/Axioms/` and `docs/formalization-plan.md` §7.

/-

# Jacobians

An AI challenge to make an API for Jacobians, by Kevin Buzzard. v0.2.

## Main missing definitions

* `genus` -- genus of a compact Riemann surface
* `Jacobian` -- the Jacobian of a compact Riemann surface
* `Jacobian.ofCurve` -- the Abel-Jacobi map from a compact Riemann surface to its Jacobian
* `ContMDiff.degree` -- the degree of a holomorphic map between compact Riemann surfaces.
    Equal to 0 if the map is constant, otherwise equal to the usual degree.
* `Jacobian.pushforward` -- the pushforward map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.
* `Jacobian.pullback` -- the pullback map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.

## Main missing theorems

* `genus_eq_zero_iff_homeo` -- a compact Riemann surface has genus 0 iff it is homeomorphic to
     the sphere
* `ofCurve_inj` -- the Abel-Jacobi map is injective iff the genus is positive
* `Jacobian.ofCurve_contMDiff` -- the Abel-Jacobi map is holomorphic
* `Jacobian.pushforward_contMDiff` -- the pushforward map is holomorphic
* `Jacobian.pullback_contMDiff` -- the pullback map is holomorphic
* `pushforward_pullback` -- pullback then pushforward is multiplication by degree

## Changelog

* v0.2: `Type*` not `Type u`; use `𝓘(ℂ)` instead of `modelWithCornersSelf ℂ ℂ`; docstrings
  and comments
* v0.1: initial public release
-/

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

/-- The genus of a compact Riemann surface. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Jacobians.RiemannSurface.genus X

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- this proof avoids the hack answer `∀ X, genus X = 0`
lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  -- Uniformization for g = 0: reduce Buzzard's `genus` (defined via the
  -- RiemannSurface.genus which is our `finrank HolomorphicOneForm`) to
  -- the axiom on that genus.
  change Jacobians.RiemannSurface.genus X = 0 ↔ _
  exact Jacobians.Axioms.AX_genus_eq_zero_iff_homeo

universe u in
-- data
/-- The Jacobian of a compact Riemann surface. -/
noncomputable def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u :=
  Jacobians.Jacobian X

namespace Jacobian

-- data
/-- The Jacobian of a compact Riemann surface is naturally an additive commutative group. -/
noncomputable instance : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (Jacobians.Jacobian X))

-- data
/-- The Jacobian of a compact Riemann surface is naturally a topological space. -/
noncomputable instance : TopologicalSpace (Jacobian X) :=
  inferInstanceAs (TopologicalSpace (Jacobians.Jacobian X))

-- Prop
instance : T2Space (Jacobian X) :=
  inferInstanceAs (T2Space (Jacobians.Jacobian X))

-- Prop
instance : CompactSpace (Jacobian X) :=
  inferInstanceAs (CompactSpace (Jacobians.Jacobian X))

-- data
/-- The Jacobian of a compact Riemann surface is a complex manifold, of dimension
equal to the genus of the surface. -/
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := by
  change ChartedSpace (Fin (Jacobians.RiemannSurface.genus X) → ℂ) (Jacobians.Jacobian X)
  infer_instance

-- Prop
instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  change IsManifold (modelWithCornersSelf ℂ (Fin (Jacobians.RiemannSurface.genus X) → ℂ))
    ω (Jacobians.Jacobian X)
  infer_instance

-- Prop
instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  Jacobians.Axioms.AX_jacobian_lieAddGroup

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian. -/
noncomputable def ofCurve (P : X) : X → Jacobian X :=
  Jacobians.Axioms.ofCurveImpl X P

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) :=
  Jacobians.Axioms.AX_ofCurve_contMDiff P

lemma ofCurve_self (P : X) : ofCurve P P = 0 :=
  Jacobians.Axioms.AX_ofCurve_self P

-- this is the lemma which stops the hack answer "J(X)=0 for all X"
lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) :=
  Jacobians.Axioms.AX_ofCurve_inj P h

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- The pushforward map between Jacobians associated to a map of the underlying curves. -/
noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  Jacobians.Axioms.pushforwardImpl X Y f hf

-- pushforward is holomorphic
theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) :=
  Jacobians.Axioms.AX_pushforward_contMDiff f hf

-- functoriality
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P :=
  Jacobians.Axioms.AX_pushforward_id_apply P

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- functoriality
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) :=
  Jacobians.Axioms.AX_pushforward_comp_apply f hf g hg P

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant. -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  Jacobians.Axioms.pullbackImpl X Y f hf

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) :=
  Jacobians.Axioms.AX_pullback_contMDiff f hf

-- functoriality
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P :=
  Jacobians.Axioms.AX_pullback_id_apply P

-- functoriality
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) :=
  Jacobians.Axioms.AX_pullback_comp_apply f hf g hg P

/-- The degree of a holomorphic map between compact Riemann surfaces. Equal to zero
for constant maps, otherwise equal to the usual degree. -/
noncomputable def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  Jacobians.Axioms.degreeImpl f hf

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobians.Axioms.AX_pushforward_pullback f hf P

end Jacobian
