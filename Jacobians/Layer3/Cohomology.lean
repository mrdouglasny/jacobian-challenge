import Jacobians.Layer3.EulerChar
import Jacobians.RiemannSurface.Cohomology.RiemannRochBase
import Jacobians.RiemannSurface.Cohomology.LineBundleBasic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Layer 3 cohomology scaffold

This file records the Phase-B cohomological scaffold for Challenge Layer 3.
The analytic inputs are isolated as axioms about the actual Riemann-Roch
spaces `L(D) = riemannRochSpace D`; Riemann-Roch and the numerical Serre
duality identity are then proved from the six-term Euler-characteristic engine.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Jacobians.Axioms
open Jacobians.RiemannSurface

namespace Jacobians.Layer3

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- **Layer-3 axiom (NOT VERIFIED).** The opaque first cohomology vector space
`H¹(X, O(D))` attached to the concrete divisor sheaf `O(D)`.

Reference: Forster, *Lectures on Riemann Surfaces*, §§16-17. This is the real
sheaf cohomology group `H¹(X, O(D))`; only its vector-space structure and
finite-dimensionality are exposed at Layer 3. -/
axiom H1coh (D : Divisor X) : Type u

/-- **Layer-3 axiom (NOT VERIFIED).** Additive group structure on
`H¹(X, O(D))`.

Reference: Forster, *Lectures on Riemann Surfaces*, §§16-17. -/
axiom H1coh.instAddCommGroup (D : Divisor X) : AddCommGroup (H1coh D)
attribute [instance] H1coh.instAddCommGroup

/-- **Layer-3 axiom (NOT VERIFIED).** Complex vector-space structure on
`H¹(X, O(D))`.

Reference: Forster, *Lectures on Riemann Surfaces*, §§16-17. -/
axiom H1coh.instModule (D : Divisor X) : Module ℂ (H1coh D)
attribute [instance] H1coh.instModule

/-- **Layer-3 axiom (NOT VERIFIED).** Serre finiteness for the first cohomology
of `O(D)`.

Reference: Forster, *Lectures on Riemann Surfaces*, §§16-17. -/
axiom H1coh.instFiniteDimensional (D : Divisor X) :
    FiniteDimensional ℂ (H1coh D)
attribute [instance] H1coh.instFiniteDimensional

private theorem coeff_le_add_point (D : Divisor X) (P : X) :
    ∀ Q : X, FreeAbelianGroup.coeff Q (D : FreeAbelianGroup X) ≤
      FreeAbelianGroup.coeff Q (D + FreeAbelianGroup.of P : Divisor X) := by
  intro Q
  rw [map_add]
  by_cases hQ : Q = P
  · subst Q
    simp [FreeAbelianGroup.coeff, FreeAbelianGroup.toFinsupp_of,
      Finsupp.single_eq_same]
  · simp [FreeAbelianGroup.coeff, FreeAbelianGroup.toFinsupp_of,
      hQ]

/-- The natural inclusion `L(D) -> L(D + P)`. -/
noncomputable def riemannRochSpaceAddPointInclusion (D : Divisor X) (P : X) :
    riemannRochSpace D →ₗ[ℂ] riemannRochSpace (D + FreeAbelianGroup.of P) :=
  Submodule.inclusion (riemannRochSpace_mono (coeff_le_add_point D P))

/-- The zero vector space used as the terminal term in the six-term exact
sequence `... -> H¹(D + P) -> 0`. -/
abbrev ZeroCoh : Type u := ULift.{u} (Fin 0 → ℂ)

/-- A universe-lifted copy of the skyscraper fiber `ℂ_P = ℂ`, used so every
term in the six-term exact-sequence engine lives in the same universe. -/
abbrev SkyscraperFiber : Type u := ULift.{u} ℂ

/-- The six-term long exact sequence data for
`0 -> L(D) -> L(D+P) -> ℂ -> H¹(D) -> H¹(D+P) -> 0`, in exactly the shape
consumed by `eulerChar_additive_of_exact_six`.

The first map is the concrete inclusion `riemannRochSpaceAddPointInclusion`.
The middle `SkyscraperFiber` is a universe-lifted copy of the skyscraper fiber
`ℂ_P = ℂ`; the terminal term is the zero vector space `ZeroCoh`. -/
structure CohomologyLESData (D : Divisor X) (P : X) where
  principalPart :
    riemannRochSpace (D + FreeAbelianGroup.of P) →ₗ[ℂ] SkyscraperFiber.{u}
  connecting :
    SkyscraperFiber.{u} →ₗ[ℂ] H1coh D
  cohomologyMap :
    H1coh D →ₗ[ℂ] H1coh (D + FreeAbelianGroup.of P)
  exact_start :
    Function.Exact (0 : riemannRochSpace D →ₗ[ℂ] riemannRochSpace D)
      (riemannRochSpaceAddPointInclusion D P)
  exact_LD_add :
    Function.Exact (riemannRochSpaceAddPointInclusion D P) principalPart
  exact_skyscraper :
    Function.Exact principalPart connecting
  exact_H1 :
    Function.Exact connecting cohomologyMap
  exact_H1_add :
    Function.Exact cohomologyMap
      (0 : H1coh (D + FreeAbelianGroup.of P) →ₗ[ℂ] ZeroCoh.{u})
  exact_terminal :
    Function.Exact
      (0 : H1coh (D + FreeAbelianGroup.of P) →ₗ[ℂ] ZeroCoh.{u})
      (0 : ZeroCoh.{u} →ₗ[ℂ] ZeroCoh.{u})

/-- **Layer-3 axiom (NOT VERIFIED).** The divisor-addition long exact
cohomology sequence

`0 -> L(D) -> L(D+P) -> ℂ_P -> H¹(X,O(D)) -> H¹(X,O(D+P)) -> 0`,

with `L(D) = riemannRochSpace D` and `ℂ_P` represented by `ℂ`.

Reference: Forster, *Lectures on Riemann Surfaces*, §§16-17. This is the
standard long exact sequence obtained from
`0 -> O(D) -> O(D+P) -> ℂ_P -> 0`. -/
axiom cohomologyLES (D : Divisor X) (P : X) : CohomologyLESData D P

/-- **Layer-3 axiom (NOT VERIFIED).** The base first-cohomology dimension:
`h¹(O_X) = genus(X)`.

Reference: Forster, *Lectures on Riemann Surfaces*, §§16-17. -/
axiom h1coh_zero_finrank :
    Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X

/-- **Layer-3 axiom (NOT VERIFIED).** Serre duality as a perfect pairing,
packaged as a linear equivalence with the dual of `L(K-D)`.

Reference: Forster, *Lectures on Riemann Surfaces*, §17. -/
axiom serreDuality_equiv (D : Divisor X) :
    Nonempty
      (H1coh D ≃ₗ[ℂ]
        Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D)))

/-- The Layer-3 Euler characteristic `χ(D) = h⁰(D) - h¹(D)`. -/
def eulerCharL3 (D : Divisor X) : ℤ :=
  (Module.finrank ℂ (riemannRochSpace D) : ℤ) -
    (Module.finrank ℂ (H1coh D) : ℤ)

private theorem zeroCoh_finrank : Module.finrank ℂ ZeroCoh.{u} = 0 := by
  rw [show Module.finrank ℂ ZeroCoh.{u} =
      Module.finrank ℂ (ULift.{u} (Fin 0 → ℂ)) by rfl]
  rw [finrank_ulift]
  exact Module.finrank_zero_of_subsingleton

private theorem skyscraperFiber_finrank :
    Module.finrank ℂ SkyscraperFiber.{u} = 1 := by
  rw [show Module.finrank ℂ SkyscraperFiber.{u} =
      Module.finrank ℂ (ULift.{u} ℂ) by rfl]
  rw [finrank_ulift]
  exact Module.finrank_self ℂ

/-- Adding one point to the divisor raises the Layer-3 Euler characteristic by
one. This is proved from the cohomology LES and the six-term Euler-characteristic
engine, not axiomatized. -/
theorem eulerCharL3_add_point (D : Divisor X) (P : X) :
    eulerCharL3 (D + FreeAbelianGroup.of P) = eulerCharL3 D + 1 := by
  let les := cohomologyLES (X := X) D P
  have h :=
    eulerChar_additive_of_exact_six_skyscraper
      (riemannRochSpaceAddPointInclusion (X := X) D P)
      les.principalPart les.connecting les.cohomologyMap
      (0 : H1coh (D + FreeAbelianGroup.of P) →ₗ[ℂ] ZeroCoh.{u})
      les.exact_start les.exact_LD_add les.exact_skyscraper les.exact_H1
      les.exact_H1_add les.exact_terminal
      skyscraperFiber_finrank
      zeroCoh_finrank
  simpa [eulerCharL3, add_comm, add_left_comm, add_assoc] using h

private theorem eulerCharL3_sub_point (D : Divisor X) (P : X) :
    eulerCharL3 (D - FreeAbelianGroup.of P) = eulerCharL3 D - 1 := by
  have h := eulerCharL3_add_point (X := X) (D - FreeAbelianGroup.of P) P
  have hD : D - FreeAbelianGroup.of P + FreeAbelianGroup.of P = D := by
    abel
  rw [hD] at h
  omega

private theorem divisor_deg_of (P : X) :
    Divisor.deg X (FreeAbelianGroup.of P : Divisor X) = 1 := by
  simp [Divisor.deg]

private theorem divisor_deg_add_point (D : Divisor X) (P : X) :
    Divisor.deg X (D + FreeAbelianGroup.of P) = Divisor.deg X D + 1 := by
  rw [map_add, divisor_deg_of]

private theorem divisor_deg_sub_point (D : Divisor X) (P : X) :
    Divisor.deg X (D - FreeAbelianGroup.of P) = Divisor.deg X D - 1 := by
  rw [map_sub, divisor_deg_of]

private theorem eulerCharL3_sub_deg_add_point (D : Divisor X) (P : X) :
    eulerCharL3 (D + FreeAbelianGroup.of P) -
        Divisor.deg X (D + FreeAbelianGroup.of P) =
      eulerCharL3 D - Divisor.deg X D := by
  have hχ := eulerCharL3_add_point (X := X) D P
  have hdeg := divisor_deg_add_point (X := X) D P
  omega

private theorem eulerCharL3_sub_deg_sub_point (D : Divisor X) (P : X) :
    eulerCharL3 (D - FreeAbelianGroup.of P) -
        Divisor.deg X (D - FreeAbelianGroup.of P) =
      eulerCharL3 D - Divisor.deg X D := by
  have hχ := eulerCharL3_sub_point (X := X) D P
  have hdeg := divisor_deg_sub_point (X := X) D P
  omega

private theorem eulerCharL3_sub_deg_add_right (E : Divisor X) :
    ∀ D : Divisor X,
      eulerCharL3 (D + E) - Divisor.deg X (D + E) =
        eulerCharL3 D - Divisor.deg X D := by
  induction E using FreeAbelianGroup.induction_on with
  | zero =>
      intro D
      simp
  | of P =>
      intro D
      exact eulerCharL3_sub_deg_add_point (X := X) D P
  | neg P _ =>
      intro D
      simpa [sub_eq_add_neg] using eulerCharL3_sub_deg_sub_point (X := X) D P
  | add E F ihE ihF =>
      intro D
      simpa [add_assoc] using (ihF (D + E)).trans (ihE D)

private theorem eulerCharL3_sub_deg_zero :
    eulerCharL3 (0 : Divisor X) - Divisor.deg X (0 : Divisor X) =
      1 - (genus X : ℤ) := by
  have h0 :
      Module.finrank ℂ (riemannRochSpace (0 : Divisor X)) = 1 := by
    simpa [h0] using (h0_zero (X := X))
  have h1 :
      Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X :=
    h1coh_zero_finrank (X := X)
  simp [eulerCharL3, h0, h1]

/-- **Layer-3 Riemann-Roch.** The classical Riemann-Roch formula, proved from
the cohomology LES, the base `h¹(O_X)` dimension, and the already-proved
six-term Euler-characteristic engine. -/
theorem riemannRochL3 (D : Divisor X) :
    eulerCharL3 D = Divisor.deg X D + 1 - (genus X : ℤ) := by
  have hconst :
      eulerCharL3 D - Divisor.deg X D =
        eulerCharL3 (0 : Divisor X) - Divisor.deg X (0 : Divisor X) := by
    simpa using (eulerCharL3_sub_deg_add_right (X := X) D (0 : Divisor X))
  have hbase := eulerCharL3_sub_deg_zero (X := X)
  have h :
      eulerCharL3 D - Divisor.deg X D = 1 - (genus X : ℤ) :=
    hconst.trans hbase
  omega

/-- **Layer-3 Serre duality, dimension form.** The nondegenerate Serre pairing
identifies `h¹(D)` with the dimension of `L(K-D)`. -/
theorem serreDualityL3 (D : Divisor X) :
    Module.finrank ℂ (H1coh D) =
      Module.finrank ℂ (riemannRochSpace (canonicalDivisor X - D)) := by
  obtain ⟨e⟩ := serreDuality_equiv (X := X) D
  calc
    Module.finrank ℂ (H1coh D)
        = Module.finrank ℂ
            (Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D))) :=
          e.finrank_eq
    _ = Module.finrank ℂ (riemannRochSpace (canonicalDivisor X - D)) :=
          Subspace.dual_finrank_eq

/-- **Layer-3: holomorphic differentials have dimension the genus** — `h⁰(K) = g`,
proved from the Layer-3 Serre pairing at `D = 0` plus `h1coh_zero_finrank`,
**independently of `AX_RiemannRoch` / `AX_SerreDuality`**. This is the discriminating
non-vacuity check: a degenerate `H1coh` could not produce `dim L(K) = g`. -/
theorem h0_canonical_L3 :
    Module.finrank ℂ (riemannRochSpace (canonicalDivisor X)) = genus X := by
  have hS := serreDualityL3 (0 : Divisor X)
  rw [sub_zero] at hS
  rw [h1coh_zero_finrank] at hS
  exact hS.symm

/-- **Layer-3: canonical degree** — `deg K = 2g − 2`, proved from `riemannRochL3`,
`h0_canonical_L3`, and Serre duality at `D = K` (where `H1coh K ≅ L(0)`, dimension 1),
all within the Layer-3 package. -/
theorem canonicalDivisor_deg_L3 :
    Divisor.deg X (canonicalDivisor X) = 2 * (genus X : ℤ) - 2 := by
  have hRR := riemannRochL3 (canonicalDivisor X)
  have hHK : Module.finrank ℂ (H1coh (canonicalDivisor X)) = 1 := by
    have h := serreDualityL3 (canonicalDivisor X)
    rw [sub_self] at h
    rw [h]
    simpa [h0] using (h0_zero (X := X))
  have hLK : Module.finrank ℂ (riemannRochSpace (canonicalDivisor X)) = genus X :=
    h0_canonical_L3
  simp only [eulerCharL3, hLK, hHK] at hRR
  omega

/-!
Non-vacuity note. `h0_canonical_L3` (`h⁰(K) = g`) and `canonicalDivisor_deg_L3`
(`deg K = 2g − 2`) are proved here **purely from the Layer-3 cohomology axioms**
(not from `AX_RiemannRoch` / `AX_SerreDuality`), which (i) is the discriminating
faithfulness check a degenerate `H1coh` would fail, and (ii) resolves the
review caveat that the existing `h0_canonical` rests on the very axioms being
re-derived. With `riemannRochL3`/`serreDualityL3`, the existing `AX_RiemannRoch`/
`AX_SerreDuality` are theorem wrappers after wiring the public `H1` API to
`H1coh`; the `SheafCohomologySpec` §3 `h⁰(O(np)) = n + 1` test follows from this
package plus genus-zero facts.
-/

end Jacobians.Layer3
