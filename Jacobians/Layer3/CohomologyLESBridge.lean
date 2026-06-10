/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Layer3.LinearSystemBridge
import KirovDolbeault.Dolbeault.CohomologicalRR
import KirovDolbeault.Dolbeault.SkyscraperProductWitness

/-!
# The cohomology LES bridge: `cohomologyLES` as a theorem

Phase-D bridge file (docs/planning/PHASE_D_BRIDGE_PLAN.md, A4 step (iii);
type alignment in docs/planning/PHASE_D_TYPE_ALIGNMENT.md §3, row
`cohomologyLES`). The former Layer-3 axiom `cohomologyLES` becomes a real
construction here: the six-term divisor-addition long exact sequence

`0 → L(D) → L(D+P) → ℂ_P → H¹(O(D)) → H¹(O(D+P)) → 0`

is obtained from the Kirov Dolbeault port's skyscraper LES
(`Jacobians.Dolbeault.FiniteCover.exists_skyscraperLES`, Forster §16, a
sorry-free theorem) instantiated at the canonical chart-disk cover — whose
local-Mittag-Leffler hypothesis is the proven
`locallyRealizable_chartDiskCover` — and transported through

* the `H⁰` bridge `riemannRochSpaceEquivGlobalSections` and its `f₁`
  naturality square (`Jacobians.Layer3.LinearSystemBridge`, A4 step (ii));
* the definitional identification `H1coh D = cechH1 (equivFinsupp D)`
  (`Jacobians.Layer3.CechH1Bridge`, A4 step (i));
* `ULift.moduleEquiv` for the universe-lifted skyscraper fiber `ℂ_P`;
* the divisor-translation congruence `equivFinsupp (D + ⟨P⟩) =
  equivFinsupp D + single P 1` at the `H⁰` and `H¹` slots.

Exactness is transported field-by-field with
`Function.Exact.of_ladder_linearEquiv_of_exact`; the sequence ends come from
`h0Incl` injectivity (ours: `Submodule.inclusion_injective`) and the port's
`surj₄`. The definitions `ZeroCoh`, `SkyscraperFiber`, `CohomologyLESData`
moved here verbatim from `Jacobians/Layer3/Cohomology.lean` (base-file split
of the Phase-C in-place pattern); all names stay in `Jacobians.Layer3`.

This file consumes only sorry-free port results; the headline declaration is
`#print axioms`-checked to `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace Jacobians.Layer3

/- Name-resolution shim (see `Jacobians/Layer3/CechH1Bridge.lean`). -/
export Jacobians.Axioms (Divisor Divisor.deg)

open Jacobians.RiemannSurface
open Jacobians.Dolbeault

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

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

/-! ### Transport equivalences at the `H¹` slots -/

/-- `H1coh D` is definitionally the port's Čech `H¹` of the chart-disk cover
(A4 step (i)); record the identification as a linear equivalence. -/
def h1cohEquiv (D : Divisor X) :
    H1coh D ≃ₗ[ℂ]
      (chartDiskCover (X := X)).toFiniteCover.cechH1
        (FreeAbelianGroup.equivFinsupp X D) :=
  LinearEquiv.refl ℂ _

/-- Congruence equivalence of Čech `H¹` along an equality of divisors. -/
def cechH1CongrDiv (𝔘 : FiniteCover X) {E₁ E₂ : X →₀ ℤ} (h : E₁ = E₂) :
    𝔘.cechH1 E₁ ≃ₗ[ℂ] 𝔘.cechH1 E₂ := by
  subst h
  exact LinearEquiv.refl ℂ _

/-- The port→ours `H¹` equivalence at `D + P`, with the port side spelled at
`E + Finsupp.single P 1` so it composes with the port's `h1Map`. -/
def h1cohAddPointEquiv (D : Divisor X) (P : X) :
    H1coh (D + FreeAbelianGroup.of P) ≃ₗ[ℂ]
      (chartDiskCover (X := X)).toFiniteCover.cechH1
        (FreeAbelianGroup.equivFinsupp X D + Finsupp.single P 1) :=
  (h1cohEquiv (D + FreeAbelianGroup.of P)).trans
    (cechH1CongrDiv (chartDiskCover (X := X)).toFiniteCover
      (equivFinsupp_add_of D P))

/-! ### The LES construction -/

/-- **The divisor-addition long exact cohomology sequence — now a theorem
(A4 step (iii) headline; formerly the Layer-3 axiom `cohomologyLES`).**

`0 -> L(D) -> L(D+P) -> ℂ_P -> H¹(X,O(D)) -> H¹(X,O(D+P)) -> 0`,

with `L(D) = riemannRochSpace D` and `ℂ_P` represented by `ULift ℂ`.

Construction: destructure the port's skyscraper LES at the chart-disk cover
(`exists_skyscraperLES` + `locallyRealizable_chartDiskCover`, sorry-free) and
transport every map and exactness field through the `H⁰` bridge, the
definitional `H¹` identification, and `ULift.moduleEquiv`.

Reference: Forster, *Lectures on Riemann Surfaces*, §16; this is the long
exact sequence of `0 -> O(D) -> O(D+P) -> ℂ_P -> 0`. -/
def cohomologyLES (D : Divisor X) (P : X) : CohomologyLESData D P :=
  -- the port's skyscraper LES at the canonical chart-disk cover
  let 𝔘 := (chartDiskCover (X := X)).toFiniteCover
  let E := FreeAbelianGroup.equivFinsupp X D
  let S : FiniteCover.SkyscraperLES 𝔘 E P :=
    Classical.choice
      (FiniteCover.exists_skyscraperLES 𝔘 locallyRealizable_chartDiskCover E P)
  -- transport equivalences (port side ≃ our side), slot by slot
  let e₁ : ↥(𝔘.globalSections E) ≃ₗ[ℂ] ↥(riemannRochSpace D) :=
    (riemannRochSpaceEquivGlobalSections D).symm
  let e₂ : ↥(𝔘.globalSections (E + Finsupp.single P 1)) ≃ₗ[ℂ]
      ↥(riemannRochSpace (D + FreeAbelianGroup.of P)) :=
    globalSectionsAddPointEquiv D P
  let e₃ : ℂ ≃ₗ[ℂ] SkyscraperFiber.{u} := ULift.moduleEquiv.symm
  let e₄ : 𝔘.cechH1 E ≃ₗ[ℂ] H1coh D := (h1cohEquiv D).symm
  let e₅ : 𝔘.cechH1 (E + Finsupp.single P 1) ≃ₗ[ℂ]
      H1coh (D + FreeAbelianGroup.of P) := (h1cohAddPointEquiv D P).symm
  -- the three transported maps
  let pp : riemannRochSpace (D + FreeAbelianGroup.of P) →ₗ[ℂ]
      SkyscraperFiber.{u} :=
    e₃.toLinearMap ∘ₗ S.h0ToSky ∘ₗ e₂.symm.toLinearMap
  let conn : SkyscraperFiber.{u} →ₗ[ℂ] H1coh D :=
    e₄.toLinearMap ∘ₗ S.f₃ ∘ₗ e₃.symm.toLinearMap
  let cmap : H1coh D →ₗ[ℂ] H1coh (D + FreeAbelianGroup.of P) :=
    e₅.toLinearMap ∘ₗ 𝔘.h1Map E P ∘ₗ e₄.symm.toLinearMap
  -- ladder squares for the four equivalence-conjugated arrows
  have sq₁ : (riemannRochSpaceAddPointInclusion D P) ∘ₗ (e₁ : _ →ₗ[ℂ] _)
      = (e₂ : _ →ₗ[ℂ] _) ∘ₗ 𝔘.h0Incl E P :=
    riemannRochSpaceEquivGlobalSections_naturality D P
  have sq₂ : pp ∘ₗ (e₂ : _ →ₗ[ℂ] _) = (e₃ : _ →ₗ[ℂ] _) ∘ₗ S.h0ToSky := by
    apply LinearMap.ext
    intro s
    simp only [pp, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have sq₃ : conn ∘ₗ (e₃ : _ →ₗ[ℂ] _) = (e₄ : _ →ₗ[ℂ] _) ∘ₗ S.f₃ := by
    apply LinearMap.ext
    intro c
    simp only [conn, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have sq₄ : cmap ∘ₗ (e₄ : _ →ₗ[ℂ] _) = (e₅ : _ →ₗ[ℂ] _) ∘ₗ 𝔘.h1Map E P := by
    apply LinearMap.ext
    intro c
    simp only [cmap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  { principalPart := pp
    connecting := conn
    cohomologyMap := cmap
    exact_start :=
      (LinearMap.exact_zero_iff_injective _ _).mpr
        (Submodule.inclusion_injective _)
    exact_LD_add :=
      Function.Exact.of_ladder_linearEquiv_of_exact
        (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) sq₁ sq₂ S.exact₁₂
    exact_skyscraper :=
      Function.Exact.of_ladder_linearEquiv_of_exact
        (e₁ := e₂) (e₂ := e₃) (e₃ := e₄) sq₂ sq₃ S.exact₂
    exact_H1 :=
      Function.Exact.of_ladder_linearEquiv_of_exact
        (e₁ := e₃) (e₂ := e₄) (e₃ := e₅) sq₃ sq₄ S.exact₃
    exact_H1_add := by
      rw [LinearMap.exact_zero_iff_surjective]
      simp only [cmap, LinearMap.coe_comp, LinearEquiv.coe_coe]
      exact e₅.surjective.comp (S.surj₄.comp e₄.symm.surjective)
    exact_terminal := by
      rw [LinearMap.exact_zero_iff_surjective]
      intro z
      exact ⟨0, Subsingleton.elim _ _⟩ }

end Jacobians.Layer3
