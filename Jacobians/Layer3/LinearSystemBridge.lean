/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Layer3.CechH1Bridge
import Jacobians.RiemannSurface.Cohomology.RiemannRochFinite
import KirovDolbeault.Dolbeault.CechH0

/-!
# The `L(D)` bridge: `riemannRochSpace D` ↔ the port's linear system and Čech `H⁰`

Phase-D bridge file (docs/planning/PHASE_D_BRIDGE_PLAN.md, A4 step (ii);
type alignment in docs/planning/PHASE_D_TYPE_ALIGNMENT.md §3, row
`cohomologyLES`, item (a)). It identifies our Riemann-Roch space

* `riemannRochSpace D ⊆ MeroField X` — quotient-then-submodule, orders via
  `extChartAt 𝓘(ℂ) p`, divisor `FreeAbelianGroup X` —

with the Kirov Dolbeault port's linear system

* `linearSystem E ⧸ germZeroSubmodule` — submodule-then-quotient, orders via
  `chartAt ℂ p`, divisor `X →₀ ℤ`, `E = FreeAbelianGroup.equivFinsupp X D` —

and composes with the port's `globalSectionsEquivQuot` to land on the Čech
`H⁰` of the canonical chart-disk cover. The three dossier sub-steps are:

1. order-definition alignment: `extChartAt 𝓘(ℂ) p = chartAt ℂ p` as functions
   (`orderAt_eq_chartAt`, Wallace), so `orderAt p f = orderW ⟨f, _⟩ p`;
2. junk-kernel match: our `GermZero` and the port's `germZeroSubmodule` are
   both "order `⊤` everywhere" (`ker_linearSystemToRiemannRoch`);
3. the subquotient shuffle: first isomorphism theorem on the germ-class map
   `linearSystemToRiemannRoch` (`linearSystemQuotEquivRiemannRoch`).

Main declarations:

* `riemannRochSpaceEquivGlobalSections D` :
  `L(D) ≃ₗ[ℂ] H⁰(chartDiskCover, 𝒪_E)` — the H⁰ bridge;
* `riemannRochSpaceEquivGlobalSections_naturality` : the `f₁` naturality
  square intertwining our `L(D) ↪ L(D+P)` inclusion with the port's `h0Incl`.

This file consumes only sorry-free port results; the headline declarations
are `#print axioms`-checked to `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace Jacobians.Layer3

/- Name-resolution shim (see `Jacobians/Layer3/CechH1Bridge.lean`): pin the
bare names `Divisor`/`Divisor.deg` in this namespace to our
`FreeAbelianGroup` divisor layer, against the port's `Jacobians.Divisor`. -/
export Jacobians.Axioms (Divisor Divisor.deg)

open Jacobians.RiemannSurface
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
open Jacobians.Dolbeault

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-! ### Divisor dictionary: `FreeAbelianGroup.coeff` vs `Finsupp` evaluation -/

/-- Our divisor coefficient is `Finsupp` evaluation after the translation
`FreeAbelianGroup.equivFinsupp` (both are `toFinsupp` evaluation). -/
theorem coeff_eq_equivFinsupp (D : Divisor X) (p : X) :
    FreeAbelianGroup.coeff p (D : FreeAbelianGroup X) =
      FreeAbelianGroup.equivFinsupp X D p := rfl

/-- The divisor translation sends `D + ⟨P⟩` to `E + Finsupp.single P 1`. -/
theorem equivFinsupp_add_of (D : Divisor X) (P : X) :
    FreeAbelianGroup.equivFinsupp X (D + FreeAbelianGroup.of P) =
      FreeAbelianGroup.equivFinsupp X D + Finsupp.single P 1 := by
  rw [map_add]
  congr 1
  simp [FreeAbelianGroup.equivFinsupp_apply]

/-- Adding a point only increases divisor coefficients (moved here from
`Jacobians/Layer3/Cohomology.lean`; needed by the naturality square). -/
theorem coeff_le_add_point (D : Divisor X) (P : X) :
    ∀ Q : X, FreeAbelianGroup.coeff Q (D : FreeAbelianGroup X) ≤
      FreeAbelianGroup.coeff Q (D + FreeAbelianGroup.of P : Divisor X) := by
  intro Q
  rw [map_add]
  by_cases hQ : Q = P
  · subst Q
    simp [FreeAbelianGroup.coeff, FreeAbelianGroup.toFinsupp_of,
      Finsupp.single_eq_same]
  · simp [FreeAbelianGroup.coeff, FreeAbelianGroup.toFinsupp_of, hQ]

/-- The natural inclusion `L(D) → L(D + P)` (moved here from
`Jacobians/Layer3/Cohomology.lean`; the `f₁` of the cohomology LES). -/
noncomputable def riemannRochSpaceAddPointInclusion (D : Divisor X) (P : X) :
    riemannRochSpace D →ₗ[ℂ] riemannRochSpace (D + FreeAbelianGroup.of P) :=
  Submodule.inclusion (riemannRochSpace_mono (coeff_le_add_point D P))

/-! ### Meromorphy and order dictionary: `extChartAt` vs `chartAt` -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ⊤ X] in
/-- Wallace's `extChartAt`-phrased meromorphy coincides with the port's
`chartAt`-phrased one (the two charts are equal as functions on the trivial
model `𝓘(ℂ)`). -/
theorem meromorphicAtX_iff_chartAt (f : X → ℂ) (p : X) :
    MeromorphicAtX f p ↔
      MeromorphicAt (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  unfold MeromorphicAtX
  rw [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ⊤ X] in
/-- Wallace's `extChartAt`-phrased vanishing order equals the port's
`chartAt`-phrased `orderW`. -/
theorem orderW_mk_eq_orderAt (g : X → ℂ) (hg : Jacobians.IsMeromorphic X g)
    (x : X) :
    Jacobians.MeromorphicFunction.orderW ⟨g, hg⟩ x = orderAt x g := by
  rw [orderAt_eq_chartAt]
  rfl

/-- Normalized membership in the port's linear system (cast-stable form). -/
theorem mem_linearSystem_iff (E : X →₀ ℤ) (F : Jacobians.MeromorphicFunction X) :
    F ∈ Jacobians.linearSystem (X := X) E ↔
      ∀ x : X, ((-(E x) : ℤ) : WithTop ℤ) ≤ F.orderW x := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · exact_mod_cast h x
  · exact_mod_cast h x

/-- Order-bound weakening along the divisor translation: a member of the
port's `L(E)` is a member of `L(E + P)` written at the translated divisor. -/
theorem mem_linearSystem_add_of {D : Divisor X} {P : X}
    {F : Jacobians.MeromorphicFunction X}
    (hF : F ∈ Jacobians.linearSystem (X := X) (FreeAbelianGroup.equivFinsupp X D)) :
    F ∈ Jacobians.linearSystem (X := X)
        (FreeAbelianGroup.equivFinsupp X (D + FreeAbelianGroup.of P)) := by
  rw [mem_linearSystem_iff] at hF ⊢
  intro x
  refine le_trans ?_ (hF x)
  rw [← coeff_eq_equivFinsupp, ← coeff_eq_equivFinsupp]
  exact_mod_cast neg_le_neg (coeff_le_add_point D P x)

/-! ### The germ-class map from the port's meromorphic functions -/

/-- View a port meromorphic function as an element of our raw
meromorphic-function submodule `MeroFunctions X`. -/
def toMeroFunctions (F : Jacobians.MeromorphicFunction X) : MeroFunctions X :=
  ⟨F.toFun, fun p => (meromorphicAtX_iff_chartAt F.toFun p).mpr (F.meromorphic p)⟩

@[simp] theorem toMeroFunctions_coe (F : Jacobians.MeromorphicFunction X) :
    (toMeroFunctions F : X → ℂ) = F.toFun := rfl

/-- Wallace order of the wrapped function equals the port's `orderW`. -/
theorem orderAt_toMeroFunctions (F : Jacobians.MeromorphicFunction X) (p : X) :
    orderAt p (toMeroFunctions F : X → ℂ) = F.orderW p := by
  rw [toMeroFunctions_coe, ← orderW_mk_eq_orderAt F.toFun F.meromorphic]

/-- The `ℂ`-linear map sending a port meromorphic function to its germ class
in our `MeroField X`. -/
def meroFieldOfPort : Jacobians.MeromorphicFunction X →ₗ[ℂ] MeroField X where
  toFun F := Submodule.Quotient.mk (toMeroFunctions F)
  map_add' F G := by
    have h : toMeroFunctions (F + G) = toMeroFunctions F + toMeroFunctions G :=
      Subtype.ext rfl
    rw [h, Submodule.Quotient.mk_add]
  map_smul' c F := by
    have h : toMeroFunctions (c • F) = c • toMeroFunctions F := Subtype.ext rfl
    rw [h, Submodule.Quotient.mk_smul, RingHom.id_apply]

@[simp] theorem meroFieldOfPort_apply (F : Jacobians.MeromorphicFunction X) :
    meroFieldOfPort (X := X) F = Submodule.Quotient.mk (toMeroFunctions F) := rfl

theorem orderAtField_meroFieldOfPort (F : Jacobians.MeromorphicFunction X)
    (p : X) :
    orderAtField p (meroFieldOfPort (X := X) F) = F.orderW p := by
  rw [meroFieldOfPort_apply, orderAtField_mk, orderAt_toMeroFunctions]

/-! ### The bridge map `L_port(E) → L(D)` and its first-isomorphism data -/

/-- The bridge map: wrap a port `L(E)`-member (`E = equivFinsupp D`) and take
its germ class; the order bound transfers along the two dictionaries. -/
def linearSystemToRiemannRoch (D : Divisor X) :
    ↥(Jacobians.linearSystem (X := X) (FreeAbelianGroup.equivFinsupp X D))
      →ₗ[ℂ] ↥(riemannRochSpace D) :=
  ((meroFieldOfPort (X := X)).domRestrict
      (Jacobians.linearSystem (FreeAbelianGroup.equivFinsupp X D))).codRestrict
    (riemannRochSpace D) fun F => by
      intro p
      rw [LinearMap.domRestrict_apply, orderAtField_meroFieldOfPort,
        coeff_eq_equivFinsupp]
      exact F.2 p

@[simp] theorem linearSystemToRiemannRoch_coe (D : Divisor X)
    (F : ↥(Jacobians.linearSystem (X := X) (FreeAbelianGroup.equivFinsupp X D))) :
    (linearSystemToRiemannRoch (X := X) D F : MeroField X)
      = Submodule.Quotient.mk
          (toMeroFunctions (F : Jacobians.MeromorphicFunction X)) := rfl

/-- Surjectivity: every germ class in `L(D)` lifts to a port `L(E)`-member
(choose any raw representative; its orders are the class's orders). -/
theorem linearSystemToRiemannRoch_surjective (D : Divisor X) :
    Function.Surjective (linearSystemToRiemannRoch (X := X) D) := by
  rintro ⟨G, hG⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (GermZero X) G
  refine ⟨⟨⟨(f : X → ℂ), fun x => (meromorphicAtX_iff_chartAt _ x).mp (f.2 x)⟩, ?_⟩, ?_⟩
  · rw [mem_linearSystem_iff]
    intro x
    rw [← coeff_eq_equivFinsupp, orderW_mk_eq_orderAt]
    have hx := hG x
    rw [orderAtField_mk] at hx
    exact_mod_cast hx
  · apply Subtype.ext
    rw [linearSystemToRiemannRoch_coe]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- Kernel match: the bridge map kills exactly the port's germ-zero junk. -/
theorem ker_linearSystemToRiemannRoch (D : Divisor X) :
    LinearMap.ker (linearSystemToRiemannRoch (X := X) D)
      = (Jacobians.germZeroSubmodule (X := X)).submoduleOf
          (Jacobians.linearSystem (FreeAbelianGroup.equivFinsupp X D)) := by
  ext F
  rw [LinearMap.mem_ker, Submodule.submoduleOf, Submodule.mem_comap,
    Submodule.subtype_apply]
  constructor
  · intro hF
    have h0 : (linearSystemToRiemannRoch (X := X) D F : MeroField X) = 0 := by
      rw [hF]; rfl
    rw [linearSystemToRiemannRoch_coe, Submodule.Quotient.mk_eq_zero] at h0
    intro p
    have hp := h0 p
    rwa [orderAt_toMeroFunctions] at hp
  · intro hF
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, linearSystemToRiemannRoch_coe,
      Submodule.Quotient.mk_eq_zero]
    intro p
    rw [orderAt_toMeroFunctions]
    exact hF p

/-- **The subquotient shuffle**: the port's junk-quotiented linear system is
our Riemann-Roch space (first isomorphism theorem on the bridge map). -/
def linearSystemQuotEquivRiemannRoch (D : Divisor X) :
    (↥(Jacobians.linearSystem (X := X) (FreeAbelianGroup.equivFinsupp X D)) ⧸
        (Jacobians.germZeroSubmodule (X := X)).submoduleOf
          (Jacobians.linearSystem (FreeAbelianGroup.equivFinsupp X D)))
      ≃ₗ[ℂ] ↥(riemannRochSpace D) :=
  (Submodule.quotEquivOfEq _ _ (ker_linearSystemToRiemannRoch D).symm).trans
    ((linearSystemToRiemannRoch (X := X) D).quotKerEquivOfSurjective
      (linearSystemToRiemannRoch_surjective D))

theorem linearSystemQuotEquivRiemannRoch_mk (D : Divisor X)
    (F : ↥(Jacobians.linearSystem (X := X) (FreeAbelianGroup.equivFinsupp X D))) :
    linearSystemQuotEquivRiemannRoch D (Submodule.Quotient.mk F)
      = linearSystemToRiemannRoch (X := X) D F := by
  rw [linearSystemQuotEquivRiemannRoch, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-! ### Composition with the port's Čech `H⁰` identification -/

/-- Forward-action lemma for the port's `globalSectionsEquivQuot`: on the
class of `F` it is the restriction cochain of `F`. -/
theorem globalSectionsEquivQuot_mk (𝔘 : FiniteCover X) (E : X →₀ ℤ)
    (F : ↥(Jacobians.linearSystem (X := X) E)) :
    𝔘.globalSectionsEquivQuot E (Submodule.Quotient.mk F)
      = 𝔘.cechRestrictL E F := by
  rw [FiniteCover.globalSectionsEquivQuot, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- **The `H⁰` bridge** (A4 step (ii) headline): our Riemann-Roch space
`L(D)` is `ℂ`-linearly the Čech `H⁰(𝔘, 𝒪_E)` of the canonical chart-disk
cover, `E = equivFinsupp D`. Composition of the subquotient shuffle with the
port's `globalSectionsEquivQuot` (restriction + gluing). -/
def riemannRochSpaceEquivGlobalSections (D : Divisor X) :
    ↥(riemannRochSpace D) ≃ₗ[ℂ]
      ↥((chartDiskCover (X := X)).toFiniteCover.globalSections
          (FreeAbelianGroup.equivFinsupp X D)) :=
  (linearSystemQuotEquivRiemannRoch D).symm.trans
    ((chartDiskCover (X := X)).toFiniteCover.globalSectionsEquivQuot _)

/-- Inverse-action lemma for the `H⁰` bridge: the restriction cochain of `F`
pulls back to the germ class of `F`. -/
theorem riemannRochSpaceEquivGlobalSections_symm_cechRestrictL (D : Divisor X)
    (F : ↥(Jacobians.linearSystem (X := X) (FreeAbelianGroup.equivFinsupp X D))) :
    (riemannRochSpaceEquivGlobalSections D).symm
        ((chartDiskCover (X := X)).toFiniteCover.cechRestrictL _ F)
      = linearSystemToRiemannRoch (X := X) D F := by
  have hq : ((chartDiskCover (X := X)).toFiniteCover.globalSectionsEquivQuot
        (FreeAbelianGroup.equivFinsupp X D)).symm
        ((chartDiskCover (X := X)).toFiniteCover.cechRestrictL _ F)
      = Submodule.Quotient.mk F := by
    rw [LinearEquiv.symm_apply_eq, globalSectionsEquivQuot_mk]
  rw [riemannRochSpaceEquivGlobalSections, LinearEquiv.symm_trans_apply, hq,
    LinearEquiv.symm_symm, linearSystemQuotEquivRiemannRoch_mk]

/-! ### The `f₁` naturality square -/

/-- The two divisor spellings of the point-augmented global sections agree. -/
theorem globalSections_add_point_eq (D : Divisor X) (P : X) :
    (chartDiskCover (X := X)).toFiniteCover.globalSections
        (FreeAbelianGroup.equivFinsupp X D + Finsupp.single P 1)
      = (chartDiskCover (X := X)).toFiniteCover.globalSections
          (FreeAbelianGroup.equivFinsupp X (D + FreeAbelianGroup.of P)) := by
  rw [equivFinsupp_add_of]

/-- The port→ours `H⁰` equivalence at `D + P`, with domain spelled at
`E + Finsupp.single P 1` so it composes with the port's `h0Incl`. -/
def globalSectionsAddPointEquiv (D : Divisor X) (P : X) :
    ↥((chartDiskCover (X := X)).toFiniteCover.globalSections
        (FreeAbelianGroup.equivFinsupp X D + Finsupp.single P 1))
      ≃ₗ[ℂ] ↥(riemannRochSpace (D + FreeAbelianGroup.of P)) :=
  (LinearEquiv.ofEq _ _ (globalSections_add_point_eq D P)).trans
    (riemannRochSpaceEquivGlobalSections (D + FreeAbelianGroup.of P)).symm

/-- **`f₁` naturality square** (dossier item (b)): the `H⁰` bridge
intertwines our order-weakening inclusion `L(D) ↪ L(D+P)` with the port's
`h0Incl`. Both maps are the identity on underlying functions/cochains. -/
theorem riemannRochSpaceEquivGlobalSections_naturality (D : Divisor X) (P : X) :
    (riemannRochSpaceAddPointInclusion D P) ∘ₗ
        ((riemannRochSpaceEquivGlobalSections D).symm :
          _ →ₗ[ℂ] ↥(riemannRochSpace D))
      = ((globalSectionsAddPointEquiv D P : _ →ₗ[ℂ] _) ∘ₗ
          (chartDiskCover (X := X)).toFiniteCover.h0Incl
            (FreeAbelianGroup.equivFinsupp X D) P) := by
  apply LinearMap.ext
  intro s
  obtain ⟨F, rfl⟩ :=
    (chartDiskCover (X := X)).toFiniteCover.cechRestrictL_surjective
      (FreeAbelianGroup.equivFinsupp X D) s
  -- the port-side image of `F` under the order weakening
  set F' : ↥(Jacobians.linearSystem (X := X)
      (FreeAbelianGroup.equivFinsupp X (D + FreeAbelianGroup.of P))) :=
    ⟨(F : Jacobians.MeromorphicFunction X), mem_linearSystem_add_of F.2⟩ with hF'
  have hofeq :
      (LinearEquiv.ofEq _ _ (globalSections_add_point_eq D P))
          ((chartDiskCover (X := X)).toFiniteCover.h0Incl
            (FreeAbelianGroup.equivFinsupp X D) P
            ((chartDiskCover (X := X)).toFiniteCover.cechRestrictL _ F))
        = (chartDiskCover (X := X)).toFiniteCover.cechRestrictL _ F' := by
    apply Subtype.ext
    rw [LinearEquiv.coe_ofEq_apply, FiniteCover.h0Incl, Submodule.coe_inclusion,
      FiniteCover.cechRestrictL_coe, FiniteCover.cechRestrictL_coe]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    globalSectionsAddPointEquiv, LinearEquiv.trans_apply]
  rw [riemannRochSpaceEquivGlobalSections_symm_cechRestrictL, hofeq,
    riemannRochSpaceEquivGlobalSections_symm_cechRestrictL]
  apply Subtype.ext
  rw [riemannRochSpaceAddPointInclusion, Submodule.coe_inclusion,
    linearSystemToRiemannRoch_coe, linearSystemToRiemannRoch_coe]

end Jacobians.Layer3
