/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.Bridge.KirovDolbeaultPeriods
import Submission.Jacobians.RiemannSurface.Genus
import Submission.Jacobians.Jacobian.Construction
import Submission.Jacobians.Axioms.PeriodLattice
import Submission.KirovDolbeault.TracePullback
import Submission.KirovDolbeault.Degree

/-!
# Bridge: the Kirov-Dolbeault period lattice alignment

The coordinate/basis bridge between our period lattice
(`periodLatticeInBasis`, developing values over `H1`) and the Dolbeault
port's `truePeriodLattice` (line integrals over `IsClosedSmoothLoop`s):

* `latticeBridge` / `latticeBridgeInv` / `latticeBridgeEquiv` — the
  coordinate change `(Fin (kirovGenus Y) → ℂ) ≃ₗ[ℂ] (Fin (genus Y) → ℂ)`
  induced by `bridgeKDFormEquiv` and the two bases;
* `latticeBridge_periodVec` — the bridge of a port period vector pairs the
  bridged basis forms against the loop;
* **the two lattice-comparison inclusions, proven** (these were the two
  smuggled axioms of the closed PR #191):
  `latticeBridge_truePeriodLattice_le` (port lattice → our lattice, via
  `developingValue_eq_lineIntegral_of_isClosedSmoothLoop`) and
  `truePeriodLattice_le_periodLatticeInBasis` (our lattice → port lattice,
  via `exists_isClosedSmoothLoop_lineIntegral_eq_developingValue`);
* `JacobianTorus.ambientPhi_ambientPullback_eq` — the ambient degree
  identity `Φ ∘ Tᵀ = deg • id` (Griffiths–Harris Ch. 2 §2.7), from the
  port's `PreimageCycle` conservation-of-number plus the ℝ-spanning
  ℤ-basis of our period lattice (`AX_PeriodLattice`, a theorem).

Linear-algebra layer and overall architecture adapted from daouid's closed
PR #191 (credit: daouid); the two lattice inclusions are proven here
instead of axiomatized.
-/

noncomputable section

open scoped Manifold ContDiff
open Jacobians.Bridge
open Jacobians.RiemannSurface
open Jacobians
open Jacobians.Axioms

namespace Jacobians.Bridge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

omit [Nonempty X] in
/-- The geometric genus of `X` equals the Kirov genus (both are the
`finrank` of the respective form spaces, identified by `bridgeKDFormEquiv`). -/
theorem genus_eq_kirovGenus : genus X = kirovGenus X := by
  unfold genus kirovGenus
  exact LinearEquiv.finrank_eq (bridgeKDFormEquiv (X := X))

/-- The linear map transferring Kirov's period coordinates to our basis
coordinates (daouid, PR #191). -/
def latticeBridge (Y : Type*) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y] :
    (Fin (kirovGenus Y) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ) where
  toFun w j :=
    ∑ i, ((ambientIso Y).symm
      (bridgeKDFormEquiv (jacobianBasis Y j))) i * w i
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h1 : (fun i => ((ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y j))) i
          * (c * x i)) =
        (fun i => c * (((ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y j))) i
          * x i)) := by
      funext i; ring
    simp_rw [h1]
    rw [Finset.mul_sum]

/-- The adjoint (transpose) identity relating `ambientTrace` and
`ambientPullbackJac` (daouid, PR #191). -/
theorem adjoint_identity {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Nonempty Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (u : Fin (kirovGenus X) → ℂ) (w : Fin (kirovGenus Y) → ℂ) :
    ∑ i, u i * (ambientPullbackJac f hf w) i =
      ∑ k, (ambientTrace f hf u) k * w k := by
  set T := ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf
  unfold ambientPullbackJac
  set M := LinearMap.toMatrix (Pi.basisFun ℂ (Fin (kirovGenus X)))
    (Pi.basisFun ℂ (Fin (kirovGenus Y))) T.toLinearMap
  change ∑ i, u i * Matrix.mulVec M.transpose w i = ∑ k, (T u) k * w k
  simp only [Matrix.mulVec, Matrix.transpose_apply]
  have h_swap : ∀ i, u i * ((fun j => M j i) ⬝ᵥ w) = ∑ j, M j i * u i * w j := by
    intro i
    change u i * (∑ j, M j i * w j) = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp_rw [h_swap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  have h_u_decomp : u = ∑ i, u i • Pi.single i 1 := pi_eq_sum_univ' u
  have h_T_decomp : T u = ∑ i, u i • T (Pi.single i 1) := by
    conv_lhs => rw [h_u_decomp]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  have h_j : (T u) j = ∑ i, M j i * u i := by
    rw [h_T_decomp]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show u i * T (Pi.single i 1) j = M j i * u i by
      unfold M
      rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply, mul_comm]
      rfl]
  rw [h_j]

/-- Kirov's line integral along a fixed closed smooth loop, as a ℂ-linear
map in the form (daouid, PR #191). -/
def lineIntegralLinearMap {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Nonempty Y] (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ) :
    _root_.Jacobians.HolomorphicOneForms Y →ₗ[ℂ] ℂ where
  toFun α := lineIntegral α γ
  map_add' α β := lineIntegral_add α β γ
    (intervalIntegrable_form_pathSpeed_of_velContinuous α γ hγ.velCont)
    (intervalIntegrable_form_pathSpeed_of_velContinuous β γ hγ.velCont)
  map_smul' c α := by
    simp [lineIntegral_smul, RingHom.id_apply]

/-- The period vector maps under `latticeBridge` to the line integrals of
the bridged basis forms (daouid, PR #191). -/
theorem latticeBridge_periodVec {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Nonempty Y] (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ) (j : Fin (genus Y)) :
    latticeBridge Y (periodVec γ) j =
      lineIntegral (bridgeKDFormEquiv (jacobianBasis Y j)) γ := by
  unfold latticeBridge
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  unfold periodVec
  unfold periodBasisForm
  set c := (ambientIso Y).symm (bridgeKDFormEquiv (jacobianBasis Y j))
  change ∑ i, c i * lineIntegral (ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i)) γ =
    lineIntegral (bridgeKDFormEquiv (jacobianBasis Y j)) γ
  have h_eq (i : Fin (kirovGenus Y)) :
      lineIntegral (ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i)) γ =
        (lineIntegralLinearMap γ hγ) (ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i)) := rfl
  simp_rw [h_eq]
  have h_sum : ∑ i, c i * (lineIntegralLinearMap γ hγ)
        (ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i)) =
      (lineIntegralLinearMap γ hγ)
        (∑ i, c i • ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [h_sum]
  set η := bridgeKDFormEquiv (jacobianBasis Y j)
  have h_basis : ∑ i, ((ambientIso Y).symm η) i •
      ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i) = η := by
    simp_rw [← map_smul]
    rw [← map_sum]
    have h_decomp := (Pi.basisFun ℂ (Fin (kirovGenus Y))).sum_repr ((ambientIso Y).symm η)
    simp only [Pi.basisFun_repr] at h_decomp
    rw [h_decomp, LinearEquiv.apply_symm_apply]
  rw [h_basis]
  rfl

/-- The pairing of a holomorphic 1-form with a Kirov period vector, as a
ℂ-linear map (daouid, PR #191). -/
def pairingWithW {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y]
    (w : Fin (kirovGenus Y) → ℂ) : HolomorphicOneForm Y →ₗ[ℂ] ℂ where
  toFun η := ∑ i, ((ambientIso Y).symm (bridgeKDFormEquiv η)) i * w i
  map_add' x y := by
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h : (fun i => (c * ((ambientIso Y).symm (bridgeKDFormEquiv x)) i) * w i) =
             (fun i => c * (((ambientIso Y).symm (bridgeKDFormEquiv x)) i * w i)) := by
      funext i; ring
    simp_rw [h]
    rw [Finset.mul_sum]

/-- The dual-basis coordinate functional of `latticeBridge Y w` is
`pairingWithW w` (daouid, PR #191). -/
theorem eY_symm_latticeBridge {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Nonempty Y] (w : Fin (kirovGenus Y) → ℂ) :
    (jacobianBasis Y).dualBasis.equivFun.symm (latticeBridge Y w) = pairingWithW w := by
  refine (jacobianBasis Y).ext (fun j => ?_)
  rw [← (jacobianBasis Y).dualBasis_equivFun, LinearEquiv.apply_symm_apply]
  rfl

/-- The inverse linear map of `latticeBridge Y` (daouid, PR #191). -/
def latticeBridgeInv (Y : Type*) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y] :
    (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (kirovGenus Y) → ℂ) where
  toFun v i := ((jacobianBasis Y).dualBasis.equivFun.symm v)
    ((bridgeKDFormEquiv (X := Y)).symm (ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) i)))
  map_add' x y := by
    ext i
    dsimp
    rw [map_add]
    rfl
  map_smul' c x := by
    ext i
    dsimp
    rw [map_smul]
    rfl

theorem latticeBridgeInv_left_inverse {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Nonempty Y] (w : Fin (kirovGenus Y) → ℂ) :
    latticeBridgeInv Y (latticeBridge Y w) = w := by
  ext k
  dsimp [latticeBridgeInv]
  have h_pair : ((jacobianBasis Y).dualBasis.equivFun.symm (latticeBridge Y w)) =
      pairingWithW w :=
    eY_symm_latticeBridge w
  rw [h_pair]
  unfold pairingWithW
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have h_trans : (ambientIso Y).symm (bridgeKDFormEquiv
      ((bridgeKDFormEquiv (X := Y)).symm
        (ambientIso Y (Pi.basisFun ℂ (Fin (kirovGenus Y)) k)))) =
      Pi.basisFun ℂ (Fin (kirovGenus Y)) k := by
    simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  rw [h_trans]
  have h_sum : ∑ i, (Pi.basisFun ℂ (Fin (kirovGenus Y)) k) i * w i = w k := by
    simp_rw [Pi.basisFun_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hk
      exact False.elim (hk (Finset.mem_univ k))
  exact h_sum

theorem latticeBridgeInv_right_inverse {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Nonempty Y] (v : Fin (genus Y) → ℂ) :
    latticeBridge Y (latticeBridgeInv Y v) = v := by
  have h_eq : (jacobianBasis Y).dualBasis.equivFun.symm (latticeBridge Y (latticeBridgeInv Y v)) =
      (jacobianBasis Y).dualBasis.equivFun.symm v := by
    refine (jacobianBasis Y).ext (fun j => ?_)
    rw [eY_symm_latticeBridge]
    unfold pairingWithW
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    set η := bridgeKDFormEquiv (jacobianBasis Y j)
    have h_eval : ∑ i, ((ambientIso Y).symm η) i * (latticeBridgeInv Y v) i =
        ((jacobianBasis Y).dualBasis.equivFun.symm v)
          (bridgeKDFormEquiv.symm (ambientIso Y
            (∑ i, ((ambientIso Y).symm η) i • Pi.basisFun ℂ (Fin (kirovGenus Y)) i))) := by
      dsimp [latticeBridgeInv]
      simp_rw [← smul_eq_mul, ← map_smul, ← map_sum]
    rw [h_eval]
    have h_sum : ∑ i, ((ambientIso Y).symm η) i • Pi.basisFun ℂ (Fin (kirovGenus Y)) i =
        (ambientIso Y).symm η := by
      have h_decomp := (Pi.basisFun ℂ (Fin (kirovGenus Y))).sum_repr ((ambientIso Y).symm η)
      simp only [Pi.basisFun_repr] at h_decomp
      exact h_decomp
    rw [h_sum]
    have h_inv : bridgeKDFormEquiv.symm ((ambientIso Y) ((ambientIso Y).symm η)) =
        (jacobianBasis Y) j := by
      dsimp [η]
      simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rw [h_inv]
  exact (LinearEquiv.injective (jacobianBasis Y).dualBasis.equivFun.symm) h_eq

/-- The canonical linear isomorphism between Kirov's period coordinates and
our basis coordinates (daouid, PR #191). -/
def latticeBridgeEquiv (Y : Type*) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y] :
    (Fin (kirovGenus Y) → ℂ) ≃ₗ[ℂ] (Fin (genus Y) → ℂ) where
  toLinearMap := latticeBridge Y
  invFun := latticeBridgeInv Y
  left_inv := latticeBridgeInv_left_inverse
  right_inv := latticeBridgeInv_right_inverse

/-! ## The two lattice-comparison inclusions — now theorems

These were the two smuggled axioms of the closed PR #191; they are proven
here from the developing-value ↔ line-integral comparison of
`Bridge/KirovDolbeaultPeriods.lean`. -/

/-- **Port lattice → our lattice.** Kirov's true period lattice maps into our
coordinate period lattice under `latticeBridge`: on the span generators
(period vectors of closed smooth loops) the bridge produces the
developing-value period vector of the loop, which lies in
`periodLatticeInBasis` at any basepoint. -/
theorem latticeBridge_truePeriodLattice_le (Y : Type*) [TopologicalSpace Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y] :
    ∀ w ∈ truePeriodLattice Y,
      latticeBridge Y w ∈ periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y) := by
  intro w hw
  rw [truePeriodLattice] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    have hvec : latticeBridge Y (periodVec γ) = fun j =>
        developingValue (γ 0) (jacobianBasis Y j)
          ((loopToPath γ hγ : Path (γ 0) (γ 0)) : C(unitInterval, Y)) := by
      funext j
      rw [latticeBridge_periodVec γ hγ j, port_lineIntegral_bridgeKD, loopToPath_coe]
      exact (developingValue_eq_lineIntegral_of_isClosedSmoothLoop
        (jacobianBasis Y j) γ hγ (γ 0)).symm
    rw [hvec]
    exact devVal_loop_mem_periodLatticeInBasis_any (Classical.arbitrary Y)
      (jacobianBasis Y) (loopToPath γ hγ)
  | zero => simp
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [map_zsmul]
    exact Submodule.smul_mem _ a ih

/-- **Our lattice → port lattice.** Every vector of our coordinate period
lattice maps under `latticeBridgeInv` into Kirov's true period lattice: a
lattice vector is the developing-value period vector of a representative
continuous loop of an `H1` class; the smooth-representative theorem
produces a closed `C¹` loop with the same bridged line integrals, whose
port period vector therefore bridges to the given vector. -/
theorem truePeriodLattice_le_periodLatticeInBasis (Y : Type*) [TopologicalSpace Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y] :
    ∀ v ∈ periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y),
      latticeBridgeInv Y v ∈ truePeriodLattice Y := by
  classical
  intro v hv
  set y₀ : Y := Classical.arbitrary Y with hy₀_def
  obtain ⟨γh, hγh⟩ := hv
  -- Every `H1` class is the class of a representative loop.
  obtain ⟨g, hg⟩ : ∃ g : FundamentalGroup Y y₀,
      Additive.ofMul (Abelianization.of g) = γh := by
    obtain ⟨g, hg⟩ := Quot.exists_rep (Additive.toMul γh)
    exact ⟨g, by simpa using congrArg Additive.ofMul hg⟩
  obtain ⟨γp, hγp⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
  -- The lattice vector is the developing-value vector of the loop.
  have hcoord : ∀ j, v j = developingValue y₀ (jacobianBasis Y j)
      ((γp : Path y₀ y₀) : C(unitInterval, Y)) := by
    intro j
    have h1 : v j = RiemannSurface.periodMap Y y₀ γh (jacobianBasis Y j) := by
      rw [← hγh]
      show ((jacobianBasis Y).dualBasis.equivFun
        (RiemannSurface.periodMap Y y₀ γh)) j = _
      rw [Module.Basis.dualBasis_equivFun]
    have h2 : RiemannSurface.periodMap Y y₀ γh (jacobianBasis Y j) =
        developingValue y₀ (jacobianBasis Y j)
          ((γp : Path y₀ y₀) : C(unitInterval, Y)) := by
      have hPM : RiemannSurface.periodMap Y y₀ γh =
          loopIntegralToH1 y₀ γh := rfl
      rw [hPM, ← loopDevValH1Hom_eq_loopIntegralToH1_apply, ← hg,
        loopDevValH1Hom_of]
      show loopDevValQuotient y₀ (jacobianBasis Y j)
          (FundamentalGroup.toPath g) = _
      rw [← hγp]
      rfl
    rw [h1, h2]
  -- Smooth representative with the same bridged line integrals.
  obtain ⟨γ', hγ', _hbase, hval⟩ :=
    exists_isClosedSmoothLoop_lineIntegral_eq_developingValue y₀ γp
  have hbridge : latticeBridge Y (periodVec γ') = v := by
    funext j
    rw [latticeBridge_periodVec γ' hγ' j, hval (jacobianBasis Y j), ← hcoord j]
  have hinv : latticeBridgeInv Y v = periodVec γ' := by
    rw [← hbridge, latticeBridgeInv_left_inverse]
  rw [hinv]
  exact periodVec_mem_truePeriodLattice_of_closed γ' hγ'

/-! ## The ambient degree identity (Griffiths–Harris Ch. 2 §2.7) -/

namespace JacobianTorus

/-- `Φ(Tᵀ(periodVec δ)) = deg • periodVec δ` given a preimage cycle with
sheet count equal to the degree (daouid, PR #191). -/
lemma ambientPhi_ambientPullback_periodVec_of_cycle {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {n : ℕ} (loops : Fin n → ℝ → X)
    (loops_smooth : ∀ i, IsClosedSmoothLoop (loops i))
    (coeffs : Fin n → ℤ) (δ : ℝ → Y)
    (h_pullback : ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (periodVec δ) = ∑ i, coeffs i • periodVec (loops i))
    (h_pushforward : ∑ i, coeffs i • periodVec (f ∘ loops i) =
        (degreeFiber f hf) • periodVec δ) :
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf
          (periodVec δ)) =
      (degreeFiber f hf) • periodVec δ := by
  rw [h_pullback, map_sum, ← h_pushforward]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, periodVec_pushforward f hf (loops i) (loops_smooth i).cont
    (loops_smooth i).diff (loops_smooth i).integrable]

/-- A preimage cycle with sheet count equal to `degreeFiber` exists for any
closed smooth loop (daouid, PR #191). -/
theorem exists_preimageCycle_sheets_eq_degree {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (δ : ℝ → Y)
    (hδ : IsClosedSmoothLoop δ) :
    ∃ c : PreimageCycle f hf δ, c.sheets = degreeFiber f hf := by
  by_cases hconst : ∃ y₀ : Y, ∀ x, f x = y₀
  · refine ⟨{ n := 0, loops := Fin.elim0, loops_smooth := fun i => i.elim0,
              coeffs := Fin.elim0, sheets := 0, pullback_eq := ?_,
              pushforward_eq := ?_ }, ?_⟩
    · rw [ambientPullbackJac_eq_zero_of_const f hf hconst]; simp
    · simp
    · show (0 : ℕ) = degreeFiber f hf
      have hcm : Jacobians.Discharge.IsConstantMap f := hconst
      rw [degreeFiber]
      exact (if_pos hcm).symm
  · obtain ⟨c, y₀, hy₀, hsheets⟩ :=
      exists_preimageCycle_sheets_eq_fibreCard_of_nonconstant f hf hconst δ hδ
    refine ⟨c, ?_⟩
    obtain ⟨w, hwval⟩ :=
      Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq f hf hconst
        (notMem_criticalValuesGeneral_of_notMem_branchLocus hy₀)
    have hwcard : w.card = (f ⁻¹' {y₀}).ncard := by
      have h1 : w.card = w.toWitness.card := rfl
      rw [h1, w.toWitness.card_eq_ncard, hwval]
    show c.sheets = degreeFiber f hf
    rw [hsheets, show degreeFiber f hf = degreeFiber f hf from rfl,
      degreeFiber_eq_card_of_regularWitness f hf hconst w, hwcard]

private lemma ambientPhi_ambientPullback_periodVec_eq {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (δ : ℝ → Y)
    (hδ : IsClosedSmoothLoop δ) :
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
      (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (periodVec δ)) =
      (degreeFiber f hf) • periodVec δ := by
  obtain ⟨c, hc⟩ := exists_preimageCycle_sheets_eq_degree f hf δ hδ
  have hpush : ∑ i, c.coeffs i • periodVec (f ∘ c.loops i) =
      (degreeFiber f hf) • periodVec δ := by
    rw [c.pushforward_eq, hc]; exact natCast_zsmul _ _
  exact ambientPhi_ambientPullback_periodVec_of_cycle f hf
    c.loops c.loops_smooth c.coeffs δ c.pullback_eq hpush

private lemma ambientPhi_ambientPullback_eq_on_lattice {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (v : Fin (kirovGenus Y) → ℂ)
    (hv : v ∈ truePeriodLattice Y) :
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
      (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf v) =
      (degreeFiber f hf) • v := by
  rw [truePeriodLattice] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, rfl⟩ := hx
    exact ambientPhi_ambientPullback_periodVec_eq f hf δ hδ
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, smul_add, ihx, ihy]
  | smul a x _ ih => rw [map_zsmul, map_zsmul, ih, smul_comm]

/-- **Ambient degree identity** `Φ ∘ Tᵀ = deg • id` (Griffiths–Harris Ch. 2
§2.7): both sides are ℝ-linear and agree on an ℝ-spanning set — the
ℤ-basis of our period lattice (`AX_PeriodLattice`, a theorem),
transported to the port's coordinates through `latticeBridgeEquiv` and the
proven inclusion `truePeriodLattice_le_periodLatticeInBasis`
(daouid, PR #191; the inclusion is now a theorem). -/
theorem ambientPhi_ambientPullback_eq {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (y : Fin (kirovGenus Y) → ℂ) :
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
      (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf y) =
      (degreeFiber f hf) • y := by
  classical
  let Λ := periodLatticeInBasis Y (Classical.arbitrary Y) (jacobianBasis Y)
  letI : IsZLattice ℝ Λ := AX_PeriodLattice Y (Classical.arbitrary Y) (jacobianBasis Y)
  letI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  letI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b₀ := Module.Free.chooseBasis ℤ Λ
  let eY := (latticeBridgeEquiv Y).restrictScalars ℝ
  let b := (Module.Basis.ofZLatticeBasis ℝ Λ b₀).map eY.symm
  set Φ : (Fin (kirovGenus Y) → ℂ) →L[ℂ] (Fin (kirovGenus Y) → ℂ) :=
    (ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf).comp
      (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf) with hΦ
  have hsmul : ∀ (s : ℝ) (a : Fin (kirovGenus Y) → ℂ), s • a = (↑s : ℂ) • a :=
    fun s a => by funext j; simp [Complex.real_smul]
  have hlat : ∀ i, Φ (b i) = (degreeFiber f hf) • b i := by
    intro i
    have hmem : b i ∈ truePeriodLattice Y := by
      dsimp [b, eY]
      have h_in : Module.Basis.ofZLatticeBasis ℝ Λ b₀ i ∈ Λ := by
        rw [Module.Basis.ofZLatticeBasis_apply]
        exact Subtype.mem (b₀ i)
      exact truePeriodLattice_le_periodLatticeInBasis Y
        (Module.Basis.ofZLatticeBasis ℝ Λ b₀ i) h_in
    show ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (b i)) = _
    exact ambientPhi_ambientPullback_eq_on_lattice f hf (b i) hmem
  have per_term : ∀ (r : ℝ) i,
      Φ (r • b i) = (degreeFiber f hf) • (r • b i) := by
    intro r i
    have h_phi_smul : Φ (r • b i) = r • Φ (b i) := by
      rw [hsmul r (b i), map_smul, hsmul r (Φ (b i))]
    rw [h_phi_smul, hlat i, smul_comm]
  show Φ y = (degreeFiber f hf) • y
  conv_lhs => rw [← b.sum_repr y, map_sum]
  conv_rhs => rw [← b.sum_repr y, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => per_term (b.repr y i) i)

end JacobianTorus

end Jacobians.Bridge
