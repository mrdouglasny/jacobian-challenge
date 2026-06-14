/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.RiemannSurface.AbelPlumbing
import Submission.Jacobians.RiemannSurface.H1Composite
import Submission.Jacobians.RiemannSurface.LoopLattice
import Submission.Jacobians.Bridge.KirovDolbeaultOpenPath
import Submission.Jacobians.Layer3.LinearSystemBridge
import Submission.KirovDolbeault.Dolbeault.AbelSubsetEngineArc
import Submission.KirovDolbeault.Dolbeault.LerayCoverExists

/-!
# E6: the Abel-engine adapter (`AB_E_ROUTE.md` §0, final rung)

Discharges the named engine hypothesis `ZeroPeriodChainSolvability` of
`Jacobians/RiemannSurface/AbelPlumbing.lean` from the unconditional Forster
§20 weak-solution engine
(`Jacobians.Dolbeault.exists_meromorphic_of_zeroPeriodChain'`,
`vendor/kirov-dolbeault-port/.../AbelSubsetEngineArc.lean`).

Translation bricks (all consumed, none new in substance):

* **arcs** — the port's zero-endpoint-velocity `smoothPath x₀ P`
  (`KirovDolbeault.PeriodLattice`), whose moving-chart line integral of a
  bridged form is its developing value (#216,
  `developingValue_eq_port_lineIntegral_of_isSmoothPath`); the mismatch
  against the `ofCurveAmbient` reference path `bridgePathArc x₀ P` is the
  developing value of a CLOSED loop, hence a period-lattice vector
  (`devVal_loop_mem_periodLatticeInBasis`);
* **pinned loops** — the closed-loop smooth representative
  (`exists_isClosedSmoothLoop_lineIntegral_eq_developingValue`,
  `Bridge/KirovDolbeaultPeriods.lean`);
* **forms** — `bridgeKDFormEquiv` carries `jacobianBasis X` to a spanning
  family of the port's `HolomorphicOneForms X`, and the engine-side E1
  rung (`SmoothOneChain.period_eq_zero_of_spanning`) extends vanishing of
  the bridged-basis periods to all port forms;
* **divisors** (E6b) — a port `MeromorphicFunction` with nonzero divisor
  has `orderW ≠ ⊤` everywhere (the port identity theorem
  `orderW_ne_top_of_exists`), so it wraps as a root
  `MeromorphicFunctionField.Rep` whose root divisor matches under
  `FreeAbelianGroup.equivFinsupp`; its class exhibits membership in
  `PrincipalDivisors X`.

Main results:

* `mem_principalDivisors_of_port_div` — E6b;
* `zeroPeriodChainSolvability` — the discharged engine hypothesis;
* `abel_subset` — `(abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker ≤
  PrincipalDivisors X`, the ⊆ direction of Abel's theorem, fully
  unconditional on the engine side.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.Bridge

open Jacobians.RiemannSurface
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

/- Name-resolution shim (same pattern as `Jacobians/Layer3/CechH1Bridge.lean`):
inside the `Jacobians.Bridge` namespace the bare name `Divisor` would resolve
to the PORT's `Jacobians.Divisor` (`X →₀ ℤ`); pin it to our
`FreeAbelianGroup` divisor layer. -/
export Jacobians.Axioms (Divisor Divisor.deg)

open Jacobians.Axioms (PrincipalDivisors)

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## E6b: port divisor output ⇒ root principal-divisor membership -/

/-- The port's integer order is the `untop₀` of its `WithTop ℤ` order. -/
theorem port_orderAtPoint_eq_untop₀_orderW
    (f : _root_.Jacobians.MeromorphicFunction X) (x : X) :
    _root_.Jacobians.MeromorphicFunction.orderAtPoint f x = (f.orderW x).untop₀ :=
  rfl

/-- The port divisor evaluates pointwise to the port order. -/
theorem port_div_apply (f : _root_.Jacobians.MeromorphicFunction X) (x : X) :
    _root_.Jacobians.MeromorphicFunction.div X f x =
      _root_.Jacobians.MeromorphicFunction.orderAtPoint f x := by
  rw [_root_.Jacobians.MeromorphicFunction.div,
    _root_.Jacobians.MeromorphicFunction.divViaOrder,
    Finsupp.ofSupportFinite_coe]

/-- **E6b (divisor faithfulness).** A port meromorphic function whose port
divisor is the `Finsupp` translation of a NONZERO root divisor `D` exhibits
`D` as principal: the identity theorem (`orderW_ne_top_of_exists`) upgrades
the single nonzero-order point to germ-nonvanishing everywhere, so the
function wraps as a root `MeromorphicFunctionField.Rep` with root divisor
`D`. -/
theorem mem_principalDivisors_of_port_div {D : Divisor X} (hD : D ≠ 0)
    (f : _root_.Jacobians.MeromorphicFunction X)
    (hdiv : _root_.Jacobians.MeromorphicFunction.div X f =
      FreeAbelianGroup.equivFinsupp X D) :
    D ∈ PrincipalDivisors X := by
  -- the translated divisor is nonzero, so some point carries nonzero order
  have hE : FreeAbelianGroup.equivFinsupp X D ≠ 0 := by
    intro h
    exact hD ((FreeAbelianGroup.equivFinsupp X).injective (by simp [h]))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, FreeAbelianGroup.equivFinsupp X D P₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Finsupp.ext h)
  -- nonzero integer order at `P₀` forces `orderW ≠ ⊤` there, hence everywhere
  have hP₀' : _root_.Jacobians.MeromorphicFunction.orderAtPoint f P₀ ≠ 0 := by
    rw [← port_div_apply, hdiv]
    exact hP₀
  have hne_top : ∀ x, f.orderW x ≠ ⊤ := by
    refine _root_.Jacobians.MeromorphicFunction.orderW_ne_top_of_exists f ⟨P₀, ?_⟩
    intro htop
    exact hP₀' (by rw [port_orderAtPoint_eq_untop₀_orderW, htop]; rfl)
  -- wrap as a root representative
  let r : MeromorphicFunctionField.Rep X :=
    { toFun := f.toFun
      meromorphicAt := fun p =>
        (Jacobians.Layer3.meromorphicAtX_iff_chartAt f.toFun p).mpr (f.meromorphic p)
      order_ne_top := fun p => by
        rw [← Jacobians.Layer3.orderW_mk_eq_orderAt f.toFun f.meromorphic]
        exact hne_top p }
  -- its root divisor is `D`
  have hdivisor : MeromorphicFunctionField.Rep.divisor r = D := by
    apply (FreeAbelianGroup.equivFinsupp X).injective
    ext p
    have hcoeff : FreeAbelianGroup.equivFinsupp X (MeromorphicFunctionField.Rep.divisor r) p =
        (orderAt p (r : X → ℂ)).untop₀ := by
      simp [MeromorphicFunctionField.Rep.divisor, MeromorphicFunctionField.Rep.orderFinsupp,
        Finsupp.ofSupportFinite_coe]
    rw [hcoeff]
    have horder : orderAt p (r : X → ℂ) = f.orderW p :=
      (Jacobians.Layer3.orderW_mk_eq_orderAt f.toFun f.meromorphic p).symm
    rw [horder, ← port_orderAtPoint_eq_untop₀_orderW, ← port_div_apply, hdiv]
  -- exhibit the principal-divisor membership
  rw [PrincipalDivisors]
  refine ⟨Quotient.mk (MeromorphicFunctionField.Rep.setoid (X := X)) r, ?_⟩
  show Multiplicative.ofAdd
      (MeromorphicFunctionField.divisor
        (Quotient.mk (MeromorphicFunctionField.Rep.setoid (X := X)) r)) =
    Multiplicative.ofAdd D
  rw [show MeromorphicFunctionField.divisor
        (Quotient.mk (MeromorphicFunctionField.Rep.setoid (X := X)) r) =
      MeromorphicFunctionField.Rep.divisor r from rfl, hdivisor]

/-! ## Divisor expansion over the `Finsupp` support -/

/-- Any hom out of the free abelian group of divisors evaluates as the
support-sum of its values on generators, weighted by the `Finsupp`
coefficients. -/
theorem hom_apply_eq_sum_support {M : Type*} [AddCommGroup M]
    (φ : FreeAbelianGroup X →+ M) (D : FreeAbelianGroup X) :
    φ D = ∑ Q ∈ (FreeAbelianGroup.toFinsupp D).support,
      (FreeAbelianGroup.toFinsupp D) Q • φ (FreeAbelianGroup.of Q) := by
  conv_lhs => rw [← Finsupp.toFreeAbelianGroup_toFinsupp D,
    ← Finsupp.sum_single (FreeAbelianGroup.toFinsupp D)]
  rw [Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Finsupp.toFreeAbelianGroup_single, map_zsmul]

/-! ## Pinned-loop periods as developing values -/

/-- The `periodMapInBasis` value of an analytic loop's homology class is the
developing value of the loop's underlying continuous path (composition of
`loopDevValH1Hom_eq_loopIntegralToH1_apply` with `loopDevValH1Hom_fromPath`). -/
theorem periodMapInBasis_loopToHomology_apply (x₀ : X) (loop : AnalyticLoop X x₀)
    (i : Fin (genus X)) :
    Jacobians.Axioms.periodMapInBasis X x₀ (jacobianBasis X)
        (Jacobians.Axioms.loopToHomology loop) i =
      developingValue x₀ (jacobianBasis X i)
        ((Jacobians.Axioms.loopToPath loop : Path x₀ x₀) : C(unitInterval, X)) := by
  have h2 : Jacobians.Axioms.periodMapInBasis X x₀ (jacobianBasis X)
      (Jacobians.Axioms.loopToHomology loop) i =
      (loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology loop)) (jacobianBasis X i) := by
    simp [Jacobians.Axioms.periodMapInBasis, periodMap, LinearMap.comp_apply,
      (jacobianBasis X).dualBasis_equivFun]
  rw [h2, ← loopDevValH1Hom_eq_loopIntegralToH1_apply]
  exact loopDevValH1Hom_fromPath x₀ (jacobianBasis X i) (Jacobians.Axioms.loopToPath loop)

/-! ## The `Path` view of the `ofCurveAmbient` reference arc -/

/-- The bridge path `bridgePathArc x₀ P` as a continuous `Path x₀ P`. -/
def bridgeArcPath (x₀ P : X) : Path x₀ P where
  toContinuousMap :=
    Jacobians.RiemannSurface.analyticArcToContinuousMap (bridgePathArc x₀ P)
  source' := by
    show (bridgePathArc x₀ P).extend ((0 : unitInterval) : ℝ) = x₀
    rw [show ((0 : unitInterval) : ℝ) = (0 : ℝ) from rfl]
    exact bridgePathImpl_at_zero x₀ P
  target' := by
    show (bridgePathArc x₀ P).extend ((1 : unitInterval) : ℝ) = P
    rw [show ((1 : unitInterval) : ℝ) = (1 : ℝ) from rfl]
    exact bridgePathImpl_at_one x₀ P

/-- The developing value of the bridge path computes `ofCurveAmbient`. -/
theorem devVal_bridgeArcPath (x₀ P : X) (i : Fin (genus X)) :
    developingValue x₀ (jacobianBasis X i)
        ((bridgeArcPath x₀ P : Path x₀ P) : C(unitInterval, X)) =
      Jacobians.Axioms.ofCurveAmbient X x₀ P i :=
  developingValue_eq_canonicalArcIntegral x₀ (jacobianBasis X i) (bridgePathArc x₀ P)

/-! ## The per-arc value identity -/

/-- **Per-arc identity.** The port smooth path's moving-chart line integral
of a bridged basis form is `ofCurveAmbient` minus the developing value of
the closed comparison loop (bridge path forward, smooth path backward). -/
theorem port_lineIntegral_smoothPath_eq (x₀ P : X) (i : Fin (genus X)) :
    _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (jacobianBasis X i))
        (_root_.Jacobians.smoothPath x₀ P) =
      Jacobians.Axioms.ofCurveAmbient X x₀ P i -
        developingValue x₀ (jacobianBasis X i)
          (((bridgeArcPath x₀ P).trans
              (smoothPathToPath (_root_.Jacobians.smoothPath x₀ P)
                (_root_.Jacobians.isSmoothPath_smoothPath x₀ P)).symm :
            Path x₀ x₀) : C(unitInterval, X)) := by
  have hline : developingValue x₀ (jacobianBasis X i)
      ((smoothPathToPath (_root_.Jacobians.smoothPath x₀ P)
          (_root_.Jacobians.isSmoothPath_smoothPath x₀ P) : Path x₀ P) :
        C(unitInterval, X)) =
      _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (jacobianBasis X i))
        (_root_.Jacobians.smoothPath x₀ P) :=
    developingValue_eq_port_lineIntegral_of_isSmoothPath (jacobianBasis X i) _
      (_root_.Jacobians.isSmoothPath_smoothPath x₀ P) x₀
  rw [devVal_trans x₀ (jacobianBasis X i) (bridgeArcPath x₀ P)
      (smoothPathToPath (_root_.Jacobians.smoothPath x₀ P)
        (_root_.Jacobians.isSmoothPath_smoothPath x₀ P)).symm,
    devVal_symm x₀ (jacobianBasis X i)
      (smoothPathToPath (_root_.Jacobians.smoothPath x₀ P)
        (_root_.Jacobians.isSmoothPath_smoothPath x₀ P)),
    devVal_bridgeArcPath, hline]
  ring

/-! ## The discharged engine hypothesis -/

/-- **E6 (the adapter): `ZeroPeriodChainSolvability` holds.** Every degree-0
divisor with a zero-period 1-chain presentation over the pinned cycle basis
is principal — discharged from the unconditional Forster §20 engine
`exists_meromorphic_of_zeroPeriodChain'` through the four translation
bricks (arcs / pinned loops / forms / divisors) described in the module
docstring. -/
theorem zeroPeriodChainSolvability_of_engine :
    ZeroPeriodChainSolvability X := by
  intro D hdeg hpres
  by_cases hD0 : D = 0
  · subst hD0
    exact (PrincipalDivisors X).zero_mem
  classical
  set x₀ : X := Classical.arbitrary X with hx₀
  set b := jacobianBasis X with hb
  obtain ⟨m, hm⟩ := hpres
  set cb := pinnedCycleBasis x₀ with hcb
  set E : X →₀ ℤ := FreeAbelianGroup.equivFinsupp X D with hE
  have hE_toFinsupp : E = FreeAbelianGroup.toFinsupp D := rfl
  set k : ℕ := E.support.card with hk
  set eqv : ↥E.support ≃ Fin k := E.support.equivFin with heqv
  set P : Fin k → X := fun a => ((eqv.symm a : ↥E.support) : X) with hP
  -- reindexing: sums over `Fin k` of point-functions are support sums
  -- (three monomorphic copies; a `Type*` binder inside `have` cannot be
  -- universe-polymorphic across `ℤ`, `X →₀ ℤ` and `Fin (genus X) → ℂ`)
  have hreindexV : ∀ g : X → (Fin (genus X) → ℂ),
      ∑ a : Fin k, g (P a) = ∑ Q ∈ E.support, g Q := by
    intro g
    rw [show (∑ a : Fin k, g (P a)) =
        ∑ a : Fin k, (fun s : ↥E.support => g s) (eqv.symm a) from rfl,
      Equiv.sum_comp eqv.symm (fun s : ↥E.support => g (s : X))]
    exact Finset.sum_coe_sort E.support g
  have hreindexZ : ∀ g : X → ℤ,
      ∑ a : Fin k, g (P a) = ∑ Q ∈ E.support, g Q := by
    intro g
    rw [show (∑ a : Fin k, g (P a)) =
        ∑ a : Fin k, (fun s : ↥E.support => g s) (eqv.symm a) from rfl,
      Equiv.sum_comp eqv.symm (fun s : ↥E.support => g (s : X))]
    exact Finset.sum_coe_sort E.support g
  have hreindexF : ∀ g : X → (X →₀ ℤ),
      ∑ a : Fin k, g (P a) = ∑ Q ∈ E.support, g Q := by
    intro g
    rw [show (∑ a : Fin k, g (P a)) =
        ∑ a : Fin k, (fun s : ↥E.support => g s) (eqv.symm a) from rfl,
      Equiv.sum_comp eqv.symm (fun s : ↥E.support => g (s : X))]
    exact Finset.sum_coe_sort E.support g
  -- the comparison loops and their lattice vectors
  set lam : Fin k → Path x₀ x₀ := fun a =>
    (bridgeArcPath x₀ (P a)).trans
      (smoothPathToPath (_root_.Jacobians.smoothPath x₀ (P a))
        (_root_.Jacobians.isSmoothPath_smoothPath x₀ (P a))).symm with hlam
  set va : Fin k → (Fin (genus X) → ℂ) := fun a i =>
    developingValue x₀ (b i) ((lam a : Path x₀ x₀) : C(unitInterval, X)) with hva
  have hva_apply : ∀ a i, va a i =
      developingValue x₀ (b i) ((lam a : Path x₀ x₀) : C(unitInterval, X)) :=
    fun _ _ => rfl
  have hva_mem : ∀ a, va a ∈ Jacobians.Axioms.periodLatticeInBasis X x₀ b := fun a =>
    devVal_loop_mem_periodLatticeInBasis x₀ b (lam a)
  -- the arc-period vector and its lattice membership
  set A : Fin (genus X) → ℂ := fun i => ∑ a : Fin k,
    (E (P a) : ℂ) * _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
      (_root_.Jacobians.smoothPath x₀ (P a)) with hA
  have hA_apply : ∀ i, A i = ∑ a : Fin k,
      (E (P a) : ℂ) * _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
        (_root_.Jacobians.smoothPath x₀ (P a)) := fun _ => rfl
  have hdpv : divisorPeriodVector x₀ D =
      ∑ a : Fin k, E (P a) • Jacobians.Axioms.ofCurveAmbient X x₀ (P a) := by
    rw [hom_apply_eq_sum_support (X := X) (divisorPeriodVector x₀) D]
    have hsum : ∑ Q ∈ (FreeAbelianGroup.toFinsupp D).support,
        (FreeAbelianGroup.toFinsupp D) Q • divisorPeriodVector x₀ (FreeAbelianGroup.of Q) =
        ∑ Q ∈ E.support, E Q • Jacobians.Axioms.ofCurveAmbient X x₀ Q := by
      refine Finset.sum_congr (by rw [← hE_toFinsupp]) fun Q _ => ?_
      rw [divisorPeriodVector_of, ← hE_toFinsupp]
    rw [hsum]
    exact (hreindexV (fun Q => E Q • Jacobians.Axioms.ofCurveAmbient X x₀ Q)).symm
  have hA_eq : A = divisorPeriodVector x₀ D - ∑ a : Fin k, E (P a) • va a := by
    funext i
    rw [hA_apply i, Pi.sub_apply, hdpv, Finset.sum_apply, Finset.sum_apply,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul,
      port_lineIntegral_smoothPath_eq x₀ (P a) i, hva_apply a i]
    ring
  have hA_mem : A ∈ Jacobians.Axioms.periodLatticeInBasis X x₀ b := by
    rw [hA_eq]
    refine sub_mem ?_ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hva_mem a))
    rw [hm]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (LinearMap.mem_range_self _ _)
  -- expand the arc-period vector over the pinned loops
  obtain ⟨h, hh⟩ := hA_mem
  set m' : Fin (2 * genus X) → ℤ := fun j => cb.isBasis.repr h j with hm'
  have hexpand : A = ∑ j, m' j •
      Jacobians.Axioms.periodMapInBasis X x₀ b
        (Jacobians.Axioms.loopToHomology (cb.loops j)) := by
    rw [← hh]
    have hrepr : h = ∑ j, m' j • Jacobians.Axioms.loopToHomology (cb.loops j) := by
      conv_lhs => rw [← cb.isBasis.sum_repr h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cb.loops_to_basis j]
    rw [show Jacobians.Axioms.periodMapInBasis X x₀ b h =
        Jacobians.Axioms.periodMapInBasis X x₀ b
          (∑ j, m' j • Jacobians.Axioms.loopToHomology (cb.loops j)) from by rw [← hrepr],
      map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul]
  -- smooth-loop representatives of the pinned loops
  have hloops : ∀ j : Fin (2 * genus X), ∃ γ' : ℝ → X,
      _root_.Jacobians.IsClosedSmoothLoop γ' ∧ γ' 0 = x₀ ∧
      ∀ form : HolomorphicOneForm X,
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) γ' =
          developingValue x₀ form
            ((Jacobians.Axioms.loopToPath (cb.loops j) : Path x₀ x₀) :
              C(unitInterval, X)) :=
    fun j => exists_isClosedSmoothLoop_lineIntegral_eq_developingValue x₀
      (Jacobians.Axioms.loopToPath (cb.loops j))
  choose gam hgam_loop hgam0 hgam_val using hloops
  -- the smooth 1-chain
  set c : _root_.Jacobians.Dolbeault.SmoothOneChain X :=
    { n := k + 2 * genus X
      coeff := Fin.append (fun a => E (P a)) (fun j => -(m' j))
      src := fun _ => x₀
      tgt := Fin.append (fun a => P a) (fun _ => x₀)
      path := Fin.append (fun a => _root_.Jacobians.smoothPath x₀ (P a)) (fun j => gam j)
      smooth := by
        intro i
        refine Fin.addCases (motive := fun i =>
            _root_.Jacobians.IsSmoothPath x₀
              (Fin.append (fun a => P a) (fun _ => x₀) i)
              (Fin.append (fun a => _root_.Jacobians.smoothPath x₀ (P a))
                (fun j => gam j) i))
          (fun a => ?_) (fun j => ?_) i
        · simp only [Fin.append_left]
          exact _root_.Jacobians.isSmoothPath_smoothPath x₀ (P a)
        · simp only [Fin.append_right]
          exact ⟨hgam0 j, (hgam_loop j).closed ▸ hgam0 j, (hgam_loop j).cont,
            (hgam_loop j).diff, (hgam_loop j).velCont⟩ } with hc
  have hc_coeff : c.coeff = Fin.append (fun a => E (P a)) (fun j => -(m' j)) := rfl
  have hc_src : c.src = fun _ => x₀ := rfl
  have hc_tgt : c.tgt = Fin.append (fun a => P a) (fun _ => x₀) := rfl
  have hc_path : c.path =
      Fin.append (fun a => _root_.Jacobians.smoothPath x₀ (P a)) (fun j => gam j) := rfl
  -- boundary = the translated divisor
  have hboundary : c.boundary = E := by
    have hbd : c.boundary = ∑ i : Fin (k + 2 * genus X), c.coeff i •
        (Finsupp.single (c.tgt i) (1 : ℤ) - Finsupp.single (c.src i) (1 : ℤ)) := rfl
    rw [hbd, Fin.sum_univ_add]
    have hloop_part : ∑ j : Fin (2 * genus X), c.coeff (Fin.natAdd k j) •
        (Finsupp.single (c.tgt (Fin.natAdd k j)) (1 : ℤ) -
          Finsupp.single (c.src (Fin.natAdd k j)) (1 : ℤ)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hc_tgt, hc_src, Fin.append_right, sub_self, smul_zero]
    have harc_part : ∑ a : Fin k, c.coeff (Fin.castAdd (2 * genus X) a) •
        (Finsupp.single (c.tgt (Fin.castAdd (2 * genus X) a)) (1 : ℤ) -
          Finsupp.single (c.src (Fin.castAdd (2 * genus X) a)) (1 : ℤ)) =
        ∑ a : Fin k, E (P a) •
          (Finsupp.single (P a) (1 : ℤ) - Finsupp.single x₀ (1 : ℤ)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc_tgt, hc_src, hc_coeff, Fin.append_left, Fin.append_left]
    rw [hloop_part, harc_part, add_zero]
    have hsplit : ∑ a : Fin k, E (P a) •
        (Finsupp.single (P a) (1 : ℤ) - Finsupp.single x₀ (1 : ℤ)) =
        (∑ a : Fin k, E (P a) • Finsupp.single (P a) (1 : ℤ)) -
          (∑ a : Fin k, E (P a)) • Finsupp.single x₀ (1 : ℤ) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => smul_sub _ _ _
    rw [hsplit]
    have hT1 : ∑ a : Fin k, E (P a) • Finsupp.single (P a) (1 : ℤ) = E := by
      rw [hreindexF (fun Q => E Q • Finsupp.single Q (1 : ℤ))]
      conv_rhs => rw [← Finsupp.sum_single E]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hT2 : ∑ a : Fin k, E (P a) = 0 := by
      rw [hreindexZ (fun Q => E Q)]
      have hdeg' : Divisor.deg X D = 0 := hdeg
      have hexp := hom_apply_eq_sum_support (X := X) (Divisor.deg X) D
      rw [hdeg'] at hexp
      have hsum : ∑ Q ∈ (FreeAbelianGroup.toFinsupp D).support,
          (FreeAbelianGroup.toFinsupp D) Q • Divisor.deg X (FreeAbelianGroup.of Q) =
          ∑ Q ∈ E.support, E Q := by
        refine Finset.sum_congr (by rw [← hE_toFinsupp]) fun Q _ => ?_
        rw [show Divisor.deg X (FreeAbelianGroup.of Q) = 1 from
          FreeAbelianGroup.lift_apply_of _ _, smul_eq_mul, mul_one, ← hE_toFinsupp]
      rw [hsum] at hexp
      exact hexp.symm
    rw [hT1, hT2, zero_smul, sub_zero]
  -- periods of the bridged basis vanish
  have hper_basis : ∀ i : Fin (genus X), c.period (bridgeKDFormEquiv (b i)) = 0 := by
    intro i
    have hpd : c.period (bridgeKDFormEquiv (b i)) = ∑ l : Fin (k + 2 * genus X),
        (c.coeff l : ℂ) * _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
          (c.path l) := rfl
    rw [hpd, Fin.sum_univ_add]
    have harc : ∑ a : Fin k, (c.coeff (Fin.castAdd (2 * genus X) a) : ℂ) *
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
          (c.path (Fin.castAdd (2 * genus X) a)) = A i := by
      rw [hA_apply i]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc_coeff, hc_path, Fin.append_left, Fin.append_left]
    have hloop : ∑ j : Fin (2 * genus X), (c.coeff (Fin.natAdd k j) : ℂ) *
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
          (c.path (Fin.natAdd k j)) =
        -∑ j : Fin (2 * genus X), (m' j : ℂ) *
          Jacobians.Axioms.periodMapInBasis X x₀ b
            (Jacobians.Axioms.loopToHomology (cb.loops j)) i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc_coeff, hc_path, Fin.append_right, Fin.append_right,
        hgam_val j (b i), ← periodMapInBasis_loopToHomology_apply x₀ (cb.loops j) i]
      push_cast
      ring
    rw [harc, hloop]
    have hAi : A i = ∑ j : Fin (2 * genus X), (m' j : ℂ) *
        Jacobians.Axioms.periodMapInBasis X x₀ b
          (Jacobians.Axioms.loopToHomology (cb.loops j)) i := by
      rw [hexpand, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, zsmul_eq_mul]
    rw [hAi]
    ring
  -- spanning: the bridged basis spans the port form space
  have hspan : Submodule.span ℂ
      (Set.range (fun i : Fin (genus X) => bridgeKDFormEquiv (b i))) = ⊤ := by
    have hrange : Set.range (fun i : Fin (genus X) => bridgeKDFormEquiv (b i)) =
        ⇑(bridgeKDFormEquiv (X := X)).toLinearMap '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr (bridgeKDFormEquiv (X := X)).surjective]
  have hper_all : ∀ α : _root_.Jacobians.HolomorphicOneForms X, c.period α = 0 :=
    fun α => c.period_eq_zero_of_spanning _ hspan hper_basis α
  -- fire the engine and pull the divisor back
  obtain ⟨f, hf⟩ := _root_.Jacobians.Dolbeault.exists_meromorphic_of_zeroPeriodChain'
    (_root_.Jacobians.Dolbeault.chartDiskCover (X := X)) c hper_all
  exact mem_principalDivisors_of_port_div hD0 f (by rw [hf, hboundary, hE])

/-! ## Basis-free variant: T-GEN in place of `AX_PeriodCycleBasis`

The engine adapter above expands the divisor's zero-period homology class
`h` over the **pinned cycle basis** `pinnedCycleBasis x₀`
(`Classical.choice (AX_PeriodCycleBasis x₀)`), producing the cancelling
1-chain's loop part as a `ℤ`-combination of the `2g` basis loops with
coefficients `cb.isBasis.repr h`. That is the ONLY place the
`AX_PeriodCycleBasis` axiom enters the ⊆ engine.

Under **T-GEN** (`AnalyticLoopsGenerateH1 x₀`: analytic-loop classes
`ℤ`-span `H1 X x₀`), the `#198` `AddSubgroup`-span trick
(`AnalyticLoopsGenerateH1.exists_loop`) gives a **single** analytic loop
`γ` with `loopToHomology γ = h` — no cycle basis, no linear-independence,
no `repr`. The cancelling chain's loop part is then a SINGLE smooth loop
representing `γ` with coefficient `-1`. The basis-free adapter consumes
period-lattice membership directly (`divisorPeriodVector x₀ D ∈
periodLatticeInBasis X x₀ (jacobianBasis X)`), which is the basis-free
restatement of `HasZeroPeriodLoopPresentation` (the `jacobianBasis` here
is a basis of *forms*, not cycles — unrelated to `AX_PeriodCycleBasis`).
-/

/-- **Basis-free engine hypothesis.** Every degree-0 divisor whose ambient
period vector lies in the period lattice is principal. This is the
basis-free restatement of `ZeroPeriodChainSolvability`: it consumes
period-lattice membership directly instead of the
`pinnedCycleBasis`-defined `HasZeroPeriodLoopPresentation`. -/
def ZeroPeriodChainSolvabilityLattice (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ D : Divisor X, D ∈ (Divisor.deg X).ker →
    divisorPeriodVector (Classical.arbitrary X) D ∈
      Jacobians.Axioms.periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X) →
    D ∈ PrincipalDivisors X

/-- **E6 (basis-free).** The basis-free engine hypothesis
`ZeroPeriodChainSolvabilityLattice` holds, given **T-GEN**
(`AnalyticLoopsGenerateH1 x₀`) for the engine basepoint `x₀ =
Classical.arbitrary X`. Same Forster §20 engine as
`zeroPeriodChainSolvability_of_engine`, but the cancelling 1-chain's loop
part is a SINGLE analytic-loop generator (`hgen.exists_loop`) with
coefficient `-1`, never a cycle-basis `repr`. No `AX_PeriodCycleBasis`. -/
theorem zeroPeriodChainSolvabilityLattice_of_engine
    (hgen : AnalyticLoopsGenerateH1 (Classical.arbitrary X)) :
    ZeroPeriodChainSolvabilityLattice X := by
  intro D hdeg hmem
  by_cases hD0 : D = 0
  · subst hD0
    exact (PrincipalDivisors X).zero_mem
  classical
  set x₀ : X := Classical.arbitrary X with hx₀
  set b := jacobianBasis X with hb
  set E : X →₀ ℤ := FreeAbelianGroup.equivFinsupp X D with hE
  have hE_toFinsupp : E = FreeAbelianGroup.toFinsupp D := rfl
  set k : ℕ := E.support.card with hk
  set eqv : ↥E.support ≃ Fin k := E.support.equivFin with heqv
  set P : Fin k → X := fun a => ((eqv.symm a : ↥E.support) : X) with hP
  -- reindexing: sums over `Fin k` of point-functions are support sums
  have hreindexV : ∀ g : X → (Fin (genus X) → ℂ),
      ∑ a : Fin k, g (P a) = ∑ Q ∈ E.support, g Q := by
    intro g
    rw [show (∑ a : Fin k, g (P a)) =
        ∑ a : Fin k, (fun s : ↥E.support => g s) (eqv.symm a) from rfl,
      Equiv.sum_comp eqv.symm (fun s : ↥E.support => g (s : X))]
    exact Finset.sum_coe_sort E.support g
  have hreindexZ : ∀ g : X → ℤ,
      ∑ a : Fin k, g (P a) = ∑ Q ∈ E.support, g Q := by
    intro g
    rw [show (∑ a : Fin k, g (P a)) =
        ∑ a : Fin k, (fun s : ↥E.support => g s) (eqv.symm a) from rfl,
      Equiv.sum_comp eqv.symm (fun s : ↥E.support => g (s : X))]
    exact Finset.sum_coe_sort E.support g
  have hreindexF : ∀ g : X → (X →₀ ℤ),
      ∑ a : Fin k, g (P a) = ∑ Q ∈ E.support, g Q := by
    intro g
    rw [show (∑ a : Fin k, g (P a)) =
        ∑ a : Fin k, (fun s : ↥E.support => g s) (eqv.symm a) from rfl,
      Equiv.sum_comp eqv.symm (fun s : ↥E.support => g (s : X))]
    exact Finset.sum_coe_sort E.support g
  -- the comparison loops and their lattice vectors
  set lam : Fin k → Path x₀ x₀ := fun a =>
    (bridgeArcPath x₀ (P a)).trans
      (smoothPathToPath (_root_.Jacobians.smoothPath x₀ (P a))
        (_root_.Jacobians.isSmoothPath_smoothPath x₀ (P a))).symm with hlam
  set va : Fin k → (Fin (genus X) → ℂ) := fun a i =>
    developingValue x₀ (b i) ((lam a : Path x₀ x₀) : C(unitInterval, X)) with hva
  have hva_apply : ∀ a i, va a i =
      developingValue x₀ (b i) ((lam a : Path x₀ x₀) : C(unitInterval, X)) :=
    fun _ _ => rfl
  have hva_mem : ∀ a, va a ∈ Jacobians.Axioms.periodLatticeInBasis X x₀ b := fun a =>
    devVal_loop_mem_periodLatticeInBasis x₀ b (lam a)
  -- the arc-period vector and its lattice membership
  set A : Fin (genus X) → ℂ := fun i => ∑ a : Fin k,
    (E (P a) : ℂ) * _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
      (_root_.Jacobians.smoothPath x₀ (P a)) with hA
  have hA_apply : ∀ i, A i = ∑ a : Fin k,
      (E (P a) : ℂ) * _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
        (_root_.Jacobians.smoothPath x₀ (P a)) := fun _ => rfl
  have hdpv : divisorPeriodVector x₀ D =
      ∑ a : Fin k, E (P a) • Jacobians.Axioms.ofCurveAmbient X x₀ (P a) := by
    rw [hom_apply_eq_sum_support (X := X) (divisorPeriodVector x₀) D]
    have hsum : ∑ Q ∈ (FreeAbelianGroup.toFinsupp D).support,
        (FreeAbelianGroup.toFinsupp D) Q • divisorPeriodVector x₀ (FreeAbelianGroup.of Q) =
        ∑ Q ∈ E.support, E Q • Jacobians.Axioms.ofCurveAmbient X x₀ Q := by
      refine Finset.sum_congr (by rw [← hE_toFinsupp]) fun Q _ => ?_
      rw [divisorPeriodVector_of, ← hE_toFinsupp]
    rw [hsum]
    exact (hreindexV (fun Q => E Q • Jacobians.Axioms.ofCurveAmbient X x₀ Q)).symm
  have hA_eq : A = divisorPeriodVector x₀ D - ∑ a : Fin k, E (P a) • va a := by
    funext i
    rw [hA_apply i, Pi.sub_apply, hdpv, Finset.sum_apply, Finset.sum_apply,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul,
      port_lineIntegral_smoothPath_eq x₀ (P a) i, hva_apply a i]
    ring
  have hA_mem : A ∈ Jacobians.Axioms.periodLatticeInBasis X x₀ b := by
    rw [hA_eq]
    refine sub_mem ?_ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hva_mem a))
    -- basis-FREE: lattice membership of the divisor period vector is the
    -- engine hypothesis `hmem`, not a cycle-basis `repr` expansion.
    exact hmem
  -- BASIS-FREE EXPANSION: `A = periodMapInBasis (loopToHomology h)` for a
  -- SINGLE analytic-loop generator `γ` (T-GEN), in place of a `2g`-term
  -- cycle-basis combination.
  obtain ⟨h, hh⟩ := hA_mem
  obtain ⟨γ, hγ⟩ := hgen.exists_loop h
  have hexpand : A = Jacobians.Axioms.periodMapInBasis X x₀ b
      (Jacobians.Axioms.loopToHomology γ) := by
    rw [← hh, hγ]
  -- a smooth-loop representative of the single generator loop `γ`
  obtain ⟨gam, hgam_loop, hgam0, hgam_val⟩ :=
    exists_isClosedSmoothLoop_lineIntegral_eq_developingValue x₀
      (Jacobians.Axioms.loopToPath γ)
  -- the smooth 1-chain: `k` basepoint arcs + ONE cancelling loop (coeff −1)
  set c : _root_.Jacobians.Dolbeault.SmoothOneChain X :=
    { n := k + 1
      coeff := Fin.append (fun a => E (P a)) (fun _ => (-1 : ℤ))
      src := fun _ => x₀
      tgt := Fin.append (fun a => P a) (fun _ => x₀)
      path := Fin.append (fun a => _root_.Jacobians.smoothPath x₀ (P a)) (fun _ => gam)
      smooth := by
        intro i
        refine Fin.addCases (motive := fun i =>
            _root_.Jacobians.IsSmoothPath x₀
              (Fin.append (fun a => P a) (fun _ => x₀) i)
              (Fin.append (fun a => _root_.Jacobians.smoothPath x₀ (P a))
                (fun _ => gam) i))
          (fun a => ?_) (fun j => ?_) i
        · simp only [Fin.append_left]
          exact _root_.Jacobians.isSmoothPath_smoothPath x₀ (P a)
        · simp only [Fin.append_right]
          exact ⟨hgam0, (hgam_loop).closed ▸ hgam0, (hgam_loop).cont,
            (hgam_loop).diff, (hgam_loop).velCont⟩ } with hc
  have hc_coeff : c.coeff = Fin.append (fun a => E (P a)) (fun _ => (-1 : ℤ)) := rfl
  have hc_src : c.src = fun _ => x₀ := rfl
  have hc_tgt : c.tgt = Fin.append (fun a => P a) (fun _ => x₀) := rfl
  have hc_path : c.path =
      Fin.append (fun a => _root_.Jacobians.smoothPath x₀ (P a)) (fun _ => gam) := rfl
  -- boundary = the translated divisor
  have hboundary : c.boundary = E := by
    have hbd : c.boundary = ∑ i : Fin (k + 1), c.coeff i •
        (Finsupp.single (c.tgt i) (1 : ℤ) - Finsupp.single (c.src i) (1 : ℤ)) := rfl
    rw [hbd, Fin.sum_univ_add]
    have hloop_part : ∑ j : Fin 1, c.coeff (Fin.natAdd k j) •
        (Finsupp.single (c.tgt (Fin.natAdd k j)) (1 : ℤ) -
          Finsupp.single (c.src (Fin.natAdd k j)) (1 : ℤ)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hc_tgt, hc_src, Fin.append_right, sub_self, smul_zero]
    have harc_part : ∑ a : Fin k, c.coeff (Fin.castAdd 1 a) •
        (Finsupp.single (c.tgt (Fin.castAdd 1 a)) (1 : ℤ) -
          Finsupp.single (c.src (Fin.castAdd 1 a)) (1 : ℤ)) =
        ∑ a : Fin k, E (P a) •
          (Finsupp.single (P a) (1 : ℤ) - Finsupp.single x₀ (1 : ℤ)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc_tgt, hc_src, hc_coeff, Fin.append_left, Fin.append_left]
    rw [hloop_part, harc_part, add_zero]
    have hsplit : ∑ a : Fin k, E (P a) •
        (Finsupp.single (P a) (1 : ℤ) - Finsupp.single x₀ (1 : ℤ)) =
        (∑ a : Fin k, E (P a) • Finsupp.single (P a) (1 : ℤ)) -
          (∑ a : Fin k, E (P a)) • Finsupp.single x₀ (1 : ℤ) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => smul_sub _ _ _
    rw [hsplit]
    have hT1 : ∑ a : Fin k, E (P a) • Finsupp.single (P a) (1 : ℤ) = E := by
      rw [hreindexF (fun Q => E Q • Finsupp.single Q (1 : ℤ))]
      conv_rhs => rw [← Finsupp.sum_single E]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hT2 : ∑ a : Fin k, E (P a) = 0 := by
      rw [hreindexZ (fun Q => E Q)]
      have hdeg' : Divisor.deg X D = 0 := hdeg
      have hexp := hom_apply_eq_sum_support (X := X) (Divisor.deg X) D
      rw [hdeg'] at hexp
      have hsum : ∑ Q ∈ (FreeAbelianGroup.toFinsupp D).support,
          (FreeAbelianGroup.toFinsupp D) Q • Divisor.deg X (FreeAbelianGroup.of Q) =
          ∑ Q ∈ E.support, E Q := by
        refine Finset.sum_congr (by rw [← hE_toFinsupp]) fun Q _ => ?_
        rw [show Divisor.deg X (FreeAbelianGroup.of Q) = 1 from
          FreeAbelianGroup.lift_apply_of _ _, smul_eq_mul, mul_one, ← hE_toFinsupp]
      rw [hsum] at hexp
      exact hexp.symm
    rw [hT1, hT2, zero_smul, sub_zero]
  -- periods of the bridged basis vanish
  have hper_basis : ∀ i : Fin (genus X), c.period (bridgeKDFormEquiv (b i)) = 0 := by
    intro i
    have hpd : c.period (bridgeKDFormEquiv (b i)) = ∑ l : Fin (k + 1),
        (c.coeff l : ℂ) * _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
          (c.path l) := rfl
    rw [hpd, Fin.sum_univ_add]
    have harc : ∑ a : Fin k, (c.coeff (Fin.castAdd 1 a) : ℂ) *
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
          (c.path (Fin.castAdd 1 a)) = A i := by
      rw [hA_apply i]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc_coeff, hc_path, Fin.append_left, Fin.append_left]
    have hloop : ∑ j : Fin 1, (c.coeff (Fin.natAdd k j) : ℂ) *
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv (b i))
          (c.path (Fin.natAdd k j)) =
        -(Jacobians.Axioms.periodMapInBasis X x₀ b
            (Jacobians.Axioms.loopToHomology γ) i) := by
      rw [Fin.sum_univ_one]
      rw [hc_coeff, hc_path, Fin.append_right, Fin.append_right,
        hgam_val (b i), ← periodMapInBasis_loopToHomology_apply x₀ γ i]
      push_cast
      ring
    rw [harc, hloop]
    rw [show A i = Jacobians.Axioms.periodMapInBasis X x₀ b
        (Jacobians.Axioms.loopToHomology γ) i from by rw [hexpand]]
    ring
  -- spanning: the bridged basis spans the port form space
  have hspan : Submodule.span ℂ
      (Set.range (fun i : Fin (genus X) => bridgeKDFormEquiv (b i))) = ⊤ := by
    have hrange : Set.range (fun i : Fin (genus X) => bridgeKDFormEquiv (b i)) =
        ⇑(bridgeKDFormEquiv (X := X)).toLinearMap '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr (bridgeKDFormEquiv (X := X)).surjective]
  have hper_all : ∀ α : _root_.Jacobians.HolomorphicOneForms X, c.period α = 0 :=
    fun α => c.period_eq_zero_of_spanning _ hspan hper_basis α
  -- fire the engine and pull the divisor back
  obtain ⟨f, hf⟩ := _root_.Jacobians.Dolbeault.exists_meromorphic_of_zeroPeriodChain'
    (_root_.Jacobians.Dolbeault.chartDiskCover (X := X)) c hper_all
  exact mem_principalDivisors_of_port_div hD0 f (by rw [hf, hboundary, hE])

/-! ## The ⊆ direction of Abel's theorem, unconditional over the engine -/

/-- **Abel ⊆, discharged.** The degree-0 Abel–Jacobi kernel is contained in
the principal divisors: `abel_subset_of_engine` over the discharged
`zeroPeriodChainSolvability_of_engine`. -/
theorem abel_subset :
    (Jacobians.Axioms.abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker ≤ PrincipalDivisors X :=
  abel_subset_of_engine zeroPeriodChainSolvability_of_engine

/-- **Abel ⊆, basis-free.** The degree-0 Abel–Jacobi kernel is contained in
the principal divisors, routing through the basis-free engine
`zeroPeriodChainSolvabilityLattice_of_engine` over **T-GEN**
(`AnalyticLoopsGenerateH1`). The kernel-membership input is unfolded to
period-lattice membership by `divisorPeriodVector_mem_lattice_of_mem_ker`
(itself axiom-free), so the only conditionality is T-GEN — no
`AX_PeriodCycleBasis`. -/
theorem abel_subset_basis_free
    (hgen : AnalyticLoopsGenerateH1 (Classical.arbitrary X)) :
    (Jacobians.Axioms.abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker ≤ PrincipalDivisors X :=
  fun _D hD =>
    zeroPeriodChainSolvabilityLattice_of_engine hgen _ hD.2
      (divisorPeriodVector_mem_lattice_of_mem_ker hD.1 hD.2)

end Jacobians.Bridge
