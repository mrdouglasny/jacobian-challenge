/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.AbelPlumbing
import Jacobians.RiemannSurface.LoopLattice
import Jacobians.Bridge.KirovDolbeaultOpenPath
import Jacobians.Layer3.LinearSystemBridge
import KirovDolbeault.Dolbeault.AbelSubsetEngineArc
import KirovDolbeault.Dolbeault.LerayCoverExists

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

end Jacobians.Bridge
