/-
# Bridge tree

Bridge files connecting our axiomatized API in `Jacobians/Axioms/` to
the real proofs vendored under `Jacobians/Vendor/`. Each bridge
**retires** an existing axiom by deriving the same fact through the
vendored content.

Currently:

* `Jacobians.Bridge.KirovHolomorphic` — derives
  `FiniteDimensional ℂ (HolomorphicOneForm X)` from Kirov's
  Montel-built `Vendor.Kirov.HolomorphicOneForms` finite-dim instance,
  retiring `AX_FiniteDimOneForms`. Replaces it with two structural
  axioms (`bridgeForm`, `bridgeForm_injective`); the construction's
  smoothness witness is in active development.

* `Jacobians.Bridge.KirovLineIntegral` — replaces
  `pathIntegralBasepointFunctional` and `AX_pathIntegral_local_antiderivative`
  by composing `bridgeForm` with `Vendor.Kirov.lineIntegral` along a
  chosen smooth path. Replaces them with four small structural path-
  selection axioms (`bridgePath` + endpoint/smoothness facts).
  Currently scaffolded; both bridge body and FTC theorem are `sorry`.
-/
import Jacobians.Bridge.KirovHolomorphic
import Jacobians.Bridge.KirovLineIntegral
