/-
Vendored selection from `rkirov/jacobian-claude` (Apache 2.0).
Original commit: 7ce9e2e8 (2026-04-24).
See per-file headers below for attribution and modification notices.

Currently vendored:
* `Genus`              — `genus X := finrank ℂ (HolomorphicOneForms X)` and the
                         `HolomorphicOneForms` definition (cotangent-bundle sections).
* `Montel.*`           — Montel / Arzelà–Ascoli compactness path for holomorphic
                         1-forms on a compact connected complex 1-manifold
                         (~3,400 LOC; one structural sorry on closed-ball compactness).
* `HolomorphicForms`   — `FiniteDimensional ℂ (HolomorphicOneForms X)` from Montel
                         compactness, plus pullback/pushforward functoriality on forms.
* `LineIntegral`       — `pathSpeed`, `lineIntegral`, linearity (add/smul/neg/const),
                         path reversal, concatenation, and `pathSpeed_comp_eq_mfderiv`
                         (chart-local chain rule). 602 LOC, **sorry-free**.
                         Starting point for retiring `pathIntegralBasepointFunctional`
                         and `loopIntegralToH1` from `Axioms/AbelJacobiMap.lean`.
* `ChartedSpaceOfLocalHomeomorph` — extends Mathlib's `IsLocalHomeomorph`
                         namespace with a constructor for `ChartedSpace` from
                         a local homeomorphism (helper for `ZLatticeQuotient`).
                         55 LOC, sorry-free.
* `ZLatticeQuotient`   — quotient `V ⧸ Λ` for `Λ : Submodule ℤ V` with
                         `[IsZLattice ℝ Λ]`: covering-map structure,
                         `ChartedSpace` and `LieAddGroup` instance transfer.
                         740 LOC, **sorry-free**. Candidate to replace the
                         `ULift`-transfer workaround in
                         `Jacobians/Jacobian/Construction.lean`.

These modules are present in the build but not yet wired into the main
`Jacobians.*` tree. Adoption work is staged via bridge files in
`Jacobians/Bridge/` (e.g. `KirovHolomorphic.lean`).
-/
import Jacobians.Vendor.Kirov.Genus
import Jacobians.Vendor.Kirov.Montel
import Jacobians.Vendor.Kirov.HolomorphicForms
import Jacobians.Vendor.Kirov.LineIntegral
import Jacobians.Vendor.Kirov.ChartedSpaceOfLocalHomeomorph
import Jacobians.Vendor.Kirov.ZLatticeQuotient
