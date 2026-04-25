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

These modules are present in the build but not yet wired into the main
`Jacobians.*` tree. Adoption work — replacing `Axioms/FiniteDimOneForms.lean`
and friends with the real Montel-derived facts — is staged separately.
-/
import Jacobians.Vendor.Kirov.Genus
import Jacobians.Vendor.Kirov.Montel
import Jacobians.Vendor.Kirov.HolomorphicForms
