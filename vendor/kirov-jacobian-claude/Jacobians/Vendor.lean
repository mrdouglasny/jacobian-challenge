/-
Vendor tree — third-party Lean source ported into this repository for adoption.

Currently contains:
* `Jacobians.Vendor.Kirov` — selected modules from `rkirov/jacobian-claude`
  (Apache 2.0). See `Jacobians/Vendor/Kirov/Genus.lean` etc. for per-file
  attribution headers, and `vendor/kirov-jacobian-claude/PROVENANCE.md` for
  full upstream sourcing details.
* `Jacobians.Vendor.Wallace` — Riemann-surface analytic infrastructure from
  `tangentstorm/JacobianChallenge` (MIT). See per-file headers and
  `vendor/wallace-jacobian-challenge/PROVENANCE.md`. All modules sorry-free and
  axiom-free (verified via `#print axioms`).
-/
import Jacobians.Vendor.Kirov
import Jacobians.Vendor.Wallace
