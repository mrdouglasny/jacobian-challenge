/-
`AX_AbelTheorem`: Abel's theorem on the kernel of the Abel-Jacobi
map on divisors.

**Statement (Lean, refined 2026-04-23).** There exists a ℤ-linear
`abelJacobiDiv : Divisor X →+ Jacobian X` extending the Abel-Jacobi
map on points (via `ofCurveImpl`), and its kernel is exactly the
subgroup of principal divisors:

    AddMonoidHom.ker abelJacobiDiv = PrincipalDivisors X.

## Consequences

* For `g > 0`, `ofCurveImpl X P : X → Jacobian X` is injective. This
  is `AX_ofCurve_inj` — derivable from Abel's full theorem since two
  points give the same Jacobian iff their difference is principal, and
  on a positive-genus curve, a degree-0 principal divisor `P - Q` with
  `P ≠ Q` would contradict the Liouville-like maximum modulus
  principle.
* The image of `abelJacobiDiv` restricted to `Div⁰(X)` (degree-zero
  divisors) is all of `Jacobian X` (Jacobi inversion). Together with
  the kernel statement, this gives `Div⁰(X) / Principal ≃ Jacobian X`
  — the concrete form of the **Jacobian variety as the degree-0
  Picard group** `Pic⁰(X)`.

## Why axiomatized

Route 1 (Riemann theta divisor): gradients of theta functions + Riemann's
theorem on theta zeros. Needs `RiemannTheta` (we have a scaffold in
`Jacobians/AbelianVariety/Theta.lean`) + multivariable complex analysis.

Route 2 (Forster-style residue argument): meromorphic differential
residue calculus on compact Riemann surfaces. Needs meromorphic
function theory + residues + Stokes.

Either route is a substantial independent project.

## History

- 2026-04-23 (A6 in completion plan): promoted from doc-only using the
  `Divisor / PrincipalDivisors / ofCurveImpl` stubs.

See `docs/formalization-plan.md` §7, discharge priority #10;
`docs/completion-plan.md` workstream A6.
Reference: Mumford Vol I §II.3.3–II.3.5; Forster Ch. III.
-/
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.RiemannSurface.LineBundle

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- **Axiom-stub (data).** The Abel-Jacobi map extended linearly from
points to divisors. On a formal combination `∑ n_P · P`, evaluates to
`∑ n_P · ofCurveImpl P₀ P - (∑ n_P) · ofCurveImpl P₀ P₀`; basepoint
`P₀` is chosen via `Classical.arbitrary`. -/
axiom abelJacobiDiv (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ Jacobian X

/-- **Axiom (Abel's theorem).** The kernel of the Abel-Jacobi map on
divisors is exactly the subgroup of principal divisors. -/
axiom AX_AbelTheorem {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (abelJacobiDiv X).ker = PrincipalDivisors X

end Jacobians.Axioms
