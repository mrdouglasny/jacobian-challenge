/-
`AX_AbelTheorem`: Abel's theorem on the kernel of the Abel-Jacobi
map on divisors.

**Statement (Lean, refined 2026-04-23; degree-0 restriction added
2026-06-05).** There exists a ℤ-linear
`abelJacobiDiv : Divisor X →+ Jacobian X` extending the Abel-Jacobi
map on points (via `ofCurveImpl`), and on the **degree-zero** divisors
its kernel is exactly the subgroup of principal divisors:

    AddMonoidHom.ker abelJacobiDiv ⊓ AddMonoidHom.ker (Divisor.deg X)
      = PrincipalDivisors X.

The degree-0 restriction is mathematically essential and was missing
before: Abel's theorem is the statement `Div⁰(X) / Principal ≃ Jac(X)`,
and principal divisors are always degree 0 (residue theorem). Without
it the axiom is FALSE — `abelJacobiDiv` sends the basepoint divisor
`(arbitrary)` to `0` (basepoint normalization, `AX_ofCurve_self`), so
that degree-1 divisor sits in the bare kernel but is not principal.
(Caught 2026-06-05 by statement-vetting after `PrincipalDivisors` was
de-opaqued to `range divHom`, which made the bare-kernel form a latent
inconsistency.) All consumers feed only degree-0 divisors (differences
`(Q₁) − (Q₂)`), so the restriction loses nothing.

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
  `Divisor / PrincipalDivisors / ofCurveImpl` layer.

See `docs/formalization-plan.md` §7, discharge priority #10;
`docs/completion-plan.md` workstream A6.
Reference: Mumford Vol I §II.3.3–II.3.5; Forster Ch. III.
-/
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.RiemannSurface.MeromorphicFunctionField

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- The Abel-Jacobi map extended linearly from
points to divisors. On a formal combination `∑ n_P · P`, evaluates to
`∑ n_P · ofCurveImpl P₀ P - (∑ n_P) · ofCurveImpl P₀ P₀`; basepoint
`P₀` is chosen via `Classical.arbitrary`. -/
noncomputable def abelJacobiDiv (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ Jacobian X :=
  FreeAbelianGroup.lift (fun P => ofCurveImpl X (Classical.arbitrary X) P)

/-- **Axiom (Abel's theorem).** The kernel of the Abel-Jacobi map on
divisors is exactly the subgroup of principal divisors. -/
axiom AX_AbelTheorem {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (abelJacobiDiv X).ker ⊓ (Divisor.deg X).ker = PrincipalDivisors X

end Jacobians.Axioms
