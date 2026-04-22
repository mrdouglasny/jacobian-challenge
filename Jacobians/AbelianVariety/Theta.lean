/-
Riemann theta function on `ℂ^g × 𝔥_g`.

Defined as the sum

    ϑ(z, τ) = ∑_{n ∈ ℤ^g} exp( π i · nᵀ τ n + 2π i · nᵀ z )

over the free ℤ-module `Fin g → ℤ`, where τ is a point of the Siegel upper
half space. The positive-definite imaginary part of τ gives a Gaussian-like
decay of the summands in the `ℓ² ℝ^g` norm of `n`, which makes the sum
absolutely convergent on compact subsets of `ℂ^g × 𝔥_g`.

This module supplies the definition and headers for the three canonical
properties, with TODO stubs:

* **Summability** — `Summable` on compact sets in `(z, τ)`.
* **Analyticity in `z`** — `AnalyticOn ℂ (RiemannTheta · τ) univ` for each `τ`.
* **Quasi-periodicity** — for `m, n ∈ ℤ^g`:
    `ϑ(z + m + τ · n, τ) = exp(- π i · nᵀ τ n - 2π i · nᵀ z) · ϑ(z, τ)`.

Not on the critical path for Buzzard's 24 sorries — the quotient `V/Λ`
structure that delivers the 7 Jacobian-side instances is already in
`ComplexTorus.lean` and does not require `RiemannTheta`. But the theta
series is load-bearing for `AX_AbelTheorem` (via Riemann's theorem on
the theta divisor) and the broader Mumford programme.

See `docs/formalization-plan.md` §3.4.
-/
import Jacobians.AbelianVariety.Siegel

namespace Jacobians.AbelianVariety

open Complex Matrix
open scoped BigOperators

variable {g : ℕ}

/-- Cast a ℤ-vector to a ℂ-vector componentwise. Auxiliary for the theta series. -/
@[simp] noncomputable def intVecToC (n : Fin g → ℤ) : Fin g → ℂ :=
  fun i => (n i : ℂ)

/-- The summand of the Riemann theta series at lattice index `n`:

    exp( π i · nᵀ τ n + 2π i · nᵀ z ).
-/
noncomputable def thetaSummand (z : Fin g → ℂ) (τ : SiegelUpperHalfSpace g)
    (n : Fin g → ℤ) : ℂ :=
  let nC := intVecToC n
  Complex.exp ((Real.pi : ℂ) * I * dotProduct nC (τ.val *ᵥ nC) +
               2 * (Real.pi : ℂ) * I * dotProduct nC z)

/-- The Riemann theta function `ϑ(z, τ)`. -/
noncomputable def RiemannTheta (z : Fin g → ℂ) (τ : SiegelUpperHalfSpace g) : ℂ :=
  ∑' (n : Fin g → ℤ), thetaSummand z τ n

namespace RiemannTheta

/-! ### Summability

The imaginary part of `τ` is positive definite, so `Im (nᵀ τ n) = nᵀ (Im τ) n`
is bounded below by `c · ‖n‖²` for some `c > 0` (smallest eigenvalue of
`Im τ`). This gives `|thetaSummand z τ n| ≤ exp(-π c ‖n‖² + 2π · (linear term in n))`,
a super-exponential decay in `‖n‖`, hence summable.

Summability on compacta in `(z, τ)`: let `(z, τ)` range over a compact set;
then `Im τ` ranges over compact in the open pos-def cone, so its smallest
eigenvalue has a uniform positive lower bound. Combined with boundedness
of `z`, the Gaussian bound holds uniformly.
-/

-- TODO (summable): `Summable (fun n => thetaSummand z τ n)` for each `(z, τ)`.
--   Strategy: prove `fun n => ‖thetaSummand z τ n‖ ≤ exp(-c · ‖n‖² + b · ‖n‖)`,
--   then `Summable.of_nonneg_of_le` against a product of single-variable
--   Gaussian sums (which are summable by `Summable.summable_prod` style
--   reasoning + `Real.summable_pow_mul_exp_neg_nat_mul_sq` or similar).

-- TODO (summable_on_compact): strengthen to a `LocallyUniformlyOn` summable
--   result, using pos-def imaginary part being an open condition with uniform
--   bounds on compact sub-intervals.

/-! ### Analyticity

Each summand is an entire function of `z` (exponential of an affine function).
`∑'` of analytic functions summing absolutely and locally uniformly is
analytic. Mathlib's `AnalyticOn.tsum` or similar should discharge this once
summability is available.
-/

-- TODO (analytic_in_z): `AnalyticOn ℂ (fun z => RiemannTheta z τ) Set.univ`.

/-! ### Quasi-periodicity

The two lattice generators act differently:

* For `m ∈ ℤ^g`: `ϑ(z + m, τ) = ϑ(z, τ)` (periodic in the integer shift).
* For `n ∈ ℤ^g`: `ϑ(z + τ · n, τ) = exp(- π i · nᵀ τ n - 2π i · nᵀ z) · ϑ(z, τ)`.

The combined form captures both: reindex the summation by `n' := n' + n` in
the `τ`-shift case; the exponential factor is exactly what the reindex
produces.
-/

-- TODO (periodic_integer_shift): for `m : Fin g → ℤ`,
--   `RiemannTheta (z + intVecToC m) τ = RiemannTheta z τ`.

-- TODO (quasi_tau_shift): for `n : Fin g → ℤ`,
--   let `nC := intVecToC n`; then
--   `RiemannTheta (z + τ.val *ᵥ nC) τ
--     = Complex.exp (- (Real.pi : ℂ) * I * dotProduct nC (τ.val *ᵥ nC)
--                    - 2 * (Real.pi : ℂ) * I * dotProduct nC z)
--       * RiemannTheta z τ`.

/-! ### Heat equation (Mumford Vol I §I.2, g = 1)

A separate identity connecting `∂ϑ/∂τ` and the second spatial derivative `∂²ϑ/∂z²`.
Not on the critical path for the 24 Challenge sorries; included for
completeness of the theta foundations.
-/

-- TODO (heat): genus-1 heat equation `∂τ ϑ = (1 / (4π i)) ∂²z ϑ`. Skip for now.

end RiemannTheta

end Jacobians.AbelianVariety
