# Abel's theorem, ⊆ direction (Jacobi inversion) — Route A: Forster

*2026-06-07. Discharge plan for the **hard** half of `AX_AbelTheorem`:*
```
ker(abelJacobiDiv X) ⊓ (Divisor.deg X).ker  ⊆  PrincipalDivisors X
```
*i.e. "`u(D)=0` and `deg D=0` ⟹ `D` is principal" (kernel ⇒ principal). This is
the direction the challenge's `ofCurve_inj` actually consumes (see
[`AX_AbelTheorem.md`](AX_AbelTheorem.md) and the split note below). Companion:
[`ABEL_SUBSET_MUMFORD_THETA_ROUTE.md`](ABEL_SUBSET_MUMFORD_THETA_ROUTE.md) (Route B).
The ⊇ (easy) direction is [`ABEL_SUPSET_LIOUVILLE_ROUTE.md`](ABEL_SUPSET_LIOUVILLE_ROUTE.md).*

Reference: Otto Forster, *Lectures on Riemann Surfaces*, §21 (Abel's Theorem),
Thm 21.6–21.8. Griffiths–Harris Ch. 2.

## Strategy in one paragraph

Given a degree-0 divisor `D = D⁺ − D⁻` with `u(D) = 0`, manufacture a meromorphic
function `f` with `div f = D` by integrating a **differential of the third kind**
`ω_D` (only simple poles, residue `+1` on `D⁺`, `−1` on `D⁻`) whose periods all
lie in `2πiℤ`, so that `f := exp(∫ ω_D)` is single-valued. Riemann–Roch + Serre
duality produce `ω_D`; the A-normalized basis from `AX_RiemannBilinear` kills its
A-periods; Riemann reciprocity + the hypothesis `u(D)=0` force its B-periods into
`2πiℤ`.

## Prerequisites (what must land first)

**Shared with Route B:**
- `AX_AnalyticCycleBasis` (symplectic homology basis `{a_j,b_j}`) — axiom, deep.
- `AX_RiemannBilinear` — axiom; supplies the A-normalized holomorphic basis
  `cω` (`∮_{a_i} cω_j = δ_ij`), the B-period matrix `τ ∈ SiegelUpperHalfSpace`,
  and the **reciprocity identity** (the second-and-third-kind variant) used in
  Step 3. *This is the load-bearing classical input of this route.*
- `AX_PeriodLattice` (`Λ` is a full ℤ-lattice) — axiom, tractable (~3–5 days).
- A **meromorphic-1-forms-with-residues** layer (third-kind differentials,
  `res_P`, the residue theorem `∑res = 0`). Partially scaffolded by
  `MeromorphicFunctionField` + Wallace `orderAt`; the residue theorem itself is
  the [residue brief](../deep-think-residue-theorem-route.md) — but see "Residue
  theorem: do we need it?" below; for THIS route we need only third-kind
  *existence* + local Laurent residue, not the global `∑res=0`.

**Route-A-specific (the big ones):**
- `AX_RiemannRoch` — axiom, effort 10. Needed in Step 2 to count sections.
  Its own prerequisite is the sheaf-cohomology LES + Serre finiteness
  (~15K LOC, multi-year). See [`AX_RiemannRoch.md`](AX_RiemannRoch.md).
- `AX_SerreDuality` — axiom, effort 10. Needed in Step 2 to realize the
  cohomology class as a meromorphic 1-form. See [`AX_SerreDuality.md`](AX_SerreDuality.md).

## Recipe (Forster §21)

Notation: `g := genus X`; `{a_j, b_j}` the symplectic basis (`AX_AnalyticCycleBasis`);
`{cω_1,…,cω_g}` the A-normalized holomorphic basis from `AX_RiemannBilinear`
(`∮_{a_i} cω_j = δ_ij`); `u(D) := abelJacobiDiv X D ∈ Jacobian X = ℂ^g/Λ`.

1. **Set-up.** Assume `D` degree-0, `u(D)=0`. Write `D = D⁺ − D⁻`, `deg D⁺ = deg D⁻ = m`.
   Goal: a meromorphic `f` with `div f = D`.

2. **Existence of a third-kind differential `ω_D`** (residues `+1` on `D⁺`, `−1`
   on `D⁻`). Apply `AX_RiemannRoch` + `AX_SerreDuality` to the line bundle
   `𝒪(D⁺+D⁻) ⊗ K_X` to get a meromorphic 1-form with the prescribed simple-pole
   residue pattern. Determined up to a holomorphic 1-form. Forster §21.7;
   Mumford Vol I §II.3 Prop 3.4. *(This is the step that forces RR+Serre.)*

3. **Kill the A-periods.** Set
   `ω̃_D := ω_D − ∑_j (∮_{a_j} ω_D) · cω_j`. Since `∮_{a_i} cω_j = δ_ij`
   (`AX_RiemannBilinear`), `∮_{a_j} ω̃_D = 0` for all `j`.

4. **Force the B-periods into `2πiℤ`.** By Riemann's bilinear reciprocity
   (second-and-third-kind variant, `AX_RiemannBilinear`), the B-periods
   `∮_{b_j} ω̃_D` equal `2πi · (components of u(D))` modulo the lattice. The
   hypothesis `u(D)=0` puts those components in `Λ`, hence each B-period ∈ `2πiℤ`.
   Combined with Step 3 (A-periods = 0 ∈ `2πiℤ`): **all periods of `ω̃_D` lie in
   `2πiℤ`.** *(Correctness note: the condition is `2πiℤ`, not "purely imaginary"
   — `e^{iπ}=−1`. This was a real error in an earlier draft; keep it right.)*

5. **Pick a pole-free basepoint.** Choose `P₀ ∈ X ∖ supp(D)` (cofinite open set;
   `Nonempty` from finite divisor support + density — do **not** use
   `Classical.arbitrary X`, which can land on a pole). Use
   `abelJacobiDivAt X P₀` (the explicit-basepoint variant).

6. **Recover `f`.** `f(P) := exp(∫_{P₀}^P ω̃_D)`. All periods ∈ `2πiℤ` ⇒ the
   integral is well-defined mod `2πiℤ` ⇒ `exp` single-valued on `X ∖ supp(D)`.
   Near `P_i ∈ D⁺`, local expansion `n_i·log(z−z_i) + holo` ⇒ `ord_{P_i}(f)=n_i`;
   likewise `D⁻`. So `f` extends meromorphically with `div f = D`. Hence
   `D ∈ PrincipalDivisors X`. Forster §21.8.

## Lean decomposition (post-prerequisites; the assembly only)

| File | Proves | Depends on |
|------|--------|-----------|
| `ThirdKindDifferential.lean` (~400) | existence of `ω_D` with prescribed simple-pole residues | `AX_RiemannRoch`, `AX_SerreDuality`, meromorphic-forms layer |
| `PeriodNormalization.lean` (~300) | A-periods killed + B-periods ∈ `2πiℤ` from `u(D)=0` | `AX_RiemannBilinear`, `AX_PeriodLattice` |
| `ExpRecovery.lean` (~350) | single-valued `f = exp(∫ω̃_D)`, `div f = D` | period-integral + local Laurent |
| `AbelSubsetForster.lean` (~150) | `ker ⊓ deg-0 ⊆ PrincipalDivisors` (assembles 2–6) | the above + `abelJacobiDivAt` |

**Assembly LOC ≈ 1200**, but gated behind RR + Serre + the meromorphic-forms layer
(collectively the multi-year sheaf-cohomology cluster).

## Residue theorem: do we need it here?

**Not the global `∑res = 0`.** Route A needs only (i) *existence* of a third-kind
differential (from RR+Serre) and (ii) the *local* Laurent residue at each pole
(for the `ord` computation in Step 6). The global residue theorem belongs to the
⊇ direction's classical proof — which we are *bypassing* via Liouville. So the
residue-theorem build is **not** on this route's critical path.

## Honest assessment

The mathematics is completely standard and the assembly is modest (~1200 LOC).
**The entire cost is the prerequisites**: RR + Serre (sheaf cohomology, multi-year)
+ `AX_RiemannBilinear` (form-integration + polygon Stokes) + `AX_AnalyticCycleBasis`
(triangulation). This route is "cheap assembly, astronomically expensive
foundation." Pursue it only as the capstone *after* the sheaf-cohomology cluster
lands — it should not be scheduled ahead of RR/Serre.

## Risk / escalation
- Do **not** attempt Steps 2–4 before `AX_RiemannRoch` **and** `AX_SerreDuality`
  are theorems (or are being used as explicit hypotheses by design).
- If the meromorphic-forms-with-residues layer balloons, note that Route A only
  needs *local* residues, not the global theorem — keep scope tight.
