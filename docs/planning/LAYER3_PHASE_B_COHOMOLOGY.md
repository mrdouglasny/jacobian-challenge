# Layer 3 — Phase B: the cohomology axiom design (Gemini-vetted)

*2026-06-08. The faithful axiomatization for discharging Riemann–Roch + Serre
duality, vetted by Gemini deep-think. Supersedes the "build the O(D) sheaf"
fear from Probe 2: we do NOT build the sheaf — we axiomatize the homological
scaffolding (the LES) directly and **prove** RR from it via the already-proven
Euler-characteristic engine.*

## Gemini verdict (rejected designs)

- **Axiomatize the manifold meromorphic order** (`(X→ℂ)→X→ℤ`): WRONG. Bad domain
  (mero functions don't map to ℂ), and order is *insufficient* — SES exactness at
  a stalk needs the ℂ-structure of the Laurent principal part, not just the integer
  order. Worse, defining `H1 := Sheaf.H 1 (O(D))` hits the **Cartan–Serre/Montel
  finiteness wall**: Mathlib's algebraic `Sheaf.H` has *no path* to
  `FiniteDimensional` — you'd axiomatize finiteness anyway after weeks of homology.
- **Axiomatize the χ-recursion** `χ(D+P)=χ(D)+1`: CIRCULAR — RR *is* the integral of
  that recursion; this hollows out the theorem. (And `SheafCohomologySpec` can't
  prevent vacuity without an actual constructed model.)

## The faithful design — "Axiomatic Cohomology Hybrid"

Axiomatize the standard cohomological scaffolding, wired to the concrete `L(D) =
riemannRochSpace D`; derive RR as a genuine theorem.

1. **`H1coh D`** — a finite-dimensional ℂ-vector space, functorial in `D`
   (the real `H¹(X, O(D))`; replaces the opaque `Axioms.H1`).
2. **`H0 ≅ L(D)`** — already in place (`H0 := riemannRochSpace D`).
3. **The 6-term LES** (the key axiom — the *exact sequence*, NOT the recursion):
   `0 → L(D) → L(D+P) → ℂ_P → H1coh D → H1coh (D+P) → 0` exact (ℂ_P = ℂ, the
   skyscraper at `P`, dim 1). Equivalently a chain of `Function.Exact` ℂ-linear maps.
4. **`finrank ℂ (H1coh 0) = genus X`** (the only dimensional input).
5. **Serre pairing** — `H1coh D × L(K−D) → ℂ` nondegenerate (replaces `AX_SerreDuality`).

## The reductions (theorems over the above)

- **Euler char additive** (PROVEN: `Layer3.eulerChar_additive_of_exact_six`):
  the 6-term LES gives `eulerChar (D+P) = eulerChar D + 1` where
  `eulerChar D := finrank L(D) − finrank (H1coh D)`. *(The recursion is PROVED from
  the LES — not axiomatized. This is the genuine RR proof.)*
- **Riemann–Roch** (`AX_RiemannRoch` ⇒ theorem): induct on `D` over
  `FreeAbelianGroup X` (both `±P` steps via the LES at `(D,D+P)` / `(D−P,D)`),
  base `eulerChar 0 = h⁰(0) − finrank H1coh 0 = 1 − g`. ⇒ `eulerChar D = deg D + 1 − g`.
- **Serre duality** (`AX_SerreDuality` ⇒ theorem): `finrank (H1coh D) = finrank
  L(K−D)` from the nondegenerate pairing (finite-dim ⇒ dual dims equal), wiring the
  existing `h1` to `H1coh`.
- Downstream (`h1_eq_zero_of_deg_gt`, `canonicalDivisor_deg`, Serre vanishing) carry
  over; the existing RiemannRochAPI/SerreDualityAPI re-point to the proved versions.

## Faithfulness / accounting

- **Faithful by design:** the LES + finiteness + Serre pairing are the *standard*
  cohomological facts; the real analytic content (finiteness = Cartan–Serre/Montel;
  the Serre trace = residue theorem) is honestly isolated *as the axioms*, while RR
  is genuinely proved. Boundary is exactly the algebraic-vs-analytic line.
- **Non-vacuity:** the `SheafCohomologySpec` §3 ℙ¹ computations (`h⁰(O(np))=n+1`,
  H¹ vanishing) should be PROVABLE from this set + the existing genus-0 machinery —
  the discriminating check. (Full consistency ultimately wants a constructed ℙ¹/torus
  model; deferred to the endgame.)
- **Net:** `AX_RiemannRoch` + (opaque `H1`) → discharged/replaced by the cleaner
  scaffolding (LES, finiteness-of-`H1coh`, `dim H1(0)=g`, Serre pairing). Count is
  ~neutral; the **win is structural** (RR a genuine theorem; trust boundary descends
  to standard cohomology) — the count win comes when the LES/finiteness themselves
  reduce (period-cluster collapse / real-cohomology endgame).
- **Trap (Gemini):** never axiomatize `order(f)=k`; if local structure is ever
  needed, axiomatize the DVR stalk — but this design avoids it.

Each axiom gets the full vetting protocol + `(NOT VERIFIED)` until cleared.
Vetting: Gemini deep-think 2026-06-08 (design selected + faithfulness-vetted).
