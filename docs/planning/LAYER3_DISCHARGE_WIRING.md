# Layer 3 — discharging AX_RiemannRoch / AX_SerreDuality (Codex-scoped plan)

*2026-06-09. Retire the headline RR/Serre axioms by resting the existing
cohomology API on the Layer-3 `H1coh`. Codex read-only scope verdict: technically
clean (moderate, mechanical), **blocked-pending owner-review of #126** for merge.*

## Import cycle + the break
`LineBundle → Layer3.Cohomology → RiemannRochAPI → Axioms.RiemannRoch/SerreDuality → LineBundle`.
Minimal break: extract `RiemannRochBase` (axiom-free `h0`/`h0_zero`/`riemannRochSpace_finiteDimensional`)
and `LineBundleBasic` (`LineBundle`/`H0`/`canonicalDivisor`/`ofDivisor`); put the Layer-3 core
above those but below the axiom wrappers; then full `LineBundle.lean` imports the Layer-3 core
and sets `H1 := H1coh`.

## De-opaque + discharge
- `def H1 {D} (_L : LineBundle D) := Jacobians.Layer3.H1coh D`; inherit instances from `H1coh`.
- `AX_RiemannRoch` → theorem from `riemannRochL3` (unfold `H0→L(D)`, `H1→H1coh`, `eulerCharL3`).
- `AX_SerreDuality` (equiv form) → theorem from **`serreDuality_equiv`** (NOT `serreDualityL3`,
  which is dimension-only — the equiv needs the equiv axiom).

## Net axioms
Removes 5 (`AX_RiemannRoch`, `AX_SerreDuality`, `Axioms.H1` + its 2 instance axioms); adds 0
(Layer-3 scaffold from #126). Downstream (`riemannRoch`, `canonicalDivisor_deg`, `h0_of_deg_gt`,
`h1_eq_zero_of_deg_gt`, the degree theorem) lose `AX_RiemannRoch`/`AX_SerreDuality`, gain the
4 Layer-3 axioms. `h0_zero` stays standard-3.

## Ordered edits
(1) extract `RiemannRochBase`; (2) extract `LineBundleBasic`; (3) point Layer-3 core at the base;
(4) `Axioms.H1 := H1coh`, inherit instances; (5) `AX_SerreDuality` ← `serreDuality_equiv`;
(6) `AX_RiemannRoch` ← `riemannRochL3`; (7) rewire `RiemannRochAPI`/`SerreDualityAPI`;
(8) `lake build Jacobians` + local `#print axioms`; (9) update `AXIOM_AUDIT.md`. Protected
CI/scripts untouched.

## Gate
**Do not merge before #126 (the Layer-3 axioms) is owner-reviewed** — the `(NOT VERIFIED)`
trust-boundary axioms must clear owner vetting first.
