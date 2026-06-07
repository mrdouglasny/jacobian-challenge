# Mσ — σ-anti-invariance `ι*ω = −ω` (plan-loop) — the core of Liouville L2

*2026-06-07. MRD greenlit "pursue Mσ now" (the central hardest L2 milestone).
This is the status-machine for the workstream described in
`docs/Msigma-codex-handoff.md` + `docs/genus-L2-execution-roadmap.md`. plan-loop
source of truth — re-read every cycle. Branch `liouville-l2-l3`.*

## Goal
Prove `pullbackInvolution_eq_neg : pullbackInvolution H ω = -ω` (σ-anti-invariance
of holomorphic 1-forms). This discharges the L2/P1 reduction
`form.coeff qSame z = −form.coeff qOpp z` (sheet-swap helper
`liouvilleProjXNumerator_eq_of_neg_coeff_neg_branch` already landed, 4a02267),
unblocking the Differentiable-G blueprint → L2 → L3 → axiom count 58→56.

## Already done (reuse)
- **Mσ.1/Mσ.2**: involution σ on the surface + `ContMDiff` — DONE
  (`Involution.lean`, axiom-free). `hyperellipticEvenInvol_mk` (σ⟦p⟧=⟦involPre p⟧).
- **This session (L2-side, reusable for Mσ.4)**: removable-singularity
  architecture + verified Mathlib names
  (`docs/planning/L2_DIFFERENTIABLE_G_BLUEPRINT.md`); P2 isolated roots
  (`eventually_eval_ne_zero_nhdsWithin`, 1fd792e); growth wrappers
  (`polynomial_growth_bound_of_tendsto_div_pow`,
  `differentiable_eq_polynomial_of_growth`); sheet-swap helper (4a02267).
- Sub-plans: Mσ.3 → `docs/Msigma3-codex-plan.md` (executable, A_q/B_q uniform
  formula + 3 submodule obligations). Mσ.4 proof sketch → handoff §Mσ.4.

## Guardrails
No new axiom (the whole point). `#print axioms`-clean (core 3 + the already-scoped
even-genus footprint: cross-summand compat + affine-IFT helper — NO new). Build-gate
each item (`lake env lean` / `lake build`). Do NOT introduce/consume axiomatized
`pullbackOneForm`/`pushforwardOneForm` — define the pullback concretely. Escalate to
MRD only for a new axiom / frozen-interface change.

## Plan (status machine)
- [x] Mσ.1/Mσ.2. σ + ContMDiff   status: done   note: Involution.lean, axiom-free.
- [ ] Mσ.3. concrete `pullbackInvolution : HolomorphicOneForm →ₗ[ℂ] HolomorphicOneForm`   status: todo   deps: [Mσ.2]   note: per `docs/Msigma3-codex-plan.md`. Uniform coeff `form.coeff(σq, A_q z)·B_q z` (A_q=σ-chart-rep, B_q=its fderiv; =id/1 on projX). 3 obligations: (1) analyticOn each target, (2) cotangent cocycle / chain-rule (~120–200 LOC, heaviest), (3) zero-off-target. Plus `pullbackInvolutionCoeff_projX` (=form.coeff(σq) on smooth-Y) for Mσ.4. CHART-BOOKKEEPING — dispatched to Codex.
- [ ] Mσ.4. `sigma_invariant_form_eq_zero (η) (hinv : pullbackInvolution H η = η) : η = 0`   status: todo   deps: [Mσ.3]   note: direct-Liouville core (handoff §Mσ.4). 4 steps: (1) σ-invariance ⇒ coeff is single-valued `c(x)` on x alone; (2) `c` entire — analytic off {f=0} + removable singularity at branch points (REUSES L2_DIFFERENTIABLE_G_BLUEPRINT removable-sing + P2 isolated roots); (3) `c=O(1/x²)` at the two ∞ points; (4) Liouville ⇒ c≡0 (`differentiable_eq_polynomial_of_growth` n=0) ⇒ η=0 (`ext_of_coeff`). REUSES this session's blueprint heavily — I take this.
- [ ] Mσ.5. `pullbackInvolution_eq_neg (ω) : pullbackInvolution H ω = -ω`   status: todo   deps: [Mσ.4]   note: short corollary. η:=ω+σ*ω is σ-invariant (σ* involutive from `hyperellipticEvenInvol_invol`) ⇒ η=0 by Mσ.4 ⇒ σ*ω=−ω. First prove `pullbackInvolution` involutive (pointwise).
- [ ] L2payoff. close L2/P1 with Mσ.5 ⇒ flip `AX_HyperellipticForm_polynomial_decomposition`   status: todo   deps: [Mσ.5]   note: feed `pullbackInvolution_eq_neg` into the P1 sheet-swap goal, then P1→P3→P4 (Differentiable G) per the blueprint + growth ⇒ axiom→theorem.
- [ ] L3. `AX_HyperellipticOneForm_eq_form`   status: todo   deps: [L2payoff]   note: cocycle propagation (L3a already a theorem) per `genus-L2-L3-discharge-plan.md`.
- [ ] D. retire both axioms; #print axioms; reconcile 58→56; PR   status: todo   deps: [L2payoff, L3]

## Sequencing
Mσ.3 (Codex, chart-bookkeeping) → Mσ.4 (me, reuses blueprint) → Mσ.5 (short) →
L2payoff → L3 → D. Mσ.4's removable-singularity step is exactly the L2
Differentiable-G blueprint — build the shared removable-sing lemma once, reuse.
