# Discharge Liouville L2/L3 — even-genus hyperelliptic (plan-loop)

*2026-06-06. MRD-picked next hard axiom. Issues #35 (L2) + #36 (L3) claimed.
Branch `liouville-l2-l3`. plan-loop source of truth — re-read every cycle.*

## Goal
Discharge the two Class-2d flagged axioms in `Jacobians/Axioms/HyperellipticLiouville.lean`:
- **L2** `AX_HyperellipticForm_polynomial_decomposition` (:215) — a holomorphic 1-form's
  projX-chart coefficient is `g.eval z / √(f z)` for a polynomial `g`, `deg g < N/2−1`.
- **L3** `AX_HyperellipticOneForm_eq_form` (:260) — every such form *equals*
  `hyperellipticForm H g` for some low-degree `g`.

Discharging both **completes** `genus (HyperellipticEvenProj H) = H.f.natDegree/2 − 1`
(the upper bound; lower bound already proven). NO new axiom.

## What's already proven (reuse)
- **Step 4** `differentiable_eq_polynomial_of_growth (n) (g) (Differentiable ℂ g) (C)
  (∀ z, ‖g z‖ ≤ C·(1+‖z‖)^n) : ∃ p, p.natDegree ≤ n ∧ ∀ z, g z = p.eval z`
  (`GeneralResults/EntireGrowth.lean:36`). The growth⇒polynomial core.
- `liouville_compact_complex_manifold` (Liouville L1, proven).
- The `inl_inr` chart-transition cocycle is REAL (`hyperellipticEvenCoeff_cocycle_inl_inr`).
- `hyperellipticForm`, `squareLocalHomeomorph`, the even atlas (`EvenAtlas.lean`), `IsZeroOffChartTarget`.

## Strategy
**L2** = construct the entire extension + bound its growth, then apply Step 4:
- The form coefficient on a projX chart is `c(z)·branch(z)` where `branch = √(f z)`-type.
  Define `g(z) := form.coeff · √(f z)` (the "numerator"). Show:
  - **L2a (branch-point regularity):** `g` extends to an ENTIRE `ℂ → ℂ` (`Differentiable ℂ`) —
    the apparent singularities at the branch points (`f z = 0`, `y = 0`) and chart seams are removable.
  - **L2b (degree-at-∞ growth):** `‖g z‖ ≤ C·(1+‖z‖)^(N/2−2)` from the chart-overlap behaviour at ∞
    (holomorphicity at the point(s) over ∞ bounds the growth).
  - **L2-assemble:** Step 4 ⇒ `g` is a polynomial, `deg ≤ N/2−2 < N/2−1`; rearrange to the axiom's
    `form.coeff q z = g.eval z / squareLocalHomeomorph…(f z)` form.
**L3** = L2 + cocycle propagation:
- **L3a (cocycle inr_inl):** discharge the cross-summand `inr_inl` cocycle via a swap lemma from the
  already-real `inl_inr` (~200–400 LOC per the file note).
- **L3-assemble:** L2 gives `g` matching `ω.coeff` on projX charts; set `ω' := hyperellipticForm H g`;
  `ω.coeff = ω'.coeff` on projX (L2) and projY (cocycle) charts; `IsZeroOffChartTarget` + chart coverage
  ⇒ `ω = ω'`. Handle the `hDeg` (`deg g < N/2−1`) propagation through `hyperellipticForm`'s signature.

## Guardrails
No new axiom. Build-gate each item (`lake env lean` / `lake build`). `#print axioms` the two
discharged theorems + `genus_HyperellipticEven_eq` (no `sorryAx`, no new axiom). Update
`AXIOM_AUDIT.md` counts + by-class breakdown (guard enforces) + README + golden report in the
discharge commit. 58 → 56.

## Plan (status machine)
- [x] S0. Branch + plan + claim #35/#36   status: done
- [x] L0. Scope   status: done   deps: []   note: DONE. KEY: `hyperellipticEvenCoeff_cocycle_inr_inl` is ALREADY a theorem (EvenForm.lean:2165, from inl_inr by symmetry) — both cocycles real, L3a is DONE. projX coeff shape = `g.eval z / squareLocalHomeomorph.symm (f z)` (AffineForm.lean:45). hyperellipticForm: Form.lean:104. Core remaining = L2 (entire extension + growth). Step-4 lemma: `differentiable_eq_polynomial_of_growth (n)(g)(Differentiable)(C)(∀z,‖g z‖≤C(1+‖z‖)^n)`.
- [ ] L2a. entire extension `g` (`Differentiable ℂ`) — branch-point + seam regularity   status: todo   deps: [L0]
- [ ] L2b. polynomial growth bound `‖g z‖ ≤ C·(1+‖z‖)^(N/2−2)` (degree-at-∞)   status: todo   deps: [L0]
- [~] L2. assemble `AX_HyperellipticForm_polynomial_decomposition`   status: in_progress   deps: [L2a, L2b]   note: SUPPORT COMPLETE (20 lemmas). Remaining = ASSEMBLY ONLY (concrete recipe below). Wrappers: `polynomial_decomposition_of_entire_growth (form)(G)(hGdiff:Differentiable ℂ G)(C)(hC:∀z,‖G z‖≤C(1+‖z‖)^(N/2−2))(hReadout:∀ a hpY q _ {z} _, form.coeff q z = G z/√f) → axiom conclusion`; `polynomial_growth_bound_of_tendsto_div_pow (G)(n)(c)(Continuous G)(Tendsto (G z/zⁿ) cocompact (𝓝 c)) → ∃C, growth`. RECIPE: (1) define global `G : ℂ → ℂ` = chart-independent `liouvilleProjXNumerator` on `{z | f z ≠ 0}` (well-def by `liouvilleProjXNumerator_eq_of_projX_overlap`), removable-extended at branch points (`liouvilleBranchPoint_numerator_analyticOn`); (2) `Differentiable ℂ G` by per-point cover (smooth ⇒ projX analyticOn; branch ⇒ branch analyticOn + the w↔z change); (3) `Continuous G` from (2); (4) `Tendsto (G z/z^(N/2−2)) cocompact (𝓝 c)` (∞-chart) ⇒ growth via the growth-wrapper; (5) `hReadout` = `form_coeff_eq_liouvilleProjXNumerator_div` rearranged; (6) apply `polynomial_decomposition_of_entire_growth`. DO NOT add more support.
- [x] L3a. cocycle `inr_inl`   status: done   deps: [L0]   note: ALREADY a theorem (`hyperellipticEvenCoeff_cocycle_inr_inl`, EvenForm.lean:2165) — both cocycle axioms were retired earlier. No work needed.
- [ ] L3. assemble `AX_HyperellipticOneForm_eq_form` (ω = hyperellipticForm H g)   status: todo   deps: [L2, L3a]
- [ ] D. retire both axioms; `#print axioms` verify; reconcile counts 58→56; PR   status: todo   deps: [L2, L3]

## Sequencing
L0 first (scope). L2a/L2b/L3a are independent (parallelizable). L2 needs L2a+L2b; L3 needs L2+L3a;
D needs L2+L3. The entire-extension (L2a) is likely the hardest — get a Gemini-3.1-pro blueprint if it
stalls (as for AX_Period_Triangle's S_trans). Escalate to MRD only for a new axiom / frozen interface.
