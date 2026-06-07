# Zulip announcement draft — "50!" (stream 583336)

Edit freely, then post. Below the line is the ready-to-paste message; above
the line are the supporting facts in case you want to swap details in/out.

## Supporting facts (last day, 55 → 50)

**Headline — Liouville L2 & L3 → theorems (PR #96).** The two deepest remaining
axioms, both now discharged:
- `AX_HyperellipticForm_polynomial_decomposition` (L2)
- `AX_HyperellipticOneForm_eq_form` (L3)

Together: the classical **canonical-differentials theorem** for even-genus
hyperelliptic curves `y²=f(z)`, `deg f = N` even — every holomorphic 1-form is
`c·zᵏ dz/y` with `k < N/2−1`. This backs `genus_HyperellipticEven_eq : g = N/2 − 1`,
and `#print axioms` on that theorem now shows **no Liouville axioms and no
`sorryAx`** — only the standard three + the structural atlas-compat axioms.

Proof route (quotient-free, two-sheet Liouville): σ-anti-invariance of the
chart-transferred coefficient `affCoeff`; an entire single-sheet numerator
`G = affCoeff·√f` (removable at branch points via `OddPartDslope`); polynomial
growth bound at ∞ ⇒ `G` is a polynomial.

**Also landed same window:**
- `AX_pushforward_contMDiff` / `AX_pullback_contMDiff` discharged (#88)
- `PlaneCurve.instT2Space` + topology cluster ported bottom-up to sorry-free
  proofs (standard-3 axioms only), retiring ad-hoc axioms (#94, #90)

---

**50.** 🎉 Active project axioms in jacobian-challenge are down to 50.

The big one this round: **both Liouville axioms (L2 + L3) are now theorems**
(PR #96) — i.e. the canonical-differentials theorem for even hyperelliptic
`y²=f(z)`, `deg f = N` even: every holomorphic 1-form is `c·zᵏ dz/y`. This is the
genuine analytic core behind `genus = N/2 − 1`, and
`#print axioms genus_HyperellipticEven_eq` is now free of any Liouville axiom or
`sorry`.

The argument that worked is quotient-free: σ-anti-invariance of the
chart-transferred coefficient, an entire single-sheet numerator `G = affCoeff·√f`
(removable at branch points), and a polynomial-growth bound at ∞ ⇒ `G`
polynomial — classical Liouville, formalized.

Also discharged in the same stretch: `pushforward/pullback contMDiff` (#88) and
the `PlaneCurve` topology cluster (now bottom-up sorry-free, #94/#90).
