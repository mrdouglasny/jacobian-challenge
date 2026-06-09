# Hyperelliptic period sub-track — scope

*2026-06-09. Goal: use the concrete hyperelliptic differentials + Liouville to
de-axiomatize the period structure for the hyperelliptic witnesses, per the
owner's insight ("a holomorphic 1-form is exact iff its periods vanish; construct
an algebraic basis of 1-forms"). Honest scope below: the insight is right and the
forms-side injectivity is tractable; the FULL `AX_PeriodLattice`/`AX_RiemannBilinear`
discharge needs more (the cycles-side / Hodge positivity), even for hyperelliptic.*

## What already EXISTS (usable now)
- **Explicit hyperelliptic differential basis** — `hyperellipticForm H g` = `g(x) dx/y`
  (`ProjectiveCurve/Hyperelliptic/Form.lean:104`); the family `{hyperellipticForm (Xᵏ) :
  0 ≤ k < g}` is real, and **linear independence is PROVED**
  (`Form.lean:417`). *(This is the "algebraic basis of 1-forms" — already done.)*
- **Liouville**, axiom-free: `liouville_compact_complex_manifold`
  (`Axioms/HyperellipticLiouville.lean:119`) — global holomorphic on compact connected ⇒ constant.
- **Period map** `periodMap X x₀ : H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`
  (`RiemannSurface/Periods.lean:35`), via `loopIntegralToH1` (`LoopIntegral.lean:40`);
  `canonicalArcIntegral`/`developingValue` for the path integral; cycle-loop integrability
  is now a theorem (`LoopIntegral.lean:17`).
- `HolomorphicOneForm X` finite-dim is a derived instance (not an axiom),
  `periodLatticeInBasis`, and the concrete `Jacobian = ℂ^g/Λ`.

## The tractable build — (B) forms-side period injectivity via Liouville
**`period_injective` :** the period map `Per : HolomorphicOneForm X → Hom(H₁,ℂ)`
(`ω ↦ (γ ↦ ∫_γ ω)`) is **injective** — i.e. a holomorphic 1-form with all periods
zero is `0`. Realizes the owner's insight; mostly axiom-free.
- Steps: zero periods ⇒ the primitive `f(p) = ∫_{p₀}^p ω` (developing map) is
  well-defined (path-independent) ⇒ `f` holomorphic with `df = ω` ⇒ Liouville ⇒
  `f` constant ⇒ `ω = df = 0`.
- Reuses: `developingValue`/`canonicalArcIntegral` (primitive), the H₁/period
  machinery (path-independence from zero periods), `liouville_compact_complex_manifold`.
- Effort: ~1–2 weeks; the load-bearing lemma is "zero periods ⇒ the developing
  primitive is single-valued + holomorphic." Holds for ANY compact RS (not just
  hyperelliptic), but pairs naturally with the explicit hyperelliptic forms.
- **Payoff:** the period matrix has full ROW rank `g` (the g differentials have
  ℝ-independent period functionals) — a real, concrete reduction.

## The honest limit — (C) full lattice / Riemann bilinear stays gated
`AX_PeriodLattice` (Λ ⊂ ℂ^g is a full-rank `IsZLattice`) ⟺ `P : H₁ → ℂ^g`
(`γ ↦ (∫_γ ω_j)`) injective ⟺ `Im τ ≻ 0` (`AX_RiemannBilinear`). This is the
**cycles side**, strictly stronger than (B):
- A real cycle `γ` with zero *holomorphic* periods has zero *antiholomorphic*
  periods too (conjugation), hence zero in `H¹_dR` — but concluding `γ = 0` needs
  the **de Rham perfect pairing** (Poincaré duality) + the **Hodge decomposition**
  `H¹_dR = H^{1,0} ⊕ H^{0,1}` (dim `g+g=2g`). Equivalently `Im τ ≻ 0` needs the
  **Riemann second bilinear relation** `i∫_X ω∧ω̄ > 0`.
- For hyperelliptic the positivity *fact* is obvious (`i∫|g(x)/y|² dx∧dx̄ > 0`,
  positive density), **but** the MACHINERY is the gap: Mathlib has no manifold
  2-form integration `∫_X ω∧η` and no de Rham/Hodge decomposition, and the bridge
  from `∫ω∧ω̄` to `Im τ` is the Riemann bilinear relation (Stokes). This is the deep
  obstacle the route-comparison flagged — **not** removed by working hyperelliptic.
- So (B) does **not** by itself feed the `#128` engine (`Im τ ≻ 0 ⇒ IsZLattice`);
  the `Im τ ≻ 0` input remains gated.

## Net assessment + recommendation
- **(A) explicit forms — done.** **(B) period injectivity via Liouville — build it:**
  tractable, ~mostly axiom-free, de-axiomatizes the forms-side injectivity and
  showcases the explicit hyperelliptic differentials. A genuine reduction realizing
  the owner's insight.
- **(C) the full `AX_PeriodLattice`/`AX_RiemannBilinear` discharge — gated** on
  manifold 2-form integration + de Rham/Hodge (or the Riemann bilinear positivity
  machinery), even for hyperelliptic. Keep axiomatized; the `#128`/bilinear engines
  reduce it to exactly `Im τ ≻ 0`, which is where the remaining debt sits.
- **Build order:** (B) first (concrete win). Then, if the 2-form-integration
  machinery is later built (or `i∫ω∧ω̄>0` axiomatized as one clean primitive),
  combine with (B) + `#128` to close (C) for hyperelliptic.

Honest framing: this sub-track lands a real, mostly-axiom-free piece (B) and
pins the remaining period debt to a single deep input (manifold 2-form integration
/ Hodge positivity), rather than fully discharging the period cluster.
