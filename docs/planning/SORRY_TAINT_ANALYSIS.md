# Transitive sorry-taint of the Buzzard challenge

**Question.** `#print axioms` on the challenge headlines shows **0 `sorryAx`** — but
that treats every axiom as a trusted terminal. An axiom is a *placeholder for a
future proof*; if its intended discharge would route through a current `sorry`,
that sorry is real and **propagates transitively through the axiom** to every
result depending on it (the latent #108 pattern). This doc does the honest
propagation: trace each challenge axiom → its discharge plan → does it need a
`sorry`?

## Method — taint classification

Each axiom is classified by its discharge plan's **Route** + **Blocked by**:
- **R — reduces to RR/Serre** (the *accepted* terminal; its further discharge is
  the separate adelic challenge, #103, whose sorries live behind the API wall).
- **I — needs-infra** (hard, not in Mathlib — but **no current sorry**: a
  research-grade axiom, clean in the taint sense).
- **C — provable-from-other-axioms** (clean iff its axiom deps are clean).
- **M / textbook** (mathlib-now / port-a-textbook-theorem — clean, terminal).
- **T — sorry-tainted** (its only known discharge routes through a current stray
  `sorry`, i.e. *not* the accepted RR/Serre adelic sorries).

A result is *truly* clean iff it depends only on {R, I, C-over-clean, M}. A **T**
anywhere in its transitive cone taints it.

## The core-challenge dependency DAG (from the discharge plans)

No axiom's "Blocked by" names a current `sorry` — every link is another **axiom**
or "needs Mathlib infra." The core chain:

```
Jacobian / ofCurve / pushforward / pullback
  └─ AX_PeriodLattice (C) ─ Blocked by → AX_RiemannBilinear (I)
       └─ AX_RiemannBilinear (I) ─ Hodge-norm + polygon-Stokes infra [no sorry]
            └─ AX_AnalyticCycleBasis (I) ─ 4g-gon topology [no sorry]
                 └─ AX_IntersectionForm_{alternating,perfect} (I) ─ intersection theory [no sorry]
  ├─ instPeriodLatticeDiscrete (C) → AX_RiemannBilinear, AX_PeriodLattice
  ├─ functoriality: AX_pushforward/pullback_contMDiff (C) → *_Ambient_preserves_lattice (I),
  │     pushforwardOneForm (I) [trace-map API infra; no sorry]
  └─ AX_AbelTheorem ─ ⊇ via Liouville (clean, no residue) │ ⊆ via Forster/Mumford → RR/Serre (R)
```

Everything bottoms out at **(I) needs-infra research axioms** (4g-gon topology,
Hodge/Stokes, intersection theory, trace-map API — all hard, **none a sorry**) and
the **(R) RR/Serre terminal** (→ adelic, the accepted separate challenge).

## Per-axiom classification (challenge-relevant + transitive deps)

| Axiom | Route | Taint |
|-------|-------|-------|
| `AX_RiemannRoch`, `AX_SerreDuality` | reduce to adelic anchor | **R** (accepted terminal) |
| `AX_AbelTheorem` | ⊇ Liouville / ⊆ RR-Serre | **R** |
| `AX_genus_eq_zero_iff_homeo`, `AX_ofCurve_inj`, `AX_curve_generates_jacobian` | → RR/Serre | **R** |
| `AX_PeriodLattice`, `instPeriodLatticeDiscrete` | → `AX_RiemannBilinear` | **C → I** |
| `AX_pushforward/pullback_contMDiff` | → `*_Ambient_preserves_lattice` | **C → I** |
| `AX_RiemannBilinear` | Hodge + polygon-Stokes | **I** (no sorry) |
| `AX_AnalyticCycleBasis` | 4g-gon topology | **I** (no sorry) |
| `AX_IntersectionForm_*`, `intersectionForm` | intersection theory | **I** (no sorry) |
| `*_Ambient_preserves_lattice`, `pushforwardOneForm`, `AX_pushforwardOneForm_id/comp` | trace-map API infra | **I** (no sorry) |
| `AX_ofCurve_contMDiff`, `AX_pushforward_pullback` | provable-from-axioms / textbook | **C / textbook** |
| `AX_Hyperelliptic_evenEquiv`, `AX_Hyperelliptic_oddEquiv` | parity-dispatch homeomorphism | **C** (equiv construction, clean) |

## The one tainted axiom — and it is *off* the core path

- **`AX_Hyperelliptic_genus` — T (sorry-tainted).** Its discharge routes through
  `genus_HyperellipticOdd_eq`, a `:= by sorry` stub in `Extensions/Hyperelliptic.lean`
  (exactly the #108 catch, which we *rejected* for this reason). But it feeds only
  the **hyperelliptic-genus demonstration**, *not* `Jacobian`/`ofCurve` — consistent
  with "hyperelliptic odd is not required for the challenge." It must stay tainted
  (an axiom) until the odd genus is genuinely proven; it must never be dragged into
  a core headline.

## Conclusion

**The core Buzzard challenge (+ Albanese) is transitively sorry-clean.** Every
challenge axiom's intended discharge routes through other axioms → needs-infra
research axioms (no sorry) or the accepted RR/Serre terminal — **never through a
stray sorry**. The only `T` is `AX_Hyperelliptic_genus`, which is a demonstration,
off the core path.

So the reduction holds in the strong sense the project wants:

> **Buzzard's challenge = {this axiom table} + {the RR/Serre anchor}**, with the
> transitive taint analysis confirming no hidden sorry leaks into the core.

The remaining honesty burden is exactly the (I) and (R) frontier: the needs-infra
research axioms and the RR/Serre adelic discharge — the legitimate open challenges,
none masquerading as done.
