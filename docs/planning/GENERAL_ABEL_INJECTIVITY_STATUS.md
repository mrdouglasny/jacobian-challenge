# General genus>1 Abel injectivity — status & roadmap

*Living synthesis of the three workstream plans
([`OFCURVE_INJ_DISCHARGE_PLAN`](OFCURVE_INJ_DISCHARGE_PLAN.md),
[`G3_DISCHARGE_PLAN`](G3_DISCHARGE_PLAN.md),
[`HOMOTOPY_INVARIANCE_PLAN`](HOMOTOPY_INVARIANCE_PLAN.md)). Last updated 2026-05-31.*

## The goal

Retire the axiom `AX_ofCurve_inj (P) (0 < genus X) : Injective (ofCurveImpl X P)`
— Buzzard's anti-degeneracy heart — turning it into a derived **theorem** for all
genus>0. (`ofCurveImpl P Q = [ (∫_P^Q ω_i)_i ] ∈ Jacobian X`, a real computed map.)

## Proof architecture (the DAG)

```
                         elliptic_ofCurve_injective ✅  (genus-1 witness, d4f6e82)
                                 │ (validates the contract on a real curve)
GENERAL genus>1:
   ofCurveImpl P₀ injective
        ⟸  basepoint-independence  (HI-4)        ── A: HOMOTOPY INVARIANCE ──┐
              ⟸  loop_integral ∈ Λ  (HI-3)                                    │
                    ⟸  loop integral factors through H₁  (HI-2)              │
                          ⟸  homotopy invariance of ∫  (HI-1) ◄── the core   │
                                ⟸ chart-local Cauchy ✅ + subdivision ✅      │
        ⟸  Abel's theorem  (AX_AbelTheorem, kept axiom)                      │
        ⟸  G3: genus>0 ⇒ (Q₁)−(Q₂) principal → Q₁=Q₂  ── B: GENUS OBSTRUCTION ┘
              ⟸  degree-1 ⇒ genus 0  (C1)
                    ⟸ Wallace conservation ✅ + toP1 (C0) + genus-invariance ✅
              ⟸  PrincipalDivisors = range divHom ✅ (D3)
                    ⟸ MeromorphicFunctionField + divHom ✅ (D1/D2)
```

Two **independent** workstreams (A homotopy invariance, B genus obstruction) meet
at the final assembly. Gemini deep-think (2×) vetted both: (1) G3 needs NO
Riemann–Roch and g≥2 needs the geometric degree-1 argument; (2) basepoint-
independence is EQUIVALENT to homotopy invariance (not weaker) — the reason A is
on the critical path.

## Status table

| Node | Milestone | State | Commit |
|------|-----------|-------|--------|
| — | `elliptic_ofCurve_injective` (genus-1 witness) | ✅ done | d4f6e82 |
| — | E2 unblock (piecewise lift + loop period ∈ Λ) | ✅ done | ad2510e |
| B/D1-2 | `MeromorphicFunctionField` + `divHom` | ✅ done | 9727e7a |
| B/D3 | `PrincipalDivisors := range divHom` (−1 axiom) | ✅ done | c463677 |
| B/C1c | genus biholo-invariance (`genus_eq_of_biholo`) | ✅ done | eb09097 |
| B/C1c | `genus ℙ¹ = 0` | ✅ pre-existing | Line/Genus.lean |
| B/C0 | `toP1` + finite-fiber + nonconstant | ✅ done | eb09097 |
| B/C0 | `toP1_contMDiff` + `mapAnalyticOrderAt = |orderAt|` | ✅ done | 09b8b3e |
| B/C1 | `degreeOne_genus_zero` (degree-1 ⇒ genus 0) | ✅ done | 0767d22 |
| B/G3 | `principal_imp_eq_of_genus_pos` ((Q₁)−(Q₂) principal ⇒ Q₁=Q₂) | ✅ **done** | 0767d22 |
| A | chart-local Cauchy + subdivision | ✅ pre-existing | ContourDeformation, SquareSubdivision |
| A/HI-0 | `canonicalArcIntegral_eq_fixedChart_integral` (single-chart bridge) | ✅ done | 15156b0 |
| A/HI-1 | global homotopy invariance (1a single-chart ∥ 1b telescoping) | 🔄 in flight | — |
| A/HI-2,3 | factor through H₁ ⇒ loop integral ∈ Λ | ⬜ todo | — |
| A/HI-4 | basepoint-independence (5-line) | ⬜ todo | — |
| — | G-assemble: retire `AX_ofCurve_inj` (−1) | ⬜ todo (needs ⊤↔ω `IsManifold.of_le` bridge) | — |

**Workstream B (genus obstruction) is COMPLETE** (0767d22). Only workstream A
(homotopy invariance) + the final assembly remain.

## Axiom ledger

- **Now: 62** project axioms (D3 retired `PrincipalDivisors`, 63→62).
- **On completion:** `AX_ofCurve_inj` retires (−1 ⇒ 61), with NO new axioms added
  (the whole-program mandate: prove all analytic facts). `AX_AbelTheorem` and
  `AX_RiemannRoch` are KEPT (textbook axioms, separate discharge tracks).
- The elliptic witness already depends on NO new axioms (standard-3 + cycle-basis
  axioms, not even `AX_PeriodLattice`).

## Critical path & the two hard cores

The tractable infrastructure is landed. The genuine remaining difficulty is two
multi-step analytic proofs that resist one-shot automation:
1. **C0 order-matching** — `mapAnalyticOrderAt(toP1 f) = |orderAt f|` (Wallace
   local-mapping degree vs meromorphic order, across the ℙ¹ ∞-chart). Route:
   `orderAt_inv` + ∞-chart `z↦z⁻¹` ⇒ `1/f` reduction. *(in flight)*
2. **HI-1 telescoping** — patch chart-local Cauchy over a subdivided homotopy
   square. Standard but bookkeeping-heavy.

Both are "weeks not months"-scale given the infra already in place. Workstreams A
and B are independent and run in parallel; the final assembly needs both.

## Non-degeneracy guarantee (eval)

`ofCurveImpl` is a genuine computed map (`[∫_P^Q ω_i]`), NOT `id` dressed up. The
elliptic witness is a real computation through the period lattice (⊆ c·Λ). Every
de-opaque (`PrincipalDivisors`, `pathIntegralBasepointFunctional`,
`loopIntegralToH1`, `abelJacobiDiv`) replaced an axiom with real content while
keeping the consuming axiom statements (`AX_AbelTheorem`, etc.) verbatim —
checked by `lake build` + kernel `#print axioms` (no `sorryAx`) on each.

**Statement-vetting (2026-06-05).** A Gemini + self-audit pass on the new
declarations found 4 faithful and 1 latent soundness bug — `AX_AbelTheorem`'s
bare-kernel form, fixed to the degree-0 restriction (`ecc8f95`). A focused audit
of the G3 chain (`degreeOne_genus_zero`, `principal_imp_eq_of_genus_pos`)
confirmed it sound: **surjectivity of `toP1 f` onto ℙ¹ is a derived output** of
the locally-constant-on-connected fiber-sum argument (no empty-fiber gap — a
non-image point would force the sum to 0, contradicting global value 1); the
bijective + local-mult-1 ⇒ biholomorphism step uses the genuine IFT local
inverse; `ContMDiff ⊤` over the ℂ-model = holomorphic, so the smoothness
exponent is faithful.
