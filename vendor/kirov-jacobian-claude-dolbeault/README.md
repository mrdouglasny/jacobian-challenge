# Jacobians Lean API Challenge

[![CI](https://github.com/rkirov/jacobian-claude/actions/workflows/lean.yml/badge.svg)](https://github.com/rkirov/jacobian-claude/actions/workflows/lean.yml)

Lean 4 formalization of Kevin Buzzard's
[Jacobians API challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)
(**v0.4**), pinned to Mathlib commit
[`8e3c989`](https://github.com/leanprover-community/mathlib4/commit/8e3c989104daaa052921bf43de9eef0e1ac9fbf5)
(2026-04-15). Built from scratch, with **zero reliance on future Mathlib**.

The exact v0.4 spec is committed verbatim as [`Jacobian_challenge.lean`](Jacobian_challenge.lean)
(byte-for-byte identical to the gist), and [`ChallengeConformance.lean`](ChallengeConformance.lean)
machine-checks (`lake env lean ChallengeConformance.lean`, exit 0) that this repo's declarations satisfy
**every v0.4 signature exactly** — same names, same statements, no `[Nonempty X]` (v0.3), `𝓘(ℂ, E)`
notation (v0.4), and the universe-polymorphic `Jacobian : Type u` (met by `ULift`-ing the concrete
`Type 0` torus, via [`Jacobians/ULiftManifold.lean`](Jacobians/ULiftManifold.lean) — infrastructure
Mathlib lacks).

## ⚠ Disclaimer — AI-produced, unreviewed by a mathematician

The human author ([rkirov](https://github.com/rkirov)) does not know the mathematics involved
(algebraic geometry, Riemann surfaces, Serre duality, Abel's theorem) and has **not** reviewed the
content. The code, proofs, and documentation were produced by **Claude** (Anthropic's LLM) across many
sessions with light human scoping/steering. The one hard
guarantee is **Lean's kernel**: anything reported as *proven* here is `#print axioms`-clean (no
`sorryAx`). Everything else — proof strategy, prose, mathematical judgment — may be wrong. Have a subject
expert check before relying on anything.

## Status — ~65% (foundations + several walls done; the hard analysis remains)

- **Builds green** (`lake build`, exit 0; **~57k lines of Lean** (`cloc`) across 277 files) with **0 custom axioms** — the
  entire unproved surface is **4 named `sorry`s**, each a true classical theorem absent from Mathlib.
- **Machine-verified (`#print axioms`):** `genus`, `ContMDiff.degree`, the 7 `Jacobian` instances,
  `ofCurve_self`, and the pushforward/pullback functoriality lemmas are sorry-free. The **residue
  theorem** is closed and axiom-clean in two forms — `MeromorphicFunction.deg_div` (Forster Cor. 4.25)
  and the general `∑ Res = 0` for any meromorphic 1-form (`residueTheorem_unconditional`, Miranda §VIII.3).
  The **finiteness theorem** (`exists_cechModel`, Forster §14), the **skyscraper χ-step**
  (`exists_skyscraperLES`, §16), and the **Čech↔Dolbeault comparison**
  (`cechH1_dolbeault_comparison_proof`) are likewise closed and axiom-clean.
- **The marquee deliverables still carry `sorryAx`** — `genus_eq_zero_iff_homeo`, `ofCurve_inj`, and the
  holomorphicity statements are gated on the open walls below. *Matching a signature is not the same as a
  finished proof.*
- **Honest scope:** the remaining ~35% is genuinely-hard greenfield analysis (the Serre §17 residue
  pairing, Abel, surface topology, manifold de Rham) — a multi-session effort.

📊 See **[`docs/DESIGN.md`](docs/DESIGN.md)** for the long-term design choices,
**[`docs/REFERENCES.md`](docs/REFERENCES.md)** for the canonical textbook sources, and
**[`formalization.yaml`](formalization.yaml)** for the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) self-reporting metadata.
For authoritative per-theorem status, prefer the tree itself (`lake build` + `#print axioms`).

### The remaining walls — the keystone first

**The Serre §17 residue pairing (`exists_serreDualityData`) is the chokepoint:** Riemann–Roch — and
through it Abel and the forward headline — is gated on exactly this one `sorry` (finiteness §14, the
skyscraper χ-step §16, and the residue theorem `∑Res = 0` beneath it are all closed). The four walls:

| Wall | Gives | Status |
|---|---|---|
| `exists_serreDualityData` (§17 residue pairing) | Riemann–Roch → the forward headline | residue theorem + finiteness + abstract 17.6/17.9 cores proven; the `H¹(X,Ω)` realization (connecting map) + 17.9 instantiation open |
| `abelJacobi_twoPoint_ne_zero` (#3, Abel) | `ofCurve_inj` | reduction proven; core open |
| `exists_cutSurface` (#7, surface topology) | the Jacobian manifold structure | bilinear relations proven; cut chart open |
| `HasHolomorphicPrimitives` (#1b, manifold de Rham) | the backward headline | S²-simply-connected proven; period slice open |

## Build & verify

```bash
lake exe cache get   # pull the Mathlib olean cache
lake build           # green; expect `declaration uses 'sorry'` warnings (the open walls + sub-lemmas)
lake env lean ChallengeConformance.lean   # exit 0 — verbatim v0.4 conformance
```

Verify any individual result with `#print axioms <decl>` — a `sorryAx` dependency means it is still gated.

## Approach

Missing classical content is kept as **honest `sorry`-bodies** (visible in Lean's `sorry` warnings),
never as typeclass-gated axioms. (An earlier draft tried `HasAbelsTheorem`/`HasResidueTheorem` instances;
reverted — hidden axioms are content-equivalent to `sorry` but read as *proven*.) Real content proven
along the way is preserved; each `sorry` is a single named classical theorem with a Forster/Miranda
pointer, isolated so the unproved surface stays visible and `#print axioms`-auditable.

## Layout

- [`Jacobian_challenge.lean`](Jacobian_challenge.lean) — the verbatim v0.4 spec ·
  [`ChallengeConformance.lean`](ChallengeConformance.lean) — the conformance check.
- [`Jacobians.lean`](Jacobians.lean) + `Jacobians/` — the implementation (171 files):
  `Abel.lean` (divisors, Abel–Jacobi, meromorphic functions), `PeriodLattice.lean`, `RiemannRoch.lean`,
  `Dolbeault/` (Čech/Serre/finiteness), `Discharge/Manifold/` (degree/fibre machinery), `Montel/`,
  `ZLatticeQuotient.lean`, …
- `docs/` — [`DESIGN.md`](docs/DESIGN.md) (long-term design choices) and
  [`REFERENCES.md`](docs/REFERENCES.md) (canonical textbook sources).
- [`formalization.yaml`](formalization.yaml) — repo-root self-reporting metadata.

## References

- Forster, *Lectures on Riemann Surfaces* (GTM 81) — primary.
- Miranda, *Algebraic Curves and Riemann Surfaces*; Griffiths–Harris, *Principles of Algebraic Geometry*.
- Degree/fibre well-definedness infrastructure ported (MIT) from
  [Brsanch/jacobian-lean-challenge](https://github.com/Brsanch/jacobian-lean-challenge); audited
  axiom-clean.
