# Object contracts

One card per **constructed object** (not per theorem). A contract lets a
reviewer judge whether the object is the right one and where it is *proven*
vs *asserted* — **without reading any Lean proof**. See
[`../validation-plan.md`](../validation-plan.md) §4 for the rationale.

## Format

Each card is a markdown file with a YAML front-block and a prose reader's
guide. Fields:

| Field | Meaning |
|-------|---------|
| `object` | the Lean declaration name (short) |
| `informal` | one-paragraph plain-English description in textbook language |
| `sources` | textbook citations with chapter/section/theorem numbers |
| `lean` | the Lean `name`, `signature`, `body` (signature only — the appendix) |
| `characterization` | the informal "what must be true" — the defining/known properties as `id`'d claims, including at least one **anti-degeneracy** clause (what would make it the wrong/hack object) |
| `known_values` | the **test matrix**: each row is `instance → expected → theorem → status → axiom_deps`. This is differential testing for mathematics. |
| `well_definedness` | the instance/fact the definition silently relies on (e.g. finite-dimensionality, without which `finrank ≡ 0`) |
| `anti_degeneracy` | `history` of any real degeneracy bug + the `current_guard` that excludes it |
| `status` | one-line summary of where it's validated |

## The `status` vocabulary (the honesty surface)

Every `known_values` cell — and the object overall — is in exactly one
state. These are computed from `#print axioms` on the cell's theorem, so
they cannot be fudged:

- **`PROVEN_CORE_AXIOMS`** — depends only on Lean's `propext`,
  `Classical.choice`, `Quot.sound`. Fully from Mathlib. The gold standard;
  this validates the *definition mechanism*, not just the value.
- **`proven_via_axiom`** — the value is correct but is obtained by
  *assuming* a named axiom (e.g. the value 0 via uniformization rather
  than by computing `dim H⁰(Ω¹)`). Validates API-consistency, not the
  definition.
- **`proven_mod_axioms`** — correct value, reduced to a named axiom set.
  Read as "reduced to those inputs".
- **`sorry`** — stated, not proven.

The invariant a validation harness enforces: **no cell is silently in a
fourth state** — "asserted, looks fine, never checked".

## How a cell's status is checked

```bash
lake env lean scripts/axiom_report.lean > docs/axiom-report.txt
```

`sorryAx` in any trace ⇒ a hidden sorry (fail). An empty axiom list ⇒
`PROVEN_CORE_AXIOMS`. A non-empty named list ⇒ `proven_mod_axioms` /
`proven_via_axiom` (the deps are listed in the cell).

## Cards

- [`genus.md`](genus.md) — prototype. Validated on `Elliptic` (core
  axioms); other cells route through axioms.
- [`ofCurve.md`](ofCurve.md) — the Abel–Jacobi map. Records the
  2026-05-31 experiment finding that its anti-hack property `ofCurve_inj`
  is **opaque-blocked** (unprovable from the current definition).

## Backlog (objects still needing cards)

`Jacobian`, `pushforward` / `pullback`, `HyperellipticEvenProj`,
`Elliptic`, the period lattice (`periodLatticeInBasis`).
