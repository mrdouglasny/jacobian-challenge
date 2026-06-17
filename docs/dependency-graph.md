# Dependency graph — module imports + the headline cone

Two import-level views of the build, generated with Mathlib's `importGraph` (`lake exe graph`).
Artifacts in [`graphs/`](graphs/): `imports-full.{dot,svg}` (whole project) and
`imports-headline-cone.{dot,svg}` (the 24 Buzzard headlines + Albanese categoricity).

This is the **import** graph (module A imports module B) — a sound *over*-approximation of the
true declaration-level dependency. It complements the **axiom** cone
([`axiom-report.txt`](axiom-report.txt), via `scripts/axiom_report.lean`): the axiom report says
*which axioms* a headline rests on; this says *which modules*.

## Regenerate

```bash
lake exe graph --to Jacobians                                   graphs/imports-full.dot
lake exe graph --to "Jacobians.Challenge,Jacobians.UniversalProperty"  graphs/imports-headline-cone.dot
# interactive: pass a .html output; rendered SVG (needs graphviz): dot -Tsvg in.dot -o out.svg
```

## Finding 1 — the project DAG

~225 compiled `Jacobians.*` modules. The interactive/SVG view is for navigation; the structural
facts worth recording:

**Vendored-port coupling.** 16 of our modules import the Kirov Dolbeault port
(`KirovDolbeault.*`), concentrated where you'd expect the analytic engine to attach:

| Directory | port-importing modules |
|---|---|
| `RiemannSurface/` | 5 |
| `Bridge/` | 5 |
| `Layer3/` | 4 |
| `Topology/`, `ProjectiveCurve/` | 1 each |

So the port surface is **localized to the Bridge + Layer-3 + a few RiemannSurface modules**, not
diffused through the tree — good for the independence goal (a future de-vendoring touches ~16
files, mostly bridges). **12 of those 16 are on the headline path** → the port is *load-bearing*
for the headlines (it powers RR/Serre `riemannRochL3` and the Abel-⊆ engine behind `ofCurve_inj`),
not just for off-path extras.

## Finding 2 — the headline cone (the 24 + categoricity)

Transitive **import** closure of `Jacobians.Challenge` (the 24) + `Jacobians.UniversalProperty`
(`isJacobian_unique` / `ofCurve_isJacobian`):

| | modules | share |
|---|---|---|
| **On the headline path** (imported by a headline) | **124** | ~55% |
| **Off the headline path** (provably not imported) | **101** | ~44% |

The off-path 44% is a *sound* statement: those modules are not transitively imported by any
headline, so the 24 + categoricity cannot depend on them. They are **intended extras**, not dead
code:

| Off-path area | modules | what it is |
|---|---|---|
| `ProjectiveCurve/` | 37 | concrete validation curves (ℙ¹, elliptic, plane, much of hyperelliptic) |
| `RiemannSurface/` | 25 | additional RS results beyond the headline path |
| `Topology/` | 15 | topology lemmas used off-path |
| `Axioms/` | 6 | off-headline axioms (intersection form, Plücker, A1, …) |
| `GeneralResults/`, `Extensions/` | 5 each | general lemmas; hyperelliptic-odd/extension validation |
| `Vendor/` | 4 | vendored modules not on the headline path |
| `Layer3/`, `Bridge/`, `AbelianVariety/` | 2 / 1 / 1 | |

**Reading it.** The validation curves (`ProjectiveCurve`, hyperelliptic `Extensions`) are
*deliberately* off the abstract-headline path — they exist to cross-check the general `genus`/
`Jacobian` on concrete instances (see `FAITHFULNESS.md` V.1–V.3), so their being off-cone is the
design working as intended, not waste. A genuine prune pass (à la Kirov) would target the
*intersection* of "off every headline cone" **and** "off every validation/entry-point cone" — not
this set; computing that needs `lake exe unused_transitive_imports` (a follow-up, not done here).

## Caveats

- Import-cone is coarser than the kernel declaration-cone: a module can be imported without a
  headline *using* its contents, so 124 is an upper bound on the true headline dependency.
- The `Jacobians` lib globs submodules, so `--to Jacobians` (the umbrella) is not the full set;
  the true universe is all `Jacobians/**.lean` sources (used as the baseline above).
