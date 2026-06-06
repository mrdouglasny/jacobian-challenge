# Kirov re-scan — what's worth borrowing from the *current* `jacobian-claude`

**Date:** 2026-06-04
**Scope:** `rkirov/jacobian-claude` as checked out at `~/Documents/GitHub/jacobian-claude`
(HEAD `765652b`, README self-reports "~60%", 34k lines / 168 `.lean` files, 0 custom
axioms, ~12 `sorry`s).
**Context:** We already vendored ~5,600 LOC from Kirov's *April* state (Montel,
HolomorphicForms, LineIntegral, ZLatticeQuotient, ChartedSpaceOfLocalHomeomorph, Genus —
see [`cross-repo-adoption.md`](cross-repo-adoption.md)). This is a re-scan of what is
**new and genuinely proven** since, under the standing rule: **we vendor proven
(sorry-free) material only — no sorries.**

---

## TL;DR

The current Kirov repo is far larger than what we took, but the new bulk falls into two
camps:

1. **A genuinely-new, sorry-free *proven* result: the residue theorem
   `MeromorphicFunction.deg_div` — "every principal divisor has degree 0"
   (`deg (div f) = 0`).** Closed in commit `e826fb4` by wiring it to a ~15k-line
   proper-map-degree / conservation-of-number (Hurwitz) engine that is **sorry-free in
   code** across its entire transitive chain. This is the only new high-value *proven*
   asset.

2. **The Dolbeault / Čech-finiteness / Serre-duality / Riemann–Roch tower (~50 files in
   `Dolbeault/`)** — aimed exactly at our `AX_RiemannRoch` + `AX_SerreDuality`, but it is
   **heavily `sorry`-laden scaffolding** (the big sorry counts live here:
   `CechFinitenessWiring` 17, `DolbeaultComparisonProof` 16, `CechDiskAcyclicAssembly` 16,
   `CohomologicalRR` 14, …). Excluded by the no-sorries rule. **Watch, don't borrow.**

**Recommendation:** do **not** bulk-vendor. The one proven asset (`deg_div`) is (a) 15k
coupled lines, (b) very likely already obtainable on our side at a fraction of the cost
from the Wallace conservation lemma we already vendor, and (c) carries a
verification caveat that must be cleared with `#print axioms` before trust. Treat it as a
**fallback source of specific lemmas**, not a subtree to lift. See the decision below.

---

## What changed since our April import

| Area | April (what we took) | Now | Borrow? |
|---|---|---|---|
| Montel finite-dim of 1-forms | vendored, axiom-free | unchanged (his structural `closedBall` sorry already closed pre-import) | already have |
| LineIntegral / ZLatticeQuotient / ChartedSpace | vendored | unchanged | already have |
| **Residue theorem `deg_div`** | was an open `sorry` upstream | **PROVEN, sorry-free** via proper-map-degree engine | **candidate — but see caveats** |
| ProperMapDegree / Hurwitz / local multiplicity (`Discharge/Manifold/` 54 files) | did not exist | **sorry-free**, real | the engine under `deg_div` |
| Dolbeault ∂̄ / Čech finiteness / Serre §17 / cohomological RR (~50 files) | did not exist | mostly **sorried scaffolding** | no (watch) |
| Abel's theorem, cut-surface topology, sphere-genus | sorried | still sorried | no |

---

## The one proven asset: `deg_div` (residue theorem)

### What it is
`MeromorphicFunction.deg_div (f) : Divisor.deg X f.div = 0` — Forster Cor. 4.25 / the
"conservation of number" statement that a meromorphic function has equal zero- and
pole-counts. Proof route (`RiemannRoch.lean:74`):

```
deg_div
  └ ProperMapDegreeSheets.exists_properMapDegree_proven   (∃ d, zerosCount = d = polesCount)
      ├ exists_properMapDegree_of_div_eq_zero             (trivial divisor)
      └ exists_properMapDegree_of_localSheets             (globalize local multiplicity)
          └ localMultiplicitySheets_of_nonconstant
              ├ localMultiplicitySheets_of_mem_range       (§17.9 fibre patching)
              └ LocalMultiplicitySheets.ofNotMemRange      (empty fibre)
          ⇐ MultiplicityPatching / MultiplicityPatchingConstruct
          ⇐ Discharge/Manifold/*  (54 files: local normal form, Hurwitz, regular-value
                                    finiteness, connectivity globalization)
```

### Verification status (read before trusting)
- **My static trace finds ZERO real code-level `sorry`** (`:= sorry`, `by sorry`, …) in
  the *entire* transitive chain above — `ProperMapDegreeSheets`,
  `MultiplicityPatching{,Construct}`, `MeromorphicTrace`, `Degree`, `RiemannRoch`, and all
  54 `Discharge/Manifold/*` files. (Per-file greps that showed "1 sorry" in these were all
  docstring mentions of the word, e.g. "non-vacuous fields, never `sorry`".)
- **⚠ Discrepancy to resolve:** the README (newer) says `deg_div` is "closed and
  axiom-clean"; `docs/STATUS.md` (dated one day earlier, 2026-06-03) still lists it as one
  of the 5 open `sorry`s. The README is consistent with the code I traced (commit
  `e826fb4` "wire deg_div to the now-PROVEN exists_properMapDegree (W2 CLOSED)" post-dates
  STATUS.md). **But the only authoritative check is `#print axioms
  MeromorphicFunction.deg_div` after a `lake build`** — this has NOT been run here (would
  require building his 34k-line tree). Do this before any adoption.

### Why we probably don't need it anyway
- Kirov's `Divisor X := X →₀ ℤ` is **type-compatible** with our `abbrev Divisor` (also a
  `Finsupp` ℤ-divisor) — good. **But** `deg_div` is stated about *his* `MeromorphicFunction
  X` structure, his `RiemannSphere = OnePoint ℂ`, his `orderW`, his `f.toRiemannSphere` /
  `f.div`. Lifting it means vendoring the ~15k-line engine **and** writing a bridge from
  our meromorphic-order notion to his.
- **We already vendor the same mathematical engine from Wallace:**
  `weightedFiberConservation_of_contMDiff` (`Vendor/Wallace/HolomorphicForms/HolomorphicMap.lean:1199`,
  sorry-free, `#print axioms` = standard 3) is exactly conservation-of-number, and we
  already consume it in `AX_BranchLocus`. `deg (div f) = 0` for a meromorphic `f` is the
  `f : X → ℙ¹` specialization (zeros = fibre over 0, poles = fibre over ∞, equal weighted
  count). **Deriving `deg_div` from the Wallace lemma we already have is almost certainly
  cheaper than importing Kirov's 15k-line tower + bridge.**
- We do **not** currently carry a standalone `AX_deg_div` axiom — the residue content is
  folded into `AX_AbelTheorem` (kernel = principal divisors) and the Wallace-backed
  `AX_BranchLocus`. So there is no single axiom that vendoring `deg_div` would cleanly
  retire; the payoff is diffuse.

### Decision
**Do not vendor the deg_div engine.** Instead:
1. First try to **derive `deg (div f) = 0` from our existing Wallace
   `weightedFiberConservation_of_contMDiff`** (specialize to the meromorphic `f : X → ℙ¹`).
   This is the right-sized move and keeps the vendor surface small.
2. Only if that derivation hits a genuine gap, **mine Kirov's chain for the specific
   missing lemma** (e.g. local normal form / regular-value finiteness from
   `Discharge/Manifold/`) rather than the whole subtree — and `#print axioms`-verify that
   lemma in isolation before lifting.

---

## The Dolbeault / Serre / Riemann–Roch tower — watch, don't borrow

This is the part aimed at our two biggest Class-1 axioms (`AX_RiemannRoch`,
`AX_SerreDuality`). Status in Kirov's repo:

- **Heavily sorried scaffolding.** The largest real-sorry files in the whole repo are all
  here: `Dolbeault/CechFinitenessWiring` (17), `DolbeaultComparisonProof` (16),
  `CechDiskAcyclicAssembly` (16), `CohomologicalRR` (14), `DolbeaultComparisonEquiv` (12),
  `CechFinitenessBallSolve` (11), `CechDiskAcyclic` (11), `CechRefinementLeray` (10), …
- Kirov's own STATUS calls these "RR/Serre/finiteness sub-tree *scaffolding* sorries — a
  parallel attempt to eventually *replace* the standalone RR kernel," and they are **not
  wired to his headline** (his challenge still routes through a standalone
  `exists_riemannRoch_divisor` sorry).
- A few **small leaves are sorry-free** — `Dolbeault/Residue.lean` (the PDE-free Serre §17
  *local* residue calculus: `resAt` + API, the §17.6 residue-1 witness), `FormCoeff.lean`,
  the `DolbeaultComparison` core — but they are embedded in, and only meaningful as part
  of, the sorried global assembly. In isolation they don't retire one of our axioms.

**Verdict:** nothing here meets the no-sorries bar today. The Serre §17 local calculus and
the Dolbeault-comparison core are the pieces to **re-check on a future re-scan** — if Kirov
closes the global finiteness wall (`exists_cechModel`, Forster 14.9), the whole RR/Serre
route could become a real vendor target that retires `AX_RiemannRoch` + `AX_SerreDuality`
together. That is the single highest-leverage thing to watch in his repo.

---

## Minor items (low priority, previously deferred)

- **`Abel.lean` chart-invariance of `meromorphicOrderAt`** — still listed as "considered,
  deferred" in `cross-repo-adoption.md`; could retire `localOrder` from
  `Axioms/BranchLocus.lean`. Small payoff; our Wallace `VanishingOrder.lean` already gives
  chart-independent order, so likely redundant now.
- **`MittagLeffler.lean`, `Primitive.lean`, `HolomorphicPrimitives.lean`** — mixed sorry
  state; not worth a targeted pull.

---

## Bottom line

- **One new *proven* asset** (`deg_div` / residue theorem) — real and sorry-free, but
  15k coupled lines, **probably re-derivable on our side from the Wallace conservation
  lemma we already vendor**, and needs a `#print axioms` confirmation first. → **Don't
  bulk-vendor; try the Wallace-derivation route, mine specific lemmas only if needed.**
- **The big new RR/Serre/Dolbeault tower** is sorried scaffolding → **excluded by the
  no-sorries rule; watch for the finiteness wall to close.**
- **Everything we'd actually want from Kirov, we already took in April.** This re-scan does
  not change our vendor surface; it records the one thing that became proven (and why we
  still don't need to lift it) and flags the RR/Serre route to re-check later.
