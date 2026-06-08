# Definitions audit — jacobian-challenge

*Last updated 2026-06-04 (`main`, after merging PRs #3 / #4 / #5).*

Companion to [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). Where the axiom audit tracks the
*trust boundary we declare explicitly*, this document tracks the **silent** trust
boundary: a `def` the Lean kernel accepts whether or not it matches its intended
meaning. The kernel checks that proofs are valid; it never checks that
`def localOrder … := 0` is the *right* `0`. A degenerate definition (`:= 0`,
`:= True`, `:= ⊥`, `:= ∅`, a constant function ignoring its arguments) typechecks,
passes `#print axioms`, and builds green — yet makes every theorem *about* it
vacuous. That is the **faithfulness wall**, and this audit is our defense.

> **Why this matters here.** A sibling Jacobian-Challenge repo we surveyed had a
> systematic placeholder layer (period pairing `:= 0`, exterior derivative
> `:= True`, period subgroup `= ⊥`) under proofs that *looked* substantive. We
> adopted only the parts of that repo decoupled from it (see
> [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md)). This audit
> confirms our own definition layer carries no analogous placeholders.

## Methodology

Source of truth is the regenerable inventory:

```
python3 scripts/definition_inventory.py     # → docs/definition-inventory.tsv (+ console summary)
python3 scripts/definition_inventory.py --flags
```

The script walks `Jacobians/**.lean` and emits one row per `def` / `abbrev` /
`structure` / named `instance`: `file, line, kind, name, uses, vetting,
body_head, red_flags`. Two mechanical signals:

1. **Degeneracy red-flags** (syntactic): `trivial-body` (RHS is a bare
   `0/1/True/⊥/∅/()/rfl/trivial/default`), `sorry-body`, `const-fun` (`fun _ … =>`
   a constant), `wrapper` (RHS is a single identifier).
2. **Usage / orphan** (semantic-ish): count of references to the leaf name across
   the lib (bare and `Ns.`-qualified). `orphan` = referenced nowhere, `near-orphan`
   = once. **Caveats, applied in the script:** typeclass *instances* are resolved
   by synthesis, not by name, so they are never flagged orphan; qualified
   references (`Bridge.bridgeFormEquiv`) *are* counted (an earlier regex bug that
   under-counted them is fixed).

Each declaration is bucketed into a coarse **vetting class** (how its correctness
is held in place):

| Vetting class | What pins correctness | Count |
|---|--:|--:|
| `used` | referenced by ≥2 sites; degeneracy would break a consumer | 137 |
| `vendored` | under `Vendor/`; verified upstream + `#print axioms`-checked on import | 59 |
| `instance` | typeclass instance; vetted by synthesis into the proofs that consume it | 23 |
| `witness` | terminal existence/concrete witness (`Witnesses.lean`, `*CycleBasis`, `*Loop`, `*Arc`); self-pinned by its own proof obligations | 13 |
| `sorry` | body still contains `sorry` | 1 |
| `orphan` | referenced nowhere; needs manual disposition | 0 |
| **total** | | **233** |

*(After this audit added witness lemmas: `hasBranchAtInfinity` moved `orphan → used`;
zero genuine orphans remain. The two rows still carrying an `orphan` red-flag are
`aLoop`/`bLoop`, vetting-class `witness` — forward scaffolding, see below.)*

> **Provenance.** Counts are on `main` after merging PRs #3 (Hyperelliptic leaf
> instances), #4 (bridgePath cluster), and #5 (this audit). The four
> `Hyperelliptic.inst*` instance declarations from #3 are included (instances
> 19 → 23, total 229 → 233). The inventory is regenerable by design — treat the
> committed TSV as a snapshot, not a frozen count; rerun
> `python3 scripts/definition_inventory.py` after adding/removing declarations.

**Heuristic limits (stated honestly).** The red-flag scan only catches
*single-token* trivial bodies; a structurally-degenerate body (`:= ⟨0, 0⟩`,
`:= { f := 0 }`) would not trip it. The usage count is a name-match, so it can
over-count a leaf name shared across namespaces. Neither signal *proves* a
definition faithful — they triage where human/witness-lemma review is worth it.
The deeper guarantee comes from the **headline theorems** (below).

## Headline result

- **Zero trivial-body placeholders** across all 233 declarations (`0`/`True`/`⊥`/…).
  Our definition layer is not syntactically degenerate.
- **Zero genuine orphans** after this audit (the one found, `hasBranchAtInfinity`,
  was pinned with a witness lemma); one known `sorry`, dispositioned below.
- The **load-bearing definitions are pinned by the axiom-free headline theorems**:
  if `genus`, `Elliptic`, `HyperellipticEvenProj`, the `hyperellipticForm`
  framework, the period-lattice `Jacobian`, `localOrder`, `bridgePath` /
  `bridgePathImpl`, or `pullbackOneForm` were degenerate, one of
  `genus ProjectiveLine = 0`, `genus (Elliptic …) = 1`,
  `genus (HyperellipticEvenProj H) = H.f.natDegree/2 − 1`, the pullback
  functoriality theorems, or the `bridgePath` regularity theorems would fail to
  typecheck. These are checked axiom-free / standard-axioms-only via
  [`docs/axiom-report.txt`](docs/axiom-report.txt) and `#print axioms`.

## Risk-set dispositions (the flagged rows)

| Decl | File:Line | Flag | Disposition |
|---|---|---|---|
| `hasBranchAtInfinity` | `ProjectiveCurve/Hyperelliptic/Basic.lean:40` | (was orphan) | `:= Odd H.f.natDegree`. Was unused; **now pinned** by witness `hasBranchAtInfinity_eq_true_iff` (this audit). Transparently faithful. |
| `hyperellipticOddBasisDifferential` | `Extensions/HyperellipticOdd.lean:122` | sorry-body | Known `sorry` (outside the core challenge; tracked in `AXIOM_AUDIT.md`/README sorry inventory). |
| `aLoop`, `bLoop` | `ProjectiveCurve/Elliptic/Witnesses.lean:123,143` | (witness) | Concrete A/B-cycle `AnalyticLoop`s (commit `d32b811`). **Forward scaffolding** earmarked for the `AX_Elliptic_H1_symplectic` discharge (`Path.toHomologyClass (aLoop)` is the intended H₁ basis). **Self-pinned:** the `AnalyticLoop` structure *forces* `start_eq`/`end_eq` (the loop must close at `0`), discharged in the witness — so they cannot be degenerate. |
| `aArc`, `bArc`, `ellipticCycleBasis`, `projectiveLineCycleBasis`, `stereographic` | `…/Witnesses.lean`, `Line.lean:279` | near-orphan | Terminal concrete witnesses; orphan-by-design (their job is to *be* an existence demonstration, not to be called). Self-pinned by their stated types. |
| `bridgePathImplRegular` | `Bridge/BridgePath.lean:837` | near-orphan | Internal predicate consumed by `bridgePathImpl_chart_differentiableAt_of_regular`. Fine. |
| vendored near-orphans | `Vendor/**` | near-orphan | Upstream API surface; verified on import, out of scope for our faithfulness review. |

## Vetting by area (how each cluster is held in place)

- **`AbelianVariety/ComplexTorus`** — `ComplexTorus V L := V ⧸ L`; instances
  pinned by the `Jacobian` construction that consumes all 7 Buzzard typeclasses.
  Axiom-free.
- **`ProjectiveCurve/` curve models** (`ProjectiveLine`, `Elliptic`,
  `HyperellipticOdd`/`EvenProj`, charts/atlases) — pinned by the genus headline
  theorems (a degenerate carrier or chart would break `genus … = g`).
- **1-form framework** (`hyperellipticForm`, `affineProjXCoeff`, `EvenForm` family)
  — pinned by the S1–S7 linear-independence + cocycle theorems (all real,
  axiom-free) and the `genus_HyperellipticEven_eq` upper/lower bounds.
- **`localOrder`** — discharged to a real `def` *with an explicit non-vacuity
  witness* `localOrder_pow : localOrder (z ↦ zᵏ) 0 0 = k` (`BranchLocus.lean`). The
  model for a witnessed definition.
- **`Bridge/BridgePath` + `KirovLineIntegral`** — `bridgePathImpl` and the
  `bridgePath` cluster are pinned by their own regularity theorems
  (`_continuous`, `_chart_differentiableAt`, `_at_zero/_at_one`, `_lineIntegrable`),
  all `#print axioms`-clean.
- **`Vendor/**`** — Kirov + Wallace; headline lemmas `#print axioms`-verified to
  the standard three on adoption (`docs/cross-repo-adoption.md`).

## Recommended test/witness lemmas (the "if needed" list)

The layer is healthy, so few are needed. Highest-value additions, in priority
order (a degenerate definition would make each *fail*, so they are genuine
regression guards):

1. **`genus` small-cases** ✅ *added* — `genus_eq_of_natDegree_eq_two_mul_add_one`
   (`deg = 2g+1 ⇒ genus = g`) and `…_two_mul_add_two` (`deg = 2g+2 ⇒ genus = g`)
   in `ProjectiveCurve/Hyperelliptic/Basic.lean`, guarding the `(d−1)/2`
   off-by-one on both parities.
2. **`hasBranchAtInfinity`** ✅ *added* — `hasBranchAtInfinity_eq_true_iff`
   (`= true ↔ Odd H.f.natDegree`), pinning the previously-unused predicate.
3. **Curve-carrier non-emptiness witnesses** where a model could collapse to
   `Empty` without a headline noticing — none found unpinned in this pass.

## Re-running

Regenerate after adding/removing definitions:

```
python3 scripts/definition_inventory.py
git diff docs/definition-inventory.tsv      # review newly-flagged rows
```

Consider wiring `definition_inventory.py --flags` into CI as a soft gate that
fails on a *new* `trivial-body`/`sorry-body`/`orphan` outside an allowlist.
