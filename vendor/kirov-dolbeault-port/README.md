# Kirov Dolbeault port — what this provides

> This is a **forward-ported build** of `rkirov/jacobian-claude` @ `4437c2b` (2026-06-09)
> to our Mathlib version (`c5ea003`, `v4.30.0`). Build: **green (8747 jobs).**
> See `PROVENANCE.md` for attribution. The verbatim reference copy (unmodified upstream)
> lives at `../kirov-jacobian-claude-dolbeault/`.

---

## Headline: the 1-form residue theorem is sorry-free

```lean
theorem residueTheorem_unconditional
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]
    (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x ∉ poles,
        AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0
```

**`#print axioms`:** `[propext, Classical.choice, Quot.sound]` only.

For any compact connected Riemann surface, holomorphic 1-form `ω₀`, and genuinely
meromorphic `g`, the total residue of `ω₀·g` vanishes. Proved following Miranda §VIII.3
(trace to ℙ¹): the trace extends meromorphically across branch points via slit geometry +
symmetric-function descent + conservation-of-number topology, then the ℙ¹ residue theorem
+ fibrewise regrouping closes the argument.

File: `Jacobians/Dolbeault/SerreResidueRamifiedRealSlitGeometry.lean`

---

## Full list of sorry-free results

All `#print axioms`-verified to `[propext, Classical.choice, Quot.sound]`.

### Residue theorem cluster (Gate A + Forster §17.3)

| Theorem | File | Content |
|---|---|---|
| `residueTheorem_unconditional` | `Dolbeault/SerreResidueRamifiedRealSlitGeometry.lean` | ∑ Res = 0 for any meromorphic 1-form |
| `MeromorphicFunction.deg_div` | `DegDivResidue.lean` | ∑ ord = 0 for any meromorphic function (Forster Cor. 4.25) |
| `MittagLefflerForm.res_eq_zero_of_globalMeromorphic` | `Dolbeault/SerreDualityPairing.lean` | Forster §17.3: `Res : H¹(X,Ω) → ℂ` is well-defined on cohomology classes |
| `MittagLefflerForm.res_eq_of_globalMeromorphic_diff` | `Dolbeault/SerreDualityPairing.lean` | Two Mittag–Leffler representatives of one class have equal residue |

### Serre §17.6 easy half

| Theorem | File | Content |
|---|---|---|
| `injective_of_residueOne_witness` | `Dolbeault/SerreDualityPairing.lean` | Abstract injectivity criterion for the Serre pairing |
| `lDim_le_h1Dim_of_residueOne_witness` | `Dolbeault/SerreDualityPairing.lean` | `lDim(K−D) ≤ h1Dim D` — easy half of Serre duality (Forster §17.6) |

### Čech cohomology machinery (Forster §14–§16)

| Theorem | File | Content |
|---|---|---|
| `exists_cechModel` | `Dolbeault/CechFiniteness*.lean` | Forster §14: finiteness of Čech `H¹(X, 𝒪_D)` |
| `exists_skyscraperLES` | `Dolbeault/Skyscraper*.lean` | Forster §16: skyscraper χ-step `χ(D+P) = χ(D) + 1` |
| `cechH1_dolbeault_comparison_proof` | `Dolbeault/DolbeaultComparison*.lean` | Čech ↔ Dolbeault comparison isomorphism |
| `cohomologicalRR` | `Dolbeault/CohomologicalRR.lean` | Riemann–Roch from the Čech machinery |

### Differential geometry + path topology

| Theorem | File | Content |
|---|---|---|
| `isCoveringMap_mk` | `ZLatticeQuotient.lean` | `E → E⧸Λ` is a covering map |
| Van Kampen, smooth path-connectivity | `VanKampen.lean`, `SmoothPath*.lean` | π₁ tools; `S²` simply connected |
| `GreenBox`, boundary positivity | `GreenBox.lean`, `BoundaryPositivity.lean` | Green's theorem setup for the ∂̄ route |

---

## What is still open (4 remaining walls)

| `sorry` | File | Content | Blocks |
|---|---|---|---|
| `exists_serreDualityData` | `Dolbeault/SerreDualityPairing.lean:127` | §17.5 connecting map + §17.9 surjectivity | RR and `h¹(𝒪) = g` via this route |
| `abelJacobi_twoPoint_ne_zero` | `Abel.lean:671` | Abel's theorem core | `ofCurve_inj` via Kirov route |
| `exists_cutSurface` | `CutSurfaceRelations.lean:161` | Cut surface / surface topology | Jacobian manifold structure |
| `HasHolomorphicPrimitives` | `DegreeOneSphere.lean:678` | Manifold de Rham (period slice) | backward genus-0 headline |

---

## Relevance to `mrdouglasny/jacobian-challenge`

### `AX_RBR1` discharge (our Layer-3 period primitive)

`Layer3.AX_RBR1` (Stokes isotropy, the bilinear-relation `∑ aᵢ`-period × `bᵢ`-period
difference = 0) ultimately rests on `∑ Res = 0` applied to a wedge product of 1-forms on
the cut surface. `residueTheorem_unconditional` is now the reference sorry-free proof of
that ingredient. It is the primary input to any eventual `AX_RBR1` discharge.

### Phase D: Layer-3 cohomology scaffold discharge

Our seven Layer-3 cohomology axioms map to what this port has proved:

| Our axiom | Kirov result | Status |
|---|---|---|
| `cohomologyLES` (Forster §16 LES) | `exists_skyscraperLES` | **sorry-free** |
| `H1coh` + finiteness instances | `exists_cechModel` | **sorry-free** |
| `serreDuality_equiv` (full Serre iso) | `lDim_le_h1Dim` (easy) + `exists_serreDualityData` (hard) | easy half proved; **hard half open** |
| `h1coh_zero_finrank` (`h¹(𝒪) = g`) | `arithmeticGenus_eq_genus_serre` | **blocked by `exists_serreDualityData`** |

Everything upstream of the connecting map — residue theorem, §17.3 well-definedness,
§17.6 easy half, the full Čech machinery — is now sorry-free at our Mathlib version.
The single remaining chokepoint for full Serre duality is `exists_serreDualityData`
(§17.5 connecting map `H⁰(principal parts) → H¹(𝒪_D)`).

### Trust level of our `serreDuality_equiv`

This port raises confidence: `lDim(K−D) ≤ h1Dim(D)` is now proved at our Mathlib
version. The full isomorphism (dimension equality) still requires `exists_serreDualityData`.

---

## Porting delta (6 changes across 5 files)

| File | Change | Reason |
|---|---|---|
| `ChartedSpaceOfLocalHomeomorph.lean` | Renamed `chartedSpace` → `chartedSpaceOfAtPreimage` | Mathlib `c5ea003` now has `IsLocalHomeomorph.chartedSpace` with a different internal construction; renaming preserves the definitional transparency downstream proofs require |
| `ZLatticeQuotient.lean:60` | Instance calls `chartedSpaceOfAtPreimage` | Follows from above |
| `DbarDisk.lean:81,91` | `exact zero_le _` → `exact zero_le` | `zero_le`'s argument became implicit in Mathlib |
| `SymmetricFunctionDescent.lean:99,238` | Same fix | Same reason |
| `VanKampen.lean:387–388` | `Set.Icc.convexCombo` → `Icc.convexComb`; `convexCombo_zero_one` → `convexComb_zero_one` | Mathlib 2026-05-15 "Combo" → "Comb" rename |
| `Dolbeault/SchwartzFiniteness.lean:9,11` | Import paths updated for `Compact.Basic` and `Compact.FredholmAlternative` | Modules moved into `Compact/` subdirectory |

---

## Usage notes

**Namespace:** `Jacobians.*` throughout (unchanged from upstream).

**Standalone package:** this is not part of our main build. It compiles independently
under `vendor/kirov-dolbeault-port/`. Run `lake build Jacobians` from that directory.

**Type alignment:** Kirov's `HolomorphicOneForms`, `MeromorphicFunction`, `genus`, etc.
are parallel definitions to ours, not the same Lean types. Integration into our build
requires bridge lemmas (pattern: `Bridge/KirovHolomorphic.lean`).

**When to integrate:** the natural trigger is Phase D — discharging the Layer-3 cohomology
scaffold. A GitHub Discussion should precede that work per community program rules
(`CLAUDE.md`). At that point, `CechFiniteness*`, `SkyscraperLES`, `CohomologicalRR`, and
`residueTheorem_unconditional` are the primary inputs.

---

*Port completed 2026-06-10. Ported by Claude Sonnet 4.6 (1M context) under MRD direction.*
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
