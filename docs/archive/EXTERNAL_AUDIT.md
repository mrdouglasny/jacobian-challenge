# External-repo audit — `Brsanch/jacobian-lean-challenge`

> **▶ 2026-05-31 — degree-well-definedness port.** 22 further modules
> (~3.3k LOC) were ported from this repo into
> `Jacobians/Discharge/Manifold/` to discharge #8′
> (`exists_preimageCycle_sheets_eq_degree`): the well-definedness top layer
> rooted at `DegreeWellDefined.lean` (`degreeFiber_eq_card_of_regular_witness`)
> — the topological `PathConnectedComplFinite` sub-tree (connected complex
> 1-manifold minus a finite set is path-connected) and the analytic
> `HLcUnconditional`/`HPkgUnconditional`/`LocalSheetDataFromContMDiff`/
> `HurwitzPatchingDataConstruction` chain (locally-constant fibre cardinality
> via the `z ↦ zᵏ` normal form). Mechanical namespace rewrite
> (`JacobianChallenge`→`Jacobians.Discharge`, `Owed.degree`→`Degree`); 2 manual
> fixes (an `open scoped ContDiff` for `ω`; a stray `ω` @-arg). Same Mathlib pin
> + toolchain, so it compiled with only those name fixes.
> `Jacobians.Discharge.degreeFiber_eq_card_of_regular_witness` re-verified
> `#print axioms` = `[propext, Classical.choice, Quot.sound]` (guarded in
> `AxiomCheck.lean`). MIT-licensed by Bryan Sanchez (2026); provenance retained
> in each ported file's header.

**Date:** 2026-05-28
**Audited commit:** `Brsanch/jacobian-lean-challenge` `HEAD` of `main`,
pushed 2026-05-27T02:50:05Z.
**Method:** `lake build JacobianChallenge.Basic` (built whole lib, 8,471
jobs) followed by `lake env lean Audit.lean` running `#print axioms` on
each item's user-facing declaration name. Same Mathlib pin
(`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`) and Lean toolchain
(`leanprover/lean4:v4.30.0-rc1`) as our repo.

## Bottom line

The external repo's "**14 STRICT-CLOSED, 2 STUB, 8 OPEN**" claim is
**verified at the `#print axioms` level.** Every one of the 14 items
labelled STRICT-CLOSED in `OPEN.md` depends only on the three standard
Mathlib axioms `[propext, Classical.choice, Quot.sound]`. No
`sorryAx` leaks. No custom axioms. The 8 OPEN items are honest
`sorry`s in `Basic.lean`. The 2 STUB items compile via discrete
topology (mathematically wrong target, structurally honest).

Earlier text-grep counts (1,105 sorries) were almost entirely matches
inside `/-! ... -/` and `/-- ... -/` docstrings narrating closure
chains. Post-comment-strip: **8 real `sorry`s in actual code**, all in
`Basic.lean`, one per OPEN item.

## Per-item verification

| # | Item | Status (claimed) | `#print axioms` verdict |
|---|---|---|---|
| 1 | `genus` | STRICT-CLOSED | **CLEAN** — `[propext, Classical.choice, Quot.sound]` |
| 2 | `Jacobian` (abbrev → `JacobianChallenge.Jacobian`) | STRICT-CLOSED | **CLEAN** |
| 3 | `AddCommGroup (Jacobian X)` (via `audit_item3_AddCommGroup`) | STRICT-CLOSED | **CLEAN** |
| 4 | `TopologicalSpace (Jacobian X)` (via `audit_item4`) | STUB (`⊥` discrete) | **CLEAN** (proof is honest; topology itself is the stub) |
| 5 | `ChartedSpace ...` | OPEN | sorry in Basic.lean:155 |
| 6 | `Jacobian.ofCurve` | STRICT-CLOSED | **CLEAN** |
| 7 | `Jacobian.pushforward` | STRICT-CLOSED | **CLEAN** |
| 8 | `Jacobian.pullback` | STRICT-CLOSED | **CLEAN** |
| 9 | `ContMDiff.degree` | STRICT-CLOSED | **CLEAN** |
| 10 | `T2Space (Jacobian X)` (via `audit_item10`) | STUB | **CLEAN** (true via discrete) |
| 11 | `CompactSpace (Jacobian X)` | OPEN | sorry in Basic.lean:148 |
| 12 | `IsManifold ...` | OPEN | sorry in Basic.lean:159 |
| 13 | `LieAddGroup ...` | OPEN | sorry in Basic.lean:163 |
| 14 | `genus_eq_zero_iff_homeo` | OPEN | sorry in Basic.lean:107 |
| 15 | `Jacobian.ofCurve_self` | STRICT-CLOSED | **CLEAN** |
| 16 | `Jacobian.ofCurve_inj` | STRICT-CLOSED | **CLEAN** |
| 17 | `Jacobian.ofCurve_contMDiff` | OPEN | sorry in Basic.lean:179 |
| 18 | `Jacobian.pushforward_contMDiff` | OPEN | sorry in Basic.lean:222 |
| 19 | `Jacobian.pushforward_id_apply` | STRICT-CLOSED | **CLEAN** |
| 20 | `Jacobian.pushforward_comp_apply` | STRICT-CLOSED | **CLEAN** |
| 21 | `Jacobian.pullback_contMDiff` | OPEN | sorry in Basic.lean:268 |
| 22 | `Jacobian.pullback_id_apply` | STRICT-CLOSED | **CLEAN** |
| 23 | `Jacobian.pullback_comp_apply` | STRICT-CLOSED | **CLEAN** |
| 24 | `Jacobian.pushforward_pullback` | STRICT-CLOSED | **CLEAN** |

Discharge-lemma forensics (all kernel-clean):

| Declaration | Verdict |
|---|---|
| `JacobianChallenge.ContMDiff.degreeFiber` | CLEAN |
| `JacobianChallenge.ContMDiff.Owed.degree.regular_value_exists_statement_holds_unconditional` | CLEAN |
| `JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional` | CLEAN |
| `JacobianChallenge.ofCurve_inj_holds` | CLEAN |

**Verified honest closure count: 14/24 STRICT-CLOSED.**

## What this means (and doesn't)

`#print axioms` confirms each strict-closed declaration's *proof* uses
only the standard axiom set. It does **not** verify that the
declarations interpret the surrounding mathematical objects correctly.
The known structural caveats remain:

1. **The `Pic⁰` quotient uses `(PrincDiv X).addSubgroupOf (Div0 X)`,
   i.e. `PrincDiv ∩ Div0`.** The defining property `PrincDiv ⊆ Div0`
   (= the residue theorem) is **not** in tree as a theorem; the
   quotient is therefore coarser than the honest `Pic⁰` would be (more
   classes survive). Items 6/15/16 are valid against this coarser
   quotient. When the residue theorem lands, only further
   identifications get added, so existing proofs should continue to
   hold — but this is structurally a partial Pic⁰ today.

2. **Items 4/10 are STUB.** `TopologicalSpace (Jacobian X) := ⊥`
   (discrete) makes items 4/10 trivially true but is not the right
   topology. The challenge spec admits no marker for "wrong-topology
   compile" — these items are dishonest under any strict reading,
   even though `#print axioms` is clean.

3. **The 8 OPEN items are not just any sorries.** They reduce, after
   the repo's own audit, to two classical theorems:
   - Item 14 → `ExistsMeroSimplePole_GenusZero X` (Forster Thm 16.9 /
     uniformization at genus 0; ~28–50k LOC).
   - Items 5/11/12/13/17/18/21 → `C3FullInputExt X` = Riemann
     bilinear + Abel + Jacobi inversion + Abel-Jacobi smoothness +
     Abel-Jacobi injectivity (~40–60k LOC).

   These two walls are exactly the same walls our local period-torus
   construction faces (Riemann bilinear / lattice + uniformization).

## Cross-construction summary

| Aspect | Local (period-torus) | External (Pic⁰) |
|---|---|---|
| `Jacobian X` | `(Fin (genus X) → ℂ) ⧸ periodLattice X` | `Div⁰ X ⧸ (PrincDiv X).addSubgroupOf (Div⁰ X)` |
| `#print axioms` audited? | **No** (repo never built) | Yes (this audit) |
| Real sorries in code | 17 | 8 |
| Items 4/5/7/8/10/11/12 (typeclasses for manifold structure) | Wired via `inferInstance` on torus quotient; "free" *modulo* `PeriodLattice.lean:692,698` (lattice property) | OPEN (or STUB for items 4/10); conditional on `C3FullInputExt X` |
| Items 9 (`ContMDiff.degree`) | Hard-coded `0`-stub (`Jacobians.lean:356`) | CLEAN `degreeFiber` |
| Items 19/20/22/23 (functoriality) | Wired via `ZLatticeQuotient.*` + `ambientPhi/ambientPsi`; depends on lattice property | CLEAN (built on divisor functoriality) |
| Item 24 (`pushforward_pullback`) | Wired, but currently vacuous (degree = 0 by stub) | CLEAN |
| Item 16 (`ofCurve_inj`) | Wired via Abel chain bottoming at `abelJacobi_twoPoint_ne_zero` (sorry) | CLEAN (degree-1 mero → biholomorphism → genus 0 contradiction) |
| Item 14 (uniformization) | Sorry (`Genus.lean:81`) | Sorry (`Basic.lean:107`) |

**Underlying-math walls (same in both):**
* **Riemann bilinear relations** → local: lattice property, external: `C3FullInputExt`. ~weeks–months.
* **Uniformization / `ExistsMeroSimplePole_GenusZero`** → Item 14 in both. ~weeks–months.

The external repo's Pic⁰ construction additionally owes **Jacobi
inversion** (surjectivity of Abel-Jacobi onto the torus); the
local period-torus construction does not. So the local construction
is strictly less classical math to close fully.

## Phase B recommendation

**B1 — surgical harvest, narrow scope.** The audit clears the way to
port specific verified-clean lemmas from the external repo into the
local repo. The single most valuable harvest:

1. **`JacobianChallenge.ContMDiff.degreeFiber`** + its discharge
   chain (`regular_value_exists_statement_holds_unconditional`,
   `ramificationSumEqualsDegree_holds_unconditional`). All clean.
   Replaces our `Jacobians.lean:356 ContMDiff.degree := 0`, which
   currently makes `pushforward_pullback` vacuous.

What is **not** worth porting:

- **The Pic⁰ functoriality** (items 7/8/19/20/22/23/24). Our local
  repo already has these proven via the period-torus quotient
  (`Jacobians.ZLatticeQuotient.*`). The external proofs are built on
  divisor pushforward and don't transfer without re-deriving against
  ℂᵍ/Λ.

- **`ofCurve_inj_holds`** (item 16). The external proof routes
  through divisor extraction → degree-1 mero function →
  biholomorphism to ℙ¹ → genus 0 contradiction. To use it locally,
  we'd need a `MeromorphicNonzero` structure + the
  `PrincDivWitnessExtraction` chain, which isn't local infrastructure.
  Our local `ofCurve_inj` already chains through Abel's theorem leaf
  (still a sorry, but it's the cleaner direct path for the
  period-torus construction).

- **The whole Pic⁰ scaffold.** Adopting it would force us to owe
  Jacobi inversion in addition to the bilinear relations — more
  classical math, not less.

What may be worth investigating later (out of scope of this audit):

- **Cauchy-Pompeiu kernel / ∂̄-solvability** scaffolding in
  `JacobianChallenge/Analysis/` — potentially reusable for the
  residue-theorem leaf in our `Jacobians/Abel.lean:574`.
- **`degreeFiber_eq_card_of_regular_witness`** —
  well-definedness of the fibre cardinality, useful if we ever wire a
  degree theorem.

## Methodological note for future audits

The grep `(^|[^a-zA-Z_])sorry([^a-zA-Z_]|$)` over `.lean` files
includes every occurrence of the *word* "sorry" — including in
`/-! ... -/` and `/-- ... -/` docstrings. A repo with extensive
narrative documentation (like the external one) can over-count
sorries by 100× from docstrings alone. The right counts:

1. Strip block comments and line comments first.
2. Or trust `#print axioms` on the actual built declarations.

A useful one-liner:

```bash
python3 -c "
import re, pathlib
for p in pathlib.Path('.').rglob('*.lean'):
    txt = p.read_text()
    s = re.sub(r'/-.*?-/', '', txt, flags=re.S)
    s = re.sub(r'--.*', '', s)
    n = len(re.findall(r'(?<![A-Za-z_])sorry(?![A-Za-z_])', s))
    if n: print(n, p)
"
```

After comment stripping: external repo has 8 sorries, local repo has
17. Both are wholly in line with each project's stated state.
