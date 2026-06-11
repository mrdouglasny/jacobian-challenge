# SVK-lite route decision — π₁ of punctured plane/sphere

Date: 2026-06-10. Branch: `feat/topology-svk-lite`. Context:
`CYCLEBASIS_ALTERNATIVES.md` direction 2b (slit-sheet proof of
`AX_PeriodCycleBasis` needs "π₁ of a punctured sphere is free, generators =
loops around the punctures").

## Inventory: Mathlib at pin (`c5ea0035…`)

What EXISTS (all verified by file inspection in `.lake/packages/mathlib`):

| Asset | Location | Notes |
|---|---|---|
| `FundamentalGroup X x` = `End (FundamentalGroupoid.mk x)` + `fromPath`/`toPath`/`map`/`mapOfEq`/`mapOfEq_apply` | `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean` | `End` mul convention: `f * g = g ≫ f`, `≫` = `Path.trans` on classes |
| `SimplyConnectedSpace`, `Subsingleton (Path.Homotopic.Quotient x y)` instance, `IsSimplyConnected` for sets, `ofContractible` | `…/FundamentalGroupoid/SimplyConnected.lean` | the Subsingleton instance is the key injectivity device |
| `ContractibleSpace` for real TVS + `Convex.contractibleSpace` | `Analysis/Convex/Contractible.lean` | gives `SimplyConnectedSpace ℂ` and simply connected disks |
| Covering maps: `liftPath`, `eq_liftPath_iff'`, homotopy lifting, `homotopicRel_iff_comp`, **`monodromy`** (`Path.Homotopic.Quotient x y → fiber x → fiber y`), `monodromy_map`, `monodromy_refl`, `monodromy_trans_apply`, `monodromy_bijective`, lifting criterion | `Topology/Homotopy/Lifting.lean` | full Hatcher §1.3 toolkit, 2025 vintage (Junyan Xu) |
| `IsQuotientCoveringMap` / `IsAddQuotientCoveringMap` (free properly-discontinuous quotient ⇒ covering), `isCancelSMul` | `Topology/Covering/Quotient.lean` | deck-group framework |
| **`Complex.isAddQuotientCoveringMap_exp`**: `exp : ℂ → {z : ℂ // z ≠ 0}` is a quotient covering by `zmultiples (2πi)`; `isCoveringMap_exp`; `isCoveringMapOn_exp` on `{0}ᶜ`; also `(·^n)`, polynomials off critical values | `Analysis/Complex/CoveringMap.lean` | the M1 engine, ready-made |
| `AddCircle` covering `𝕜 → AddCircle p` | `Topology/Covering/AddCircle.lean` | alternative base case, not needed |
| Free groups: `FreeGroup`, `IsFreeGroup`, **Nielsen–Schreier** | `GroupTheory/FreeGroup/…` | available if a free cover is ever built |
| `FundamentalGroupoid.equivOfHomotopyEquiv` | `…/FundamentalGroupoid/InducedMaps.lean` | homotopy-equivalence functoriality (not needed on chosen route) |

What does NOT exist at pin:

- **π₁(S¹) ≃ ℤ** — absent in any form (no `FundamentalGroup` computation
  anywhere in Mathlib; grep over all files referencing `FundamentalGroup`).
- **Seifert–van Kampen** — absent. `CategoryTheory/Limits/VanKampen.lean` is
  the *categorical* van Kampen-colimit notion (extensive categories), not the
  topological theorem. Kirov's vendored `VanKampen.lean` proves only the
  simple-connectivity corollary (two simply connected opens with path-connected
  intersection ⇒ simply connected union) via Lebesgue subdivision.
- **Deck-transformation ≃ π₁** for universal covers — absent (monodromy exists
  but is never connected to a group isomorphism).
- **Wedge sums / bouquets** with π₁ — absent.

## Candidate routes

**(a) Two-open SVK for the fundamental groupoid + induction on punctures.**
Requires the full pushout/presentation form of SVK (the simple-connectivity
version Kirov proved is far weaker). Nothing in Mathlib; building
groupoid-SVK with free-product-with-amalgamation output is a known multi-week
formalization project on its own (it has been done in other systems with
substantial effort; never merged in Mathlib despite the circle-π₁ gap being
famous). Honest estimate: 3–8 weeks. NOT chosen as the session route; this is
exactly the long pole the milestone ladder tells us to stop+document at.

**(b) Deformation retract onto a wedge of circles + Mathlib wedge-π₁.**
Dominated by (a): there is no wedge-π₁ in Mathlib, and computing it IS SVK.
Reject.

**(c) Covering-space route.** For the *base case and the generator
identification* this is essentially free given the pin's assets:

- M1: `exp`-shifted coverings `z ↦ a + exp z : ℂ → {z // z ≠ a}` are quotient
  coverings by `2πiℤ` (compose `isAddQuotientCoveringMap_exp` with the
  translation homeomorphism — `IsAddQuotientCoveringMap.homeomorph_comp`).
  ℂ is simply connected (contractible TVS). General lemma to build (the one
  genuinely missing primitive): *quotient covering with simply connected total
  space ⇒ `Multiplicative G ≃* π₁(base)`*, by the monodromy bijection
  `π₁ ≃ fiber` (injectivity = `Subsingleton` of path classes upstairs,
  surjectivity = path-connectedness upstairs + `monodromy_map`) composed with
  the free transitive deck action on the fiber. Generators identified: the iso
  sends `g` to the projection of ANY path `e₀ → g +ᵥ e₀` upstairs
  (`Subsingleton` makes the choice irrelevant) — for `exp` this is the
  explicit circle loop `t ↦ a + r·exp(2πit)`.
- M2-lite (winding homs): for finite `S ⊆ ℂ` and `s ∈ S`, the inclusion
  `ℂ∖S ↪ ℂ∖{s}` composed with the M1 iso gives
  `winding s : π₁(ℂ∖S, x₀) →* Multiplicative ℤ`, and
  `winding s (loop around s') = δ_{s,s'}` (off-diagonal: the small circle
  around `s'` lives in a convex disk inside `ℂ∖{s}`, which is simply
  connected, so its class dies before reaching `π₁(ℂ∖{s})`).
  Consequence, in the consuming shape: the puncture loops have ℤ-independent
  images in `H1(ℂ∖S) = π₁^ab` — the *lower bound* half of "free on |S|
  generators", with the generators explicitly identified.
- What route (c) does NOT give: the *upper bound* (the puncture loops
  generate) and non-abelian freeness. Those need SVK (route (a)) or a
  Lebesgue-grid generation argument (Kirov's subdivision method upgraded from
  "nullhomotopic" to "decomposes as a word in puncture loops") — both
  multi-week. See `SVK_BLOCKER.md` when reached.

## Decision

**Route (c).** It is the cheapest honest route to every milestone that is
reachable at all this session, it produces the missing famous Mathlib
primitive (π₁ of `ℂ∖{pt}` ≃ ℤ) as a reusable module, and it front-loads the
half of M3 (identified independent generator loops) that the slit-sheet
consumer needs first. Full freeness/generation (M3 proper) is acknowledged
multi-week SVK territory from the start; it gets a design + blocker doc, not
a half-built attempt.

Modules: `Jacobians/Topology/CoveringPi1.lean` (general deck ≃* π₁ lemma),
`Jacobians/Topology/PuncturedPlanePi1.lean` (M1 + winding homs M2-lite).
Mathlib-only imports; Kirov's port not imported (his `VanKampen.lean` method
noted for the future generation argument, with attribution, but nothing
adapted verbatim on this route).
