# Claude self-review of the twice-amended formalization plan

Date: 2026-04-20.
Reviewer: Claude (Opus 4.7, the same model that wrote the plan).
Mode: adversarial self-review with deliberate bias toward finding flaws. Goal: don't rubber-stamp my own work. Focus on (a) stale content that round-2 amendments left behind, (b) new problems the amendments introduced, (c) residual math/Lean issues neither Gemini nor Codex flagged.

Sources read in full: `formalization-plan.md:1-791`, `gemini-review.md`, `codex-review.md`.

---

## CRITICAL — residual failures from round-2 amendments

### C1. Multiple stale axiom references

Round-2 amendments renamed or removed `AX_DegreeIndependence` (subsumed by `AX_BranchLocus`), `AX_Uniformization0` (derived from `AX_RiemannRoch + AX_SerreDuality`), and retracted the `AddCircle`-transport `LieAddGroup` strategy. The renames were applied in §7 and §3.3 but **not propagated** elsewhere:

- `formalization-plan.md:264` — Track 2 payoff table still lists `AX_DegreeIndependence` as "Proved on HyperellipticCurve."
- `formalization-plan.md:267` — same table still lists `AX_Uniformization0` as "Proved on ProjectiveLine."
- `formalization-plan.md:230` — §3.5.3 Hyperelliptic key facts still say "`AX_DegreeIndependence` for maps between hyperelliptic curves follows from an explicit computation on coordinates."
- `formalization-plan.md:706` — §9 phase A3 row still says "`ComplexTorus.lean` — 7 instances via `AddCircle` transport," but round 2 retracted this strategy.
- `formalization-plan.md:756` — §11 risk bullet still frames upstream discrete-group-quotient as an improvement on "the `AddCircle`-transport shortcut" we no longer use.
- `formalization-plan.md:783` — §12 v0.2 target still references `AX_DegreeIndependence`.
- `formalization-plan.md:784` — same target references `AX_Uniformization0`.

This is the kind of stale content that Codex caught in round 2 (§2 and §8 still saying `Jacobian X := AbelianVariety (τ X)`) and I apparently repeated in round 2's amendments. Net: 7 concrete edits needed just to make the document internally consistent.

### C2. `§5.4` contains working-through-thinking, not final architecture

Lines 517–525 begin "**Wait — the natural direction is:**" and end with "... no wait. Let me think again." This is stream-of-consciousness authorial work that was never cleaned up into a normative statement. It reads like a paragraph I left mid-thought. Consequence: the plan does not actually commit to a single, unambiguous definition of `pushforward` and `pullback`, even though these need concrete definitions before §5.5 can make sense of `pushforward_pullback = deg • id`.

### C3. Basepoint independence is stated, not proved

`formalization-plan.md:459-467`. The plan says "`Jacobian X` is *canonically* independent of `x₀`" via path conjugation, and proposes `Jacobian X := JacobianAmbient X ⧸ (⨆ x₀, periodLattice X x₀)` with "the sup is constant because of canonical iso."

**Problem:** The `periodLattice X x₀` and `periodLattice X x₁` are `AddSubgroup`s of the same ambient `JacobianAmbient X`. "Canonically isomorphic" is not the right statement — we need **equal as subgroups**, because `iSup` of a constant family of `AddSubgroup`s is that constant subgroup. The statement that they're equal requires:

> For any two basepoints `x₀, x₁ ∈ X` and any loop `γ ∈ π_1(X, x₁)`, there exists a loop `γ' ∈ π_1(X, x₀)` whose integral against any `ω ∈ HolomorphicOneForm X` equals the integral of `γ`.

This is true (take `γ' := p * γ * p⁻¹` for a path `p : x₀ ⇝ x₁`; integrals along `p` cancel), but it requires `pathIntegral` to be defined and additive. So it's a **theorem in B5/B4 territory**, not a definitional triviality. The plan treats it as a construction-time one-liner.

The alternative "`Jacobian_base` with compatibility lemma" is actually cleaner — let `Jacobian X := periodLattice X (Classical.arbitrary X)`, prove `periodLattice X x = periodLattice X x'` as a lemma, be done. The `iSup` formulation is a workaround that adds complexity without gaining anything.

### C4. `AX_BranchLocus` is self-referentially stated

`formalization-plan.md:614`: "For non-constant holomorphic `f : X → Y`: ... away from critical values, fiber cardinality is constant `= deg f`."

But `deg f` is defined in §5.4 using this axiom. So: axiom says "fiber cardinality equals `deg f`", and `deg f` is defined as a sum over one fiber. The axiom effectively says "the value of the sum agrees with the cardinality away from critical values." Fine mathematically but the statement as written is circular.

**Fix:** restate the axiom without mentioning `deg f`. Something like: "for non-constant holomorphic `f : X → Y` between compact Riemann surfaces, (a) `f` is proper, (b) fibers are discrete hence finite, (c) `∑_{p ∈ f⁻¹(q)} localOrder(f, p, q)` is independent of `q`." Then `deg f` is defined as that common value.

---

## SUBSTANTIVE — round-2 amendments missed these

### S1. §2 architecture tree still describes pre-generalization types

`formalization-plan.md:38` — "`Lattice.lean (FullRankLattice of ℂ^g, discreteness)`"
`formalization-plan.md:40` — "`ComplexTorus.lean (AbelianVariety τ, all 7 instances)`"

Both are stale after §3.1 generalized to "arbitrary finite-dim ℂ-vector space `V`" and §3.3 changed `AbelianVariety (τ : SiegelUpperHalfSpace g)` to `AbelianVariety V Λ`. The module tree in §2 is the first thing a reader sees, and it describes the *original* (pre-round-1) architecture.

### S2. Mumford Vol I §II.2 cited as blueprint; amended plan is incompatible

`formalization-plan.md:19` calls Mumford Vol I Ch II §2 the "**Primary blueprint for Part B**." Mumford §II.2 constructs the Jacobian as `ℂ^g / Λ_τ` via an **explicit basis** of holomorphic 1-forms and symplectic cycle basis. Our amended plan is **basis-free at the type level** — the Mumford construction is *one way* to compute the period lattice concretely, but it is not the shape of our `Jacobian X` definition.

The source picture in §1 never addresses this tension. A reader expects "Mumford §II.2 ≈ our implementation" but the two actually disagree at the definitional level; Mumford becomes the blueprint for *proofs of properties* (discreteness of periodLattice, Riemann bilinear) rather than the definition. Worth calling this out explicitly.

### S3. PathIntegral scope: 1-complex-dim or n-complex-dim?

`formalization-plan.md:319-326`. The `pathIntegral` signature is stated for a general `X` satisfying Buzzard's typeclass constraints — i.e. `ChartedSpace ℂ X` charts to ℂ, so the complex dimension is 1. Good for our use case.

But `HolomorphicOneForm X` (§4.1) is stated generically as sections of a cotangent bundle; there's no assumption built in that charts are to ℂ (as opposed to `ℂ^n` for general `n`). The derivative `D(c₂ ∘ c₁.symm)` in the chart-cocycle fallback is a ℂ-linear map `ℂ → ℂ`, which for 1-dim identifies with multiplication by a complex number — which is why the cocycle makes sense as an equation in ℂ. For higher-dim it would be a Jacobian matrix and the 1-form's transformation rule would need to take values in a dual space.

**Conclusion:** The plan quietly assumes 1-dim throughout. Fine — Buzzard's `ChartedSpace ℂ X` pins this — but should be explicitly flagged. Otherwise a future reader may think `HolomorphicOneForm` is a general complex-manifold construct and be surprised when pushforward-along-branched-cover makes use of the 1-dim specialization.

### S4. v0.1 "all 22 instance/data sorries" miscounts

`formalization-plan.md:769`. Buzzard has 22 sorries, breaking down:

| Category | Count |
|----------|-------|
| Defs/instances (data) | 13 (genus, Jacobian, 7 instances, ofCurve, pushforward, pullback, ContMDiff.degree) |
| Theorems | 9 (genus_eq_zero_iff_homeo, ofCurve_contMDiff, ofCurve_self, ofCurve_inj, pushforward_contMDiff, pushforward_id_apply, pushforward_comp_apply, pullback_contMDiff, pullback_id_apply, pullback_comp_apply, pushforward_pullback) |

Wait, that's 10 theorems, not 9. Let me recount from Challenge.lean:
genus_eq_zero_iff_homeo (1), ofCurve_contMDiff (1), ofCurve_self (1), ofCurve_inj (1), pushforward_contMDiff (1), pushforward_id_apply (1), pushforward_comp_apply (1), pullback_contMDiff (1), pullback_id_apply (1), pullback_comp_apply (1), pushforward_pullback (1) = **11 theorems**. Plus 13 data/instance sorries = 24 total. Hmm.

Actually let me count Challenge.lean sorries directly from my read:
Line 44: `genus` sorry (1).
Line 53: `genus_eq_zero_iff_homeo` sorry (2).
Line 59: `Jacobian` sorry (3).
Lines 65, 69, 72, 75, 80, 83, 86: 7 instance sorries (4-10).
Line 89: `ofCurve` sorry (11).
Line 92: `ofCurve_contMDiff` sorry (12).
Line 94: `ofCurve_self` sorry (13).
Line 97: `ofCurve_inj` sorry (14).
Line 107: `pushforward` sorry (15).
Line 112: `pushforward_contMDiff` sorry (16).
Line 115: `pushforward_id_apply` sorry (17).
Line 125: `pushforward_comp_apply` sorry (18).
Line 131: `pullback` sorry (19).
Line 136: `pullback_contMDiff` sorry (20).
Line 139: `pullback_id_apply` sorry (21).
Line 143: `pullback_comp_apply` sorry (22).
Line 149: `ContMDiff.degree` sorry (23).
Line 152: `pushforward_pullback` sorry (24).

**Buzzard's file actually has 24 sorries, not 22.** The "22 sorries" number has propagated through all docs (`README.md`, `docs/plan.md`, `docs/status.md`, `docs/challenge-summary.md`, `docs/formalization-plan.md`) without verification.

Either I miscounted once at the start and it got copied, or Buzzard's v0.2 has 24 but something coarser (e.g. "Main missing definitions: 6" and "Main missing theorems: 6" from the docstring = 12 items counted as *theorems-and-definitions* not sorries) was misread as 22. **This needs a straight `grep -c 'sorry' Jacobians/Challenge.lean` before any further planning.** A plan targeting the wrong count is a planning error.

### S5. `pullback : Jacobian Y → Jacobian X` has no agreed-on construction in the plan

Related to C2 but worth separating. The natural construction of `pullback` uses **trace of 1-forms** `f_* : HolomorphicOneForm X → HolomorphicOneForm Y` (fiberwise sum with branch multiplicities), which gives a map on duals pointing `(H⁰ Y)^∨ → (H⁰ X)^∨`. But `f_*` on forms is exactly the construction that requires `AX_BranchLocus` — you need finiteness of fibers and branch-multiplicity tracking to define the sum.

So: `pullback` on Jacobians depends on `f_*` on forms, which depends on `AX_BranchLocus`. That's a real dependency chain that doesn't appear in §8 dep graph. The graph shows `AX_BranchLocus → Functoriality → PushPull` with `Functoriality` as a single block, but inside `Functoriality` one of the two functors (`pullback`) needs branch-locus theory to even be defined, not just to prove the push-pull identity.

### S6. `§4.5 IntersectionForm.lean` embeds an `axiom` inline

`formalization-plan.md:396`: `axiom periodMap_injective : Function.Injective (periodMap X x₀)`

This is shown inside the `IntersectionForm.lean` example code block. But the plan says axioms live in `Axioms/`, with `Axioms/PeriodInjective.lean` specifically listed (§2 architecture tree). The plan's example code should reference the axiom by its full name, not redeclare it inline. This is a minor but concrete mixup of content between two files.

### S7. Self-duality claim for `EllipticCurve E` understated

`formalization-plan.md:214` — "Self-duality: `Jacobian E ≃ E` (as complex manifolds). Identifies the Abel-Jacobi map with the identity up to translation."

For an elliptic curve `E`, this is true: `E` *is* its own Jacobian (the Abel-Jacobi map `ofCurve P₀ : E → Jacobian E` is an isomorphism, given a choice of origin `P₀`). But establishing this requires:

1. Abel's theorem for g=1 (injectivity of ofCurve).
2. Surjectivity (Jacobi inversion for g=1).
3. Holomorphicity of the inverse.
4. Checking the group operation on `E` (usual elliptic curve + chord-tangent) agrees with the group op on `Jacobian E` (quotient addition).

(4) alone is a nontrivial theorem — the elliptic-curve group law in Weierstrass form is chord-tangent, while `Jacobian E` adds via lifts in `ℂ`. Agreement is essentially the addition formula for the Weierstrass ℘-function. Formalizing this is **not 2 weeks of Mathlib-reuse**; it is the full content of the g=1 Jacobian theorem.

The plan budgets §3.5.2 Elliptic at 2 weeks and attributes most cost to "Mathlib elliptic-curve infrastructure reuse." Actually realistic if we axiomatize `Jacobian E ≃ E` for Elliptic; much longer if we prove it.

---

## MINOR — cleanup / stylistic

### M1. `§3.4 Theta.lean` fixed to `Fin g → ℂ`

`formalization-plan.md:163-165`. After §3.1 generalized lattices to arbitrary `V`, the theta series is still specifically a function of `z : Fin g → ℂ`. That's actually fine — the series truly needs coordinates, via the sum over `ℤ^g`. But the plan should note this is not a generalization gap; Theta genuinely lives on coordinatized `ℂ^g`.

### M2. §4.3 Homology.lean

`formalization-plan.md:351`. Says "axiomatize it in `Axioms/`, discharge later" for the rank=2g fact, which was indeed made into `AX_H1FreeRank2g` per round 1. The bullet should reference the axiom by name for navigability.

### M3. §4.4 Periods.lean

`formalization-plan.md:367-371` still builds an explicit `periodMatrix` as a `Matrix (Fin (2*g)) (Fin g) ℂ` relative to chosen bases. After the basis-free amendment this matrix is derived content (convenience form for interfacing with Mumford Vol I §II.2), not a structural component. The text treats it as a primary output. Minor issue: misleads the reader about what's essential.

### M4. `§9` budget internal checks

The A milestone totals "~2 months" from A1 (1 day) + A2 (1-2w) + A3 (2-3w) + A4 (4-6w). Adds to 1d + 1-2w + 2-3w + 4-6w ≈ 7-11 weeks, call it ~2 months. OK.

B milestone: 5 months = 2-4w (B1) + 3mo (B2) + 1-2w (B3) + 2-3w (B4) + 2-3w (B5) + 3d (B6) = roughly 4.5-5.5 months. OK.

C milestone: 3-4 months = 5-6w (C1) + 2mo (C2) + 3w (C3) + 1w (C4) = ~4-4.5 months. OK.

Grand total serial A→B→C: 2+5+4 = 11 months. Matches "9-12 months" claim. ✓

Track 2 (concurrent with B): 2mo (A) + 5mo (T, during B) = 7 months to v0.1 including Track 2. Matches "Track 2 closed concretely: ~5-6 months" if we count from T1 start, not A1.

### M5. Plan never says what goes in `Jacobians/Basic.lean`

§2 shows `Basic.lean` in the tree but no section defines its contents. Presumably: shared imports, open-scope declarations (`ContDiff` for ω, `Manifold` for 𝓘), and any shared notation. A one-paragraph §2.0 or §A0 would fix.

### M6. v0.2 target references `AX_DegreeIndependence` and `AX_Uniformization0`

See C1; specifically `formalization-plan.md:783-784`.

### M7. `RiemannSurface/` directory in §2 still advertises "period matrix in 𝔥_g" as content

`formalization-plan.md:55`. In the amended plan `Periods.lean` constructs the period *pairing* primarily; the period matrix is an optional derived artifact. Tree descriptor overstates the matrix's centrality.

---

## Recommended edits to the plan

Grouped by risk:

**Must fix before v0.1 scaffolding (CRITICAL)**:

1. Sweep `AX_DegreeIndependence`, `AX_Uniformization0`, and `AddCircle`-transport references everywhere. Target lines: 230, 264, 267, 706, 756, 783, 784.
2. Clean up §5.4 lines 517–525 stream-of-consciousness into a single normative statement of how `pushforward` and `pullback` are defined.
3. Replace `§5.1`'s `iSup`-over-basepoints construction with the cleaner "`Jacobian_base := ...`, prove `periodLattice X x = periodLattice X x'` as a lemma" formulation.
4. Restate `AX_BranchLocus` without self-reference on `deg f`.
5. **`grep -c 'sorry' Jacobians/Challenge.lean`** to confirm the count and update the plan (and all other docs) consistently.

**Should fix for v0.1 credibility (SUBSTANTIVE)**:

6. Update §2 module tree: `Lattice.lean (FullRankLattice in arbitrary ℂ-space V)`, `ComplexTorus.lean (AbelianVariety V Λ)`.
7. §1 source picture: note explicitly that Mumford §II.2 is the blueprint for *properties* of the period lattice, not the *definition* of the Jacobian.
8. §4.1 / §4.2: flag that the plan assumes 1-complex-dim throughout (forced by Buzzard's `ChartedSpace ℂ X`).
9. §8 dep graph: split `Functoriality` into `pullback` (needs AX_BranchLocus) and `pushforward` (doesn't directly, though PushPull does).
10. §3.5.2: downgrade "self-duality `Jacobian E ≃ E` in 2 weeks" to "axiomatized or a 1-2-month theorem including Jacobi inversion and group-law agreement."

**Cleanup (MINOR)**:

11. §4.5 IntersectionForm: replace inline `axiom` with `import Axioms.PeriodInjective`-style reference.
12. §4.3 Homology: reference `AX_H1FreeRank2g` by name.
13. §4.4 Periods: clarify that `periodMatrix` is a derived convenience, not a structural component.
14. Add a §2.0 or brief note specifying `Basic.lean` contents.

---

## Verdict

The plan is materially better than the pre-reviews version but has drifted from self-consistency. Round 1 and round 2 each changed the canonical architecture, and the document now carries three layers of text (original, round 1, round 2) without a full pass of global consistency editing. Most critical findings here are **stale content**, not new mathematical mistakes — but stale content in a plan is as harmful as wrong content, because implementers will follow the first thing they see.

The core architectural commitments are sound: basis-free Jacobian, direct LieAddGroup construction (not `AddCircle` transport), `meromorphicOrderAt`-based degree, `AX_BranchLocus` as the one gate for functoriality, explicit lifted paths for hyperelliptic. None of these need revision. The plan needs a **consistency pass**, not another major rewrite.

Recommended next action: apply the 5 CRITICAL edits + check-sorry-count, verify `lake build` succeeds (the user is doing this concurrently), then begin T1 scaffolding (`ProjectiveCurve/Line.lean`) as the first code milestone. Additional substantive and minor edits can go in later amendment passes.
