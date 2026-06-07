# `PlaneCurve.instCompactSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:170`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 6 &nbsp;&nbsp; **Est:** ~1–2 focused weeks, ~200–300 LOC (after `PlaneCurve` lands as a real `def`)
**Blocked by:** `PlaneCurve` (the type itself at `Jacobians/ProjectiveCurve/PlaneCurve.lean:161` is still axiomatic)

**Statement (verbatim):**
```lean
axiom PlaneCurve.instCompactSpace (H : PlaneCurveData) :
    CompactSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instCompactSpace
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `Jacobians/ProjectiveCurve/PlaneCurve.lean:161`. The docstring at lines 128–151 explains that the one-point compactification `OnePoint (PlaneCurveAffine H)` (the historical-but-wrong encoding referenced at `PlaneCurve.lean:17` and `PlaneCurve.lean:148`) is topologically wrong for `d ≥ 2`: a smooth degree-`d` plane curve generically meets `{z = 0}` in `d` distinct points by Bézout, not one. The correct construction is the three-affine-chart quotient (dehomogenize at `z ≠ 0`, `y ≠ 0`, `x ≠ 0` and glue). Once that lands, compactness is *provable from the other axioms* — there is no in-pin `CompactSpace` instance on `Projectivization` in Mathlib (`Mathlib/LinearAlgebra/Projectivization/Basic.lean:48` defines the type with no topology, and a repo-wide grep finds no `CompactSpace`/`TopologicalSpace` instance under `Mathlib/LinearAlgebra/Projectivization/`), so this discharge cannot piggy-back on `ProjectiveSpace.compactSpace`; it must execute the chart-cover argument directly.

**Gemini critique addressed:**
- **Route correction.** Original recipe said `mathlib-now [review]`; the critique correctly flagged that since the route hinges entirely on the `PlaneCurve` definition (still axiomatic) and on three project-internal `PlaneCurveAffine`-style summands, the right classification is `provable-from-other-axioms`. Updated.
- **Effort recalibration.** Original estimate of 3 / ~40 LOC was wildly optimistic. Closed-polydisc construction, max-modulus inequalities over `Fin 3`, quotient-topology continuity, and three-summand gluing realistically run 200–300 LOC, mirroring the two-summand `Hyperelliptic/Even.lean` compactness proof (which already runs ~60 LOC just for the closed-ball subset arguments at `Jacobians/ProjectiveCurve/Hyperelliptic/Even.lean:485–542`). Bumped to Effort 6.
- **Step 2B logical gap.** Original Step B said "every projective point has at least one nonzero homogeneous coordinate" and asserted this gives the cover. The critique correctly points out that an arbitrary nonzero coordinate may have small modulus, leaving the dehomogenized affine coordinates with modulus `> 1`, *outside* the closed unit polydiscs. The fix is to select the coordinate with **maximum** absolute value at each point of `PlaneCurve H` — that coordinate is strictly positive (since `[0:0:0]` is ruled out by `PlaneCurveData.h_smooth` at `PlaneCurve.lean:52–53`), and after dehomogenizing by it the other two affine coordinates have modulus `≤ 1` by construction, landing the point inside the corresponding closed-polydisc patch. Step 2B is rewritten below to make this explicit.
- **Quotient-topology overhead.** The critique notes that pushing closedness/compactness through `Quotient.mk` is not automatic. Recipe now explicitly cites `IsCompact.image` (`Mathlib/Topology/Compactness/Compact.lean:121`), `Quotient.compactSpace` (`Mathlib/Topology/Compactness/Compact.lean:1199`), `isCompact_iff_compactSpace` (`Mathlib/Topology/Compactness/Compact.lean:1037`), and `isCompact_univ_iff` (`Mathlib/Topology/Compactness/Compact.lean:784`).
- **Textbook citation.** Per critique, the closed-polydisc cover of `ℙⁿ` is the standard proof in Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 ("Complex Manifolds — Projective Space"). Added.

**Proof recipe**

1. **Wait on `PlaneCurve`.** Discharge after the `PlaneCurve` recipe (`docs/planning/PlaneCurve.md`, effort 8) lands the type as a real `def`. The intended encoding is the three-chart quotient/pushout
   ```
   PlaneCurve H := Quotient (planeCurveSetoid H : Setoid (Σ i : Fin 3, PlaneCurveAffineDehom H i))
   ```
   where `PlaneCurveAffineDehom H i` is the dehomogenization of `H.F` at coordinate `i` (so `i = 2` gives the existing `PlaneCurveAffine H` from `PlaneCurve.lean:65–66`, `i = 1` swaps `y ↔ z`, `i = 0` swaps `x ↔ z`), mirroring the two-chart `Quotient (Sum ...)` pattern at `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean:174–186` (the `instChartedSpace` for the even atlas) but with three summands instead of two — that is the model. The setoid identifies points related by the projective rescaling on the gluing region (`xy ≠ 0`, `xz ≠ 0`, `yz ≠ 0`).

2. **Build the closed-polydisc cover** (this is the heart of the proof; cite Griffiths–Harris Ch. 0 §2). With `PlaneCurve H` realized as above, each of the three affine charts contributes a closed compact piece, and *together* they cover `PlaneCurve H`. Concretely:

   - **Step 2A — per-chart closed compact piece.** For each `i ∈ Fin 3`, define
     ```
     K_i := { p : PlaneCurveAffineDehom H i // ‖p.val.1‖ ≤ 1 ∧ ‖p.val.2‖ ≤ 1 }
     ```
     — the closed unit polydisc inside the `i`-th affine chart. `K_i` is **closed** as the intersection of `PlaneCurveAffineDehom H i` (closed by the analogue of `PlaneCurveAffine.isClosed_carrier` at `PlaneCurve.lean:82–93`, which only uses `MvPolynomial.continuous_eval` and trivially generalizes to any of the three dehomogenizations) with the preimage of `Metric.closedBall (0 : ℂ × ℂ) 1`. `K_i` is **compact** as a closed subset of the compact `Metric.closedBall (0 : ℂ × ℂ) 1` (the latter compact by `Metric.isCompact_closedBall` at `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean:80` applied via the closed embedding of the chart's carrier into `ℂ²`). Convert via `isCompact_iff_compactSpace` (`.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean:1037`). This mirrors `Jacobians/ProjectiveCurve/Hyperelliptic/Even.lean:485–520` (the `hK₁_subset`/`hK₂_subset` pattern from `HyperellipticEven` compactness), generalized from two to three summands.

   - **Step 2B — the three closed polydiscs cover `PlaneCurve H` (max-modulus argument).** Let `q : PlaneCurve H` and lift it to some homogeneous representative `(x, y, z) ∈ ℂ³ \ {0}` (nonzero by `PlaneCurveData.h_smooth` at `PlaneCurve.lean:52–53`, which rules out `[0:0:0]`). Define
     ```
     i₀ := argmax (Fin 3 → ℝ) (fun i => ‖(![x, y, z] : Fin 3 → ℂ) i‖)
     ```
     i.e. the index of the coordinate with **maximum absolute value**. Since `(x, y, z) ≠ 0`, the value at `i₀` is strictly positive, so we may divide. The dehomogenized representative in chart `i₀` is `(coord_j / coord_{i₀}, coord_k / coord_{i₀})` for the other two indices `j, k`; by choice of `i₀` each of these has modulus `≤ 1`, landing the point inside `K_{i₀}`. Hence the image of `K_0 ⊔ K_1 ⊔ K_2` under the quotient map `Quotient.mk planeCurveSetoid` is *all* of `PlaneCurve H`. **This is the critical step the critique flagged; the original recipe wrote only "every projective point has at least one nonzero homogeneous coordinate," which is true but insufficient — only the maximum-modulus coordinate guarantees the dehomogenization lands in the closed unit polydisc.**

   - **Step 2C — push compactness through the quotient.** The three injections `PlaneCurveAffineDehom H i ↪ Σ i, PlaneCurveAffineDehom H i` and the quotient map `Quotient.mk planeCurveSetoid` are continuous (the former by `continuous_sigmaMk`, the latter by `continuous_quot_mk`). Therefore each `Quotient.mk ∘ Sigma.mk i '' K_i` is compact by `IsCompact.image` (`.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean:121`). Their union is compact by `IsCompact.union`. By Step 2B that union *is* `Set.univ : Set (PlaneCurve H)`, so `IsCompact (Set.univ : Set (PlaneCurve H))`. Conclude `CompactSpace (PlaneCurve H)` via `isCompact_univ_iff` (`.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean:784`).

   - **Alternative (slicker, equivalent) Step 2C.** If `PlaneCurve H` is encoded as `Quotient s` for `s : Setoid (Σ i, PlaneCurveAffineDehom H i)` *and* the sigma-type is itself compact (because each `K_i` covers its summand modulo the projective rescaling), one can invoke `Quotient.compactSpace` (`.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean:1199`) directly. In practice the explicit `IsCompact.image` route above is more flexible because the source sigma-type is **not** compact (the affine charts are noncompact by `AX_PlaneCurveAffine_noncompact` at `PlaneCurve.lean:121–124`); we are compactifying *via* the quotient, not preserving compactness through it.

3. **Why no `ProjectiveSpace.compactSpace` shortcut.** A natural alternative is "`PlaneCurve H` is closed in `Projectivization ℂ (Fin 3 → ℂ)`, which is compact, hence compact." But: a search of `.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/` (Basic.lean, Constructions.lean, Subspace.lean, Independence.lean, Cardinality.lean, Action.lean) reveals **no `TopologicalSpace` instance**, let alone a `CompactSpace` instance. The closest in-Mathlib hits for compact projective constructions are `Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean` (`ℙ¹` only, via one-point compactification, wrong dimension for our `ℙ²`) and `Mathlib/Topology/Category/Profinite/Basic.lean:99` (profinite quotients, irrelevant). So Mathlib's `Projectivization` cannot discharge this; the chart-cover argument in Step 2 is required.

4. **Replace the axiom.** Replace `axiom PlaneCurve.instCompactSpace` at `PlaneCurve.lean:170–171` with `instance PlaneCurve.instCompactSpace` (or — preferred — let typeclass synthesis pick it up automatically once `def PlaneCurve` carries the quotient structure, since `Quotient.compactSpace`/`isCompact_univ_iff` give it for free from a `[CompactSpace (Σ i, PlaneCurveAffineDehom H i)]` instance in the slick alternative, or from a manually-stated `instance` in the explicit route). Drop the `attribute [instance]` at `PlaneCurve.lean:172`.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace lines 170–172 with a real instance (or remove the stub once typeclass inference finds it via the quotient).
- (likely new) `Jacobians/ProjectiveCurve/PlaneCurve/Atlas.lean` — helper module hosting the three `PlaneCurveAffineDehom H i` summands, the planeCurveSetoid, the per-summand `isClosed_carrier_i` lemma (generalizing `PlaneCurve.lean:82–93`), the three `K_i` closed-polydisc compactness lemmas (generalizing `Jacobians/ProjectiveCurve/Hyperelliptic/Even.lean:485–542`), the max-modulus cover lemma (Step 2B), and the final `CompactSpace` instance. Mirrors the module split `Hyperelliptic/EvenAtlas.lean` performed for the two-summand case.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds (and `lake build Jacobians.ProjectiveCurve.PlaneCurve.Atlas` if split).
- `#print axioms PlaneCurveData.genus` (downstream consumer at `PlaneCurve.lean:57–59`) no longer lists `PlaneCurve.instCompactSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `PlaneCurve` ends up encoded as a closed subspace of `Projectivization ℂ (Fin 3 → ℂ)` rather than as a chart-quotient, this entire recipe must be rewritten — and the prerequisite then becomes "first build `CompactSpace (Projectivization ℂ (Fin (n+1) → ℂ))` in Mathlib," which is a multi-week sphere-quotient project of its own (via `Metric.sphere (0 : Fin (n+1) → ℂ) 1` and the `ℂˣ`-scalar action) and warrants its own ROADMAP entry.
- If the three-chart `def PlaneCurve` lands but the gluing setoid is set up so that the three `K_i` images do **not** quotient-cover (e.g., a gluing-region offset breaks the max-modulus argument), escalate: the max-modulus selection has to match the setoid's chart-transition convention exactly.
- If the per-chart closed-polydisc compactness blows up beyond ~150 LOC per chart, consider abstracting a single `compact_closedPolydisc_of_dehomogenization` helper rather than three near-copies.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instCompactSpace.md`. Verdict: revise. Revised: 2026-06-03.
