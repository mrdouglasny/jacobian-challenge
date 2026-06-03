# `squareLocalHomeomorph_zero_notMem_source` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean:66`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 2 &nbsp;&nbsp; **Est:** a few hours, ~15 LOC
**Blocked by:** none

**Statement (verbatim):**
```lean
/-- **Narrow structural axiom.** The point `0 ∈ ℂ` is not in the
source of `squareLocalHomeomorph p hp`.

This is the only piece of `squareLocalHomeomorph_symm_ne_zero` that
isn't directly derivable from the chart's `right_inv`. It is true
because `squareLocalHomeomorph` is built from the IFT-derived
`ContDiffAt.toOpenPartialHomeomorph` on `y ↦ y²` at `p.val.2 ≠ 0`,
and the IFT's source neighborhood is bounded away from the critical
point `y = 0` of the squaring map.

Discharge requires either:
* an explicit characterization of the source of
  `ContDiffAt.toOpenPartialHomeomorph` (Mathlib does not currently
  expose one beyond `mem_toOpenPartialHomeomorph_source`), or
* a topological argument that the squaring map is not locally
  injective at `0` and any chart source containing both `0` and
  `p.val.2 ≠ 0` would witness this — which contradicts
  `OpenPartialHomeomorph.left_inv`. -/
axiom squareLocalHomeomorph_zero_notMem_source
    (p : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) :
    (0 : ℂ) ∉ (squareLocalHomeomorph (H := H) p hp).source
```

**Why it's an axiom right now:** The Mathlib API for the chart produced by
`ContDiffAt.toOpenPartialHomeomorph` (`Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean:31`)
exposes only one fact about its source: the base point lies in it
(`ContDiffAt.mem_toOpenPartialHomeomorph_source`,
`…/ContDiff.lean:43`). Underneath, the source is
`Classical.choose hf.approximates_deriv_on_open_nhds`
(`…/InverseFunctionTheorem/FDeriv.lean:115–122`), i.e. a `Classical.choose`-extracted
open neighborhood of `a` satisfying `ApproximatesLinearOn f f' s c`. There is no
public lemma "source is contained in any prescribed open `U ∋ a`" and no
"source avoids any prescribed closed set disjoint from `a`". Geometrically the
axiom is obvious: `y ↦ y²` has derivative `0` at `y = 0`, so its restriction to
any open set containing `0` is not injective; a partial homeomorphism is
injective on its source; and `p.val.2 ≠ 0` is in the source by construction, so
the source cannot also contain `0` unless `y ↦ y²` is injective on a set
containing both — which it is not. The load-bearing piece is the local
non-injectivity of `y ↦ y²` at `0` (concretely `(-y)² = y²` for any `y ≠ 0`).

**Proof recipe**

The key observation is that we do *not* need to know where the source lives, nor do we need any new Mathlib characterization of the IFT chart source. We only need: if `0` were in the source, then the squaring map would be injective on a set containing both `0` and some `y ≠ 0` (eventually), but `y² = (−y)²` breaks injectivity on every neighborhood of `0`. Concretely we exploit the chart's left inverse together with openness of the source.

1. **Set up.** Replace `axiom` at `AffineForm.lean:66` with `theorem … := by`.
   Introduce `e := squareLocalHomeomorph (H := H) p hp` and assume
   `h0 : (0 : ℂ) ∈ e.source` for contradiction. By construction
   (`OddAtlas/AffineChart.lean:126–142`) `e` is
   `hcont.toOpenPartialHomeomorph (fun y => y^2) hf (by simp)` where
   `hcont : ContDiffAt ℂ ω (fun y => y^2) p.val.2` and `p.val.2 ≠ 0` (from
   `hp : p ∈ smoothLocusY H`, unfolded via `smoothLocusY`, see use at
   `OddAtlas/AffineChart.lean:129–130`).

2. **`e` acts as `y ↦ y²` on its source.** Cite
   `ContDiffAt.toOpenPartialHomeomorph_coe` at
   `Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean:38–41`
   to get `(e : ℂ → ℂ) = fun y => y^2` definitionally. Hence for any
   `y ∈ e.source`, `e y = y^2`.

3. **Pick a small symmetric witness near `0`.** `e.source` is open
   (via the API in `Mathlib/Topology/PartialHomeomorph.lean`). Combined with
   `h0`, `e.source ∈ 𝓝 0`. So there is `r > 0` with
   `Metric.ball (0 : ℂ) r ⊆ e.source` (cite `Metric.mem_nhds_iff` and
   `Metric.isOpen_ball`). Let `w = (r / 2 : ℂ)`. Since `r > 0`, `w ≠ 0`, and because `‖w‖ = r / 2 < r`, both `w` and `-w` are in `Metric.ball (0 : ℂ) r` (which is symmetric under negation), hence in `e.source`. Furthermore, `w ≠ -w` since `2w ≠ 0` in `ℂ`.

4. **Derive contradiction from injectivity.** By step 2,
   `e w = w^2 = (-w)^2 = e (-w)`. Since both `w, -w ∈ e.source`, apply
   the partial homeomorphism's `injOn` (or via the underlying `PartialEquiv`'s
   `left_inv` pair — API found in `Mathlib/Topology/PartialHomeomorph.lean`). 
   Concretely:
   ```lean
   have h1 : e.symm (e w) = w := e.left_inv h_w_src
   have h2 : e.symm (e (-w)) = -w := e.left_inv h_negw_src
   rw [show e w = e (-w) from by simp [e_coe]; ring] at h1
   exact absurd (h1.symm.trans h2) (by intro hh; have := hh; linarith [w_ne_zero])
   ```

5. **Close.** `exact absurd (… ) (…)`. Replace `axiom` with `theorem` in
   `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean` at line 66.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean` — replace
  `axiom squareLocalHomeomorph_zero_notMem_source` at lines 66–68 with a
  `theorem` of the same signature, body following the recipe.
- (No other project file needs to change; the consumer
  `squareLocalHomeomorph_symm_ne_zero` at `AffineForm.lean:78` already cites the
  axiom by name and continues to typecheck verbatim).

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm` succeeds.
- `#print axioms` of any downstream consumer
  (`squareLocalHomeomorph_symm_ne_zero` at `AffineForm.lean:78`, or the cocycle
  proof site at `AffineForm.lean:1050`) no longer lists
  `squareLocalHomeomorph_zero_notMem_source`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS;
  axiom count drops by 1.

**Risk / escalation triggers**
- If the partial homeomorphism API does not expose an `injOn` or `left_inv`-style
  call that accepts both source memberships and the equation `e w = e (-w)` in
  ≤ 5 lines, do not implement an ad-hoc injectivity proof — escalate.
- If the symmetric-ball step fails because `e.source` turns out to be a
  `Classical.choose`-opaque neighborhood that we cannot extract a metric ball
  from (we *can* — `IsOpen` + `0 ∈ s` ⇒ `Metric.ball 0 r ⊆ s` is standard
  Mathlib), escalate.
- The recipe assumes `p.val.2 ≠ 0` (the smooth-locus hypothesis) is *not*
  needed in the proof — only the structural non-injectivity of
  `y ↦ y²` at `0` is used. If a step appears to require `p.val.2 ≠ 0` for
  injectivity, that signals a confusion: escalate before refactoring.

### Gemini critique addressed:
- **Route and Effort recalibrated:** Changed the route to `mathlib-now` and reduced the effort estimate to 2 (a few hours, ~15 LOC), recognizing that the topological proof is direct and trivial.
- **Removed blocker:** Removed `contDiffOn_symm_toOpenPartialHomeomorph` as a blocker, since the local contradiction proof bypasses the need for the IFT source internals entirely.
- **Prevented scope creep:** Deleted "Route (B)" completely to avoid tempting the implementer into an unnecessary, heavy upstream Mathlib PR.
- **Fixed hallucinatory references:** Corrected the non-existent Mathlib file path to `Mathlib/Topology/PartialHomeomorph.lean` and updated Step 3 to explicitly construct `w = (r / 2 : ℂ)` instead of using an abstract bounding condition on a real variable `r`.

---
**Vetting trail.** Critique: `_vetting/squareLocalHomeomorph_zero_notMem_source.md`. Verdict: revise. Revised: 2026-06-03.