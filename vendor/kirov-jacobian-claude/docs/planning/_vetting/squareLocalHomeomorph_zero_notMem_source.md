# Gemini 3.1 Pro critique — `squareLocalHomeomorph_zero_notMem_source`

**Model:** gemini-3.1-pro-preview
**Duration:** 81.1s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed axiom-discharge plan.

### 1. Route classification
**Wrong.** You classified this as `needs-infra` and listed `contDiffOn_symm_toOpenPartialHomeomorph` as a blocker, but your recommended Route (A) avoids the IFT source entirely and uses only standard metric topology and partial homeomorphism API. The correct route is **`mathlib-now`**. The blocker is irrelevant to Route (A) and must be removed.

### 2. Effort 1..10
**Wildly uncalibrated.** An estimate of "Effort: 6" (~1 focused week, ~150 LOC) is absurd for Route (A). This is a trivial topological contradiction: `Metric.isOpen_iff` gives a ball of radius `r > 0`, you pick `w = (r / 2 : ℂ)`, and you apply `injOn`. This is a 15-line proof. The effort is **1 or 2** (a few hours, tops). Your massive estimate only makes sense for the over-engineered Route (B).

### 3. Proof recipe
The mathematical logic in **Route (A) is brilliant and rigorously sound.** Bypassing the IFT source construction internals to instead exploit the local non-injectivity of `y ↦ y²` at `0` is exactly the right move. It cleanly forces a contradiction with the `PartialHomeomorph`'s source injectivity. 

However, there are technical execution errors in the Lean details:
* **Hallucinated Mathlib files:** You cited `Mathlib/Topology/OpenPartialHomeomorph/Defs.lean`. This file does not exist in Mathlib. The standard Mathlib type is `PartialHomeomorph` (formerly `LocalHomeomorph`), and its API lives in `Mathlib/Topology/PartialHomeomorph.lean`. If `OpenPartialHomeomorph` is a custom project wrapper, citing it as a Mathlib path is still wrong.
* **Type coercions in Step 3:** You state "pick any `w ∈ ℂ` with `0 < ‖w‖ < r`". In Lean, you cannot just use `r` (which is in `ℝ`); you will need to explicitly construct `w = (r / 2 : ℂ)` to satisfy the norm bounds smoothly. 

### 4. Textbook citations
N/A — This is a standard undergraduate analysis/topology exercise. 

### 5. What's missing or wrong
* **Contradictory metadata:** Proposing a `mathlib-now` proof while leaving the header as `needs-infra` and leaving a blocker that is explicitly bypassed. 
* **Scope creep:** Route (B) is a heavier, unnecessary upstream PR. Do not tempt the author to waste a month on IFT source bounds when a 15-line local topological proof exists. Drop Route (B) entirely.
* **Fake file paths:** As noted, `OpenPartialHomeomorph/Defs.lean` is a hallucinated Mathlib reference. 

### 6. Recommendation
**Revise.** Update the metadata to `mathlib-now` (Effort 1-2) with no blockers, strip out Route (B) entirely to prevent scope creep, and fix the hallucinated Mathlib `PartialHomeomorph` file references.

VERDICT: revise — Change the route to `mathlib-now` (Effort 1-2), drop the irrelevant blocker and Route B, and fix the hallucinated Mathlib file paths.
