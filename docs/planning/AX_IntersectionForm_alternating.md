# `AX_IntersectionForm_alternating` — discharge recipe

**Location:** `Jacobians/Axioms/IntersectionForm.lean:66`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** ~2 focused months (multi-month, multi-contributor project for Mathlib algebraic topology)
**Blocked by:** `intersectionForm` (and transitively `AX_AnalyticCycleBasis`, `AX_RiemannBilinear` — see `intersectionForm.md`). Independent of `AX_IntersectionForm_perfect`.

**Statement (verbatim):**
```lean
axiom AX_IntersectionForm_alternating
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (a : H1 X x₀) :
    intersectionForm x₀ a a = 0
```

**Why it's an axiom right now:** It is a *characterizing* property of the axiom-stub `intersectionForm` (see docstring at `Jacobians/Axioms/IntersectionForm.lean:64-65`). The pairing has no underlying definition yet, so "alternating" cannot be derived from anything — it has to be assumed. Once `intersectionForm` is actually built from cup products, it will follow from the graded-commutativity of the cup product, but this depends on a massive stack of currently missing algebraic topology infrastructure.

**Proof recipe**

This is deeply blocked on missing Mathlib infrastructure (`needs-infra`). It requires a mathematical dependency tree spanning singular cohomology, cup products, and Poincaré duality before a one-step topological proof is possible.

**Infrastructure Requirements:**
1. **Singular Cohomology & Cup Products:** Build cochain complexes and singular cohomology groups over `ℤ`, along with the cup product `⌣` structure. 
   *Prereqs:* Requires formalizing the chain-level cup product and verifying it descends to cohomology. Must include the proof of graded commutativity: `α ⌣ β = (-1)^{|α||β|} (β ⌣ α)` (Hatcher *Algebraic Topology* §3.2, Theorem 3.14).
2. **Top Cohomology & Fundamental Class Isomorphism:** Build the machinery to evaluate top cohomology. 
   *Prereqs:* Requires the Universal Coefficient Theorem (UCT) or Poincaré Duality to establish `H²(X; ℤ) ≅ ℤ` for a compact orientable surface (Hatcher Thm 3.26). Crucially, this requires formally proving that evaluation on the fundamental class provides an isomorphism to `ℤ`, allowing properties of `ℤ` to reflect back to `H²`.

**Post-Infra Discharge Sequence:**
1. **Unfold `intersectionForm`:** Once `intersectionForm.md` builds the definition `intersectionForm x₀ a b = fundamentalClass.symm (cup (PD a) (PD b))`, unfold this in the goal to reach `fundamentalClass.symm (cup (PD a) (PD a)) = 0`.
2. **Apply Graded Commutativity:** For `PD a` in degree 1, invoke the new graded commutativity lemma to show `(PD a) ⌣ (PD a) = -(PD a ⌣ PD a)`. This yields `2 * ((PD a) ⌣ (PD a)) = 0` in the group `H²(X; ℤ)`.
3. **Bridge via Isomorphism:** Apply the formal isomorphism `H²(X; ℤ) ≅ ℤ` established in the infra step. The relation `2x = 0` is transported to `ℤ`.
4. **Torsion-Free Resolution:** Use the torsion-free property of `ℤ` to conclude that `2x = 0` implies `x = 0`. This rigorously proves `(PD a) ⌣ (PD a) = 0`, and thus `intersectionForm x₀ a a = 0`.
5. **Replace with Theorem:** Change `axiom AX_IntersectionForm_alternating` to a `theorem` at `Jacobians/Axioms/IntersectionForm.lean:66`.

**Files touched**
- `Jacobians/Axioms/IntersectionForm.lean` — replace `axiom AX_IntersectionForm_alternating` (lines 66–70) with a `theorem`.

**Acceptance**
- `lake build Jacobians.Axioms.IntersectionForm` succeeds.
- `#print axioms Jacobians.Axioms.AX_IntersectionForm_alternating` returns `[]` (or contains only `propext`, `Classical.choice`, `Quot.sound`).
- `lake build Jacobians.Axioms.AnalyticCycleBasis` still succeeds (the `symplectic` field at `Jacobians/Axioms/AnalyticCycleBasis.lean:238-242` uses this property).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the chosen cohomology infrastructure only exposes graded-commutativity as a chain-level identity up to chain homotopy, escalating will be necessary to build the cocycle-to-cohomology API rather than ad-hoc bridging.
- The categorical tracking to show `H²(X; ℤ) ≅ ℤ` preserves the `2x = 0` property requires explicit algebraic mappings; escalate if the isomorphism API is not robust enough to push algebra through.

### Gemini critique addressed:
- **Route Reclassified:** Changed from `provable-from-other-axioms` to `needs-infra`, acknowledging the total absence of singular cohomology and cup products in Mathlib.
- **Effort Recalibrated:** Increased Effort from 3 to 10, estimating a multi-month, multi-contributor project to build out the required algebraic topology base.
- **Recipe Overhauled:** Removed fictional Lean pseudo-code and an invalid "optional shortcut." Replaced with a rigorous mathematical dependency tree outlining the specific topological and categorical steps needed.
- **Bridging Gap Addressed:** Explicitly detailed the requirement to build machinery proving `H²(X; ℤ) ≅ ℤ` via UCT or Poincaré Duality, as resolving `2x=0` over cohomology is not a trivial `linarith`/`omega` arithmetic operation.

---
**Vetting trail.** Critique: `_vetting/AX_IntersectionForm_alternating.md`. Verdict: reject. Revised: 2026-06-03.