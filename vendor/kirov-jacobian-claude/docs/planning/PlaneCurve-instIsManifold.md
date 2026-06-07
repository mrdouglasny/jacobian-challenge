# `PlaneCurve.instIsManifold` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:185`
**Route:** genuine-textbook &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** ~3–4 focused weeks, ~800 LOC (once `PlaneCurve` and `PlaneCurve.instChartedSpace` land)
**Blocked by:** `PlaneCurve`, `PlaneCurve.instChartedSpace`

**Statement (verbatim):**
```lean
axiom PlaneCurve.instIsManifold (H : PlaneCurveData) :
    IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H)
attribute [instance] PlaneCurve.instIsManifold
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `PlaneCurve.lean:161`. The analytic structure requires the three-affine-chart atlas (its own recipe `PlaneCurve.instChartedSpace`) to be in place first. The core mathematical difficulty is proving that all **nine** pairwise chart transitions on the three summands `{z ≠ 0}`, `{y ≠ 0}`, `{x ≠ 0}` are real-analytic (`ContDiffOn ω`). For general degree $d \ge 5$, closed-form inverses for the charts do not exist by the Abel-Ruffini theorem, so these transition analyticity proofs must rely completely on abstract applications of the Implicit Function Theorem (IFT) across projective coordinate patches.

**Proof recipe**

1. **Textbook alignment:** Follow the standard Riemann surface construction for smooth plane curves, e.g., Miranda's *Algebraic Curves and Riemann Surfaces* (Chapter II.1) or Forster's *Lectures on Riemann Surfaces* (Section 3). The core objective is proving that the transition maps between affine patches are holomorphic (`ContDiffOn ℂ ω`).
2. Set up the overarching `chartAt_compat` lemma exactly matching the 9 cases (3 diagonal, 6 cross-summand).
   - Define `chartAt_compat (H : PlaneCurveData) (q q' : PlaneCurve H) : ContDiffOn ℂ ω (((chartAt H q).symm.trans (chartAt H q')) : ℂ → ℂ) ((chartAt H q).symm.trans (chartAt H q')).source` by unfolding `chartAt` and using `rcases` on `Quotient.out q` and `Quotient.out q'`.
3. **Diagonal Cases (3):** The same-summand transitions follow from `HyperellipticAffine.affineChartAt_compat`-style "same-summand affine compatibility" lemmas. These are straightforward applications of the IFT on a single affine plane curve.
4. **Cross-Summand Transitions (6):** **Crucially, do not attempt to write closed-form chart inverses.**
   - Define the 6 explicit transition lemmas (e.g., `affineLiftChartZ_compat_affineLiftChartX`).
   - Use Mathlib's abstract IFT API (`ContDiffAt.toOpenPartialHomeomorph` / `PartialHomeomorph.contDiffOn_symm`) applied to the local defining polynomials. 
   - Since Mathlib's IFT heavily targets `ContDiff ∞` (smooth), explicitly bridge the gap to `ω` (analytic) by showing the maps are complex differentiable (`HasFDerivAt`) on their open domains, which implies `ContDiffOn ℂ ω` for functions between finite-dimensional complex vector spaces.
5. **Ambient Space Transitions:** For each cross-summand pair, define the ambient projective rational transition map (e.g., $\phi_{zx}(x, y) = (1/x, y/x)$ for $z \neq 0 \leftrightarrow x \neq 0$). 
   - Explicitly prove that on the geometric overlap region ($U_z \cap U_x$), the denominators do not vanish (e.g., $x \neq 0$).
   - Compose this ambient rational map (which is analytic away from its poles) with the abstract IFT partial homeomorphisms obtained in Step 4.
6. Assemble the manifold instance:
   ```lean
   noncomputable instance PlaneCurve.instIsManifold
       (H : PlaneCurveData) : IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H) := by
     apply isManifold_of_contDiffOn
     intro e e' he he'
     rcases he with ⟨q, rfl⟩
     rcases he' with ⟨q', rfl⟩
     simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
       Set.range_id, Set.preimage_id, id_eq, Set.inter_univ, Set.univ_inter] using
       chartAt_compat H q q'
   ```
7. Replace `axiom PlaneCurve.instIsManifold` with `noncomputable instance` in `PlaneCurve.lean`; drop the `attribute [instance]` at line 187.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace lines 185–187 with the `instance` calling `chartAt_compat`.
- `Jacobians/ProjectiveCurve/PlaneCurve/Atlas.lean` — add `chartAt_compat` plus 3 diagonal sub-lemmas (`affineLiftChartZ_compat_affineLiftChartZ`, etc.).
- `Jacobians/ProjectiveCurve/PlaneCurve/CrossCompat.lean` — new module for the 6 cross-summand compatibility sub-lemmas (fully proven, no new axioms).

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurveData.genus` no longer lists `PlaneCurve.instIsManifold`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; net axiom count drops by 1 (no new bounded axioms are permitted).

**Risk / escalation triggers**
- **Analyticity vs Smoothness gaps:** Mathlib's complex/analytic IFT (`ω`) API might be missing critical glue compared to the smooth (`∞`) case. If `ContDiffAt ℂ ω` cannot be established for the inverse implicitly defined by the polynomial, escalate.
- **Topology mismatches:** The abstract IFT `toOpenPartialHomeomorph` produces a local homeomorphism; if proving this matches the explicit quotient topology constructed in `PlaneCurve.instTopologicalSpace` requires missing `IsOpenMap` API for plane curves, escalate.

**Gemini critique addressed:**
- Reclassified route to `genuine-textbook` (citing Miranda Ch II.1 / Forster Sec 3) and increased Effort to 9 to reflect the complexity of abstract IFT over arbitrary degree polynomials.
- Eliminated the invalid axiom-proliferation strategy; all 6 cross-summand transition lemmas will be proven completely without admitting sub-axioms.
- Shifted the mathematical strategy to explicitly use Mathlib's abstract IFT API (`ContDiffAt.toOpenPartialHomeomorph`) since closed-form inverses are impossible by the Abel-Ruffini theorem for $d \ge 5$.
- Added explicit steps detailing the composition of projective transition maps (e.g., $(x, y) \mapsto (1/x, y/x)$) while verifying denominators do not vanish on overlaps, and addressed the gap between smooth (`∞`) and analytic (`ω`) IFTs.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instIsManifold.md`. Verdict: reject. Revised: 2026-06-03.