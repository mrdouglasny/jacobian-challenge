# `AX_pushforwardOneForm_comp` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:197`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** ~4 focused weeks, ~600–800 LOC
**Blocked by:** `pushforwardOneForm`, Riemann Removable Singularity infrastructure

**Statement (verbatim):**
```lean
axiom AX_pushforwardOneForm_comp {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] {Z : Type w} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ, ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g) :
    pushforwardOneForm (g ∘ f) (hg.comp hf) =
      (pushforwardOneForm g hg).comp (pushforwardOneForm f hf)
```

**Why it's an axiom right now:** `pushforwardOneForm` is itself an axiom (`Jacobians/Axioms/AbelJacobiMap.lean:146–151`), so composition identities about it cannot be derived — they must be assumed. Unlike `pullbackOneForm`, which is a direct forward map, the pushforward (trace) requires summing pullbacks along local inverses over the unramified locus, and extending via Riemann's Removable Singularity theorem. This analytic infrastructure does not yet exist.

**Proof recipe**

Textbook reference: Mumford Vol I §II.3 (functoriality of trace); Griffiths-Harris Ch. 2.3 ("the trace map satisfies `(g ∘ f)_* = g_* ∘ f_*`"). The proof relies strictly on local inverse branches on the unramified locus and analytic continuation over ramification points.

1. **Discharge `pushforwardOneForm` first.** Per `pushforwardOneForm.md`, `pushforwardOneForm` must be instantiated using a fiberwise-trace over local inverses on the dense open set of regular values, then analytically extended to the branch locus. 

2. **Isolate the Unramified Locus.** Identify the regular values $Z_{reg} \subset Z$ of $g \circ f$. This is a dense open set formed by the regular values of $g$ intersecting $g^{-1}(\text{regular values of } f)$. Over any point $r \in Z_{reg}$, the map $g \circ f$ is a finite covering space.

3. **Fiber decomposition on Unramified Locus.** For $r \in Z_{reg}$, the unbranched fiber of $g \circ f$ is strictly finite. The fibers decompose as `(g ∘ f)⁻¹(r) = ⋃_{q ∈ g⁻¹(r)} f⁻¹(q)`.

4. **Chain rule on Local Inverses.** The trace is defined by summing pullbacks along local inverses: `((g ∘ f)_* ω)_r = \sum_{p \in (g \circ f)^{-1}(r)} ((g \circ f)_p^{-1})^* \omega_p`. 
   By the Inverse Function Theorem, the local inverse of $g \circ f$ at $r$ through $p$ is $f_p^{-1} \circ g_q^{-1}$, where $q = f(p)$. 
   Applying `mfderiv_comp` to the *inverse branches* $f_p^{-1}$ and $g_q^{-1}$, the pullback along the composite inverse equals the pullback along $f_p^{-1}$ followed by the pullback along $g_q^{-1}$.

5. **Sum rearrangement (`Finset`).** On the unramified locus, use `Finset.sum_biUnion` to regroup the strictly finite double sum `\sum_{q \in g^{-1}(r)} \sum_{p \in f^{-1}(q)}`. The inner sum constitutes `(f_* ω)_q`, and the outer sum applies $g_*$ to the result, proving `((g ∘ f)_* ω)_r = (g_* (f_* ω))_r` on the dense open set $Z_{reg}$.

6. **Analytic Continuation (Removable Singularities).** Both sides of the equation — `pushforwardOneForm (g ∘ f) (hg.comp hf)` and `(pushforwardOneForm g hg).comp (pushforwardOneForm f hf)` — are globally defined holomorphic 1-forms on $Z$. Since they agree on the dense open set $Z_{reg}$ (the complement of the finite ramification locus), they must be identically equal everywhere. Cite the identity principle for holomorphic sections/forms.

7. **Replace `axiom` with `theorem`** at `Jacobians/Axioms/AbelJacobiMap.lean:197–207`. Signature unchanged.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_pushforwardOneForm_comp` (lines 197–207) with a `theorem`. 

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.pullbackAmbientLinear_comp` (which uses this — see `Jacobians/Axioms/AbelJacobiMap.lean:518–537`) no longer lists `AX_pushforwardOneForm_comp`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The Mathlib API for local inverses (`LocalHomeomorph` / `Inverse Function Theorem` for manifolds) may lack the lemmas needed to compute pullbacks along inverse branches.
- The Riemann Removable Singularity theorem for holomorphic forms might be missing or hard to apply across finite ramification loci; escalate if analytic continuation over the branch locus balloons the scope unexpectedly.

## Gemini critique addressed:
- **Route & Effort recalibrated**: Upgraded to `needs-infra` and 9 effort (~4 weeks). The plan now explicitly accounts for the heavy analytic infrastructure required (local inverses, removable singularities).
- **Corrected derivative direction**: Replaced forward `mfderiv_comp` on `f` and `g` with application of the chain rule and Inverse Function Theorem on the *inverse branches* `(g ∘ f)^{-1} = f^{-1} \circ g^{-1}`.
- **Removed type-theoretic shortcut**: Scrapped the "dualized" proof step, acknowledging that `pushforwardOneForm` maps forms (not duals of forms) and there is no canonical `Ω¹ ≅ Ω¹*` isomorphism.
- **Finiteness and Ramification handled**: Replaced `tsum`/`tsum_sigma` with `Finset.sum_biUnion` strictly on the unramified locus (dense open set of regular values), and added a step to bridge the gap using analytic continuation (Removable Singularities) over the branch locus.

---
**Vetting trail.** Critique: `_vetting/AX_pushforwardOneForm_comp.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
