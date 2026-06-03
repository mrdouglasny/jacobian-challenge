# `pushforwardOneForm` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:146`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** months of dedicated work, 3,000+ LOC (trace formula, symmetric product infrastructure, Riemann removable singularity)
**Blocked by:** `AX_BranchLocus` (`Jacobians/Axioms/BranchLocus.lean:100`); transitively depends on `localOrder` (`Jacobians/Axioms/BranchLocus.lean:69–72`, already a `def`).

**Statement (verbatim):**
```lean
axiom pushforwardOneForm {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y
```

**Why it's an axiom right now:** The pushforward (trace) of a holomorphic 1-form along a finite cover is classically defined fiberwise: for `ω ∈ Ω¹(X)` and `q ∈ Y`, `(f_* ω)(q) = Σ_{p ∈ f⁻¹(q)} (chart-local pullback of ω at p) · 1/f'(p)` (well outside the branch locus), with a separate analytic continuation argument across the branch locus where some `f'(p) = 0`. The construction needs (i) a finite fiber (from `AX_BranchLocus`), (ii) a chart-local trace formula, (iii) `coeff` of the result satisfying `IsHolomorphicOneFormCoeff` + `SatisfiesCotangentCocycle` on `Y` (`Jacobians/RiemannSurface/OneForm.lean:69–95`), and (iv) Riemann's removable-singularity theorem to handle branch points. None of these is currently in this repo (or in Mathlib at this pin). Per the docstring at lines 140–145, multiplicities are counted by `localOrder` (`Jacobians/Axioms/BranchLocus.lean:69`); for constant `f` the pushforward is the zero map.

**Proof recipe**

Textbook reference: Mumford Vol I §II.3 ("trace of meromorphic differentials"); Griffiths-Harris Ch. 2.3 ("the trace map of a finite map"); Forster Ch. II §17 ("trace of meromorphic differentials, residue formula").

1. **Define the unramified trace strictly on $Y \setminus B$.** Get the branch locus $B \subset Y$ as a finite set from `AX_BranchLocus` (clause 2). For any $q \in Y \setminus B$, $f$ is a local homeomorphism and the fiber $f^{-1}(q)$ is a finite set of constant size. Obtain this fiber as a `Finset` via `AX_BranchLocus`. Define the trace using `Finset.sum` over this fiber. Crucially, do *not* pick explicit inverse functions with `deriv` as that requires tracking branch cuts; instead, define the trace locally via symmetric functions of the coordinates of the preimages. This yields a well-defined holomorphic 1-form strictly on the open set $Y \setminus B$.
2. **Local Algebraic Cancellation (Newton sums) at branch points.** To show the singularity at a branch point $q \in B$ is removable, we must prove boundedness. Locally, $f$ looks like $z \mapsto z^k = w$ with $k = \text{localOrder } f \ p \ q > 1$ (`Jacobians/Axioms/BranchLocus.lean:55–61, 81–94`). Pulling back involves derivatives of the inverse, producing fractional powers of $w$. Build new infrastructure for Newton sums and symmetric polynomials of local analytic functions to formalize the Galois-theoretic local argument: summing over the roots of unity $\zeta^j$ forces all negative fractional powers of $w$ to algebraically cancel out, leaving a bounded local function.
3. **Riemann Removable Singularity.** Because the trace function is bounded and holomorphic on a punctured disk around $q \in B$, it extends holomorphically across $q$. Build the missing Riemann removable singularity API from scratch (Mathlib lacks an out-of-the-box topological closure / extension theorem for this case) and apply it to extend the trace function from $Y \setminus B$ to all of $Y$.
4. **Verify the `holomorphicOneFormSubmodule Y` membership** (`Jacobians/RiemannSurface/OneForm.lean:118–142`):
   - `IsHolomorphicOneFormCoeff`: verified by the extension in step 3.
   - `SatisfiesCotangentCocycle`: each fiberwise pullback satisfies it on `X`; pushed-forward, the cocycle on `Y` follows from chain rule + linearity of `fderiv` on $Y \setminus B$, and extends continuously to $B$.
   - `IsZeroOffChartTarget`: trivial extension by zero off `(extChartAt 𝓘(ℂ) q).target`.
5. **Constant-`f` branch.** If `∃ c, ∀ x, f x = c`, define `pushforwardOneForm f hf := 0` directly (no summation needed). The classical pushforward is zero for constants because `f'(p) = 0` everywhere.
6. **ℂ-linearity in `ω`.** Define `pushforwardOneForm f hf : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y` via `LinearMap.mk'` on the coefficient construction; `map_add'` and `map_smul'` are direct on each fiberwise summand on $Y \setminus B$, which continuously extends.

Discrete sub-deliverable: **step 1 alone** (unramified trace defined rigorously on $Y \setminus B$ as a holomorphic 1-form). This PR produces a well-defined function on the unramified locus without yet proving holomorphicity across branch points.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom pushforwardOneForm` (lines 146–151) with a `noncomputable def` based on the fiberwise trace + branch-locus extension; promote `AX_pushforwardOneForm_id` and `AX_pushforwardOneForm_comp` (lines 190–193, 197–207) to `theorem`s (their discharge plans are in `AX_pushforwardOneForm_id.md` and `AX_pushforwardOneForm_comp.md`).
- (new helper) `Jacobians/RiemannSurface/OneFormTrace.lean` — new file holding the trace construction strictly on $Y \setminus B$.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Axioms.pullbackAmbientLinear` (which consumes this via `Jacobians/Axioms/AbelJacobiMap.lean:289–301`) no longer lists `pushforwardOneForm`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The removable-singularity step at branch points is a massive undertaking. If standard symmetric polynomials logic cannot map smoothly onto the analytic structure, escalate.
- If the constant-`f` case interacts badly with `Classical.choice` of fiber-degree from `AX_BranchLocus` (which requires `_hnc : ¬ ∃ c, …`, see `Jacobians/Axioms/BranchLocus.lean:106`), wrap with `by_cases` on `∃ c, ∀ x, f x = c` *before* invoking `AX_BranchLocus`, matching the pattern in `degreeImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:566–573`).
- Signature change risk: the proposed proof needs `[Nonempty X]` and `[Nonempty Y]` for several `extChartAt` invocations, but the current axiom signature does *not* assume `Nonempty`. Downstream `pushforwardAmbientLinear` (line 272–284) does assume `Nonempty`, so the change propagates cleanly — but verify before submitting.

## Gemini critique addressed:
- **Reclassified route and recalibrated effort:** Changed route to `needs-infra` and recalibrated effort to 10 (~3,000+ LOC, months of work) to reflect the heavy infrastructure required for symmetric analytic functions and removable singularities.
- **Fixed discontinuous sum logic:** Changed the definition to operate strictly on the open set $Y \setminus B$ using `Finset.sum` over the finite fiber (obtained via `AX_BranchLocus`), rather than a globally filtered `tsum` that fails analytically at branch points.
- **Added crucial algebraic cancellation step:** Included the Galois-theoretic argument (Newton sums of roots of unity) required to show that fractional powers cancel out to prove boundedness locally at branch points.
- **Removed flawed duality alternative:** Deleted the "Alternative route" which mathematically misidentified the first dual with the second dual and erroneously tried to dualize pullback without an inner product / pairing.

## Sub-plans needed
- `RiemannRemovableSingularity.md` — Riemann removable singularity theorem for bounded holomorphic functions on punctured manifolds.
- `SymmetricProductsAnalytic.md` — Infrastructure for Newton sums and symmetric polynomials of local analytic functions to formalize roots-of-unity cancellation.
---
**Vetting trail.** Critique: `_vetting/pushforwardOneForm.md`. Verdict: reject. Revised: 2026-06-03.