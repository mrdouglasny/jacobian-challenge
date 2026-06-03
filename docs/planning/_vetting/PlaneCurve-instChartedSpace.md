# Gemini 3.1 Pro critique — `PlaneCurve-instChartedSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 58.3s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **revise**

---

An expert review of your axiom-discharge plan for `PlaneCurve.instChartedSpace`.

### 1. Route Classification
**Correct as `needs-infra`.**
Because the underlying `PlaneCurve` type is currently an axiom stub, you physically cannot instantiate `ChartedSpace` until the topological/quotient structure is defined. The plan acknowledges this.

### 2. Effort Estimate
**Underestimated (6 $\to$ 8).**
Building a multi-chart atlas on a quotient manifold, wrestling with `PartialHomeomorph` pushforwards, and specifically extracting 1D subtype charts from 2D ambient IFT homeomorphisms is notoriously painful in Lean. 250 LOC is vastly too optimistic for doing this from scratch without an existing `AffineCurveData` API.

### 3. Proof Recipe & Logical Gaps
The overarching architectural strategy (a 3-summand quotient over affine patches) is correct for this project’s constraints, but the tactical execution contains severe hallucinations and gaps:

* **Hallucinated Mathlib API:** `OpenPartialHomeomorph` does not exist in Mathlib v4.30 (the type is `PartialHomeomorph`). Furthermore, `OpenPartialHomeomorph.lift_openEmbedding` is hallucinated. Pushing a chart forward along an open embedding `e` requires manually assembling a `PartialHomeomorph` (with `source = univ` and `target = range e`) and composing it via `PartialHomeomorph.trans`.
* **Missing Subtype Restriction:** You state you will use `ContDiffAt.toOpenPartialHomeomorph` (IFT) to get the chart. Mathlib's IFT constructs an ambient local diffeomorphism $\mathbb{C}^2 \to \mathbb{C}^2$. The recipe completely handwaves how to restrict this to the subspace $\{F_{dehom} = 0\}$ to yield a `PartialHomeomorph` to $\mathbb{C}$. You cannot just "use" the IFT directly on the subtype; you must define the projection map, use the IFT to prove its ambient inverse is smooth, and rigorously build the subtype restriction. 
* **Implicit Mathematical Step (Euler's Formula):** You claim the local parametrization follows from "whichever partial derivative is nonzero by `H.h_smooth`". But `H.h_smooth` is a condition on the *homogeneous* polynomial in 3 variables. To know that the dehomogenized polynomial has a non-vanishing partial derivative on the affine zero-locus, you must apply Euler's homogeneous function theorem ($\sum x_i \partial_i F = d \cdot F$). This is completely omitted from the plan.

### 4. Textbook Citations
N/A. (Standard differential/algebraic geometry).

### 5. What's Missing or Wrong (Specifics)
* **Impossible Type Signature:** `dehomogenize : PlaneCurveData → Fin 3 → PlaneCurveData` is definitively wrong. `PlaneCurveData` holds a homogeneous polynomial in 3 variables. Setting one variable to 1 yields a non-homogeneous polynomial in 2 variables of degree $\le d$, which cannot physically inhabit `PlaneCurveData`. You need a new `PlaneCurveAffineData` structure or must output `MvPolynomial (Fin 2) ℂ`.
* **The "Lift" naming convention:** You use `affineLiftChartZ H a`. If it depends on `a`, it's a chart *centered* at `a`. Your `chartAt` matches on `Quotient.out q` to get *some* representative `a` and returns the chart centered at `a`. This is mathematically valid (the `PartialHomeomorph` domain will be open and contain `q`), but you must prove that the inverse image of the affine open under the quotient map is open, which requires proving the quotient map is an open map (or that the inclusions are open embeddings into the quotient). 

### 6. Recommendation
**Revise.** Fix the impossible `dehomogenize` type signature, remove the hallucinated `OpenPartialHomeomorph` API, explicitly detail the Euler's formula step to map projective smoothness to affine smoothness, and provide the exact mechanism for extracting the 1D subtype chart from the 2D ambient IFT map.

VERDICT: revise — The quotient strategy is sound, but the plan hallucinates Mathlib APIs, proposes an impossible type signature for `dehomogenize`, and completely handwaves the difficult restriction of the ambient 2D IFT chart to the 1D curve subtype.
