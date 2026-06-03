# AX_AnalyticCycleBasis — discharge recipe

**Location:** `Jacobians/Axioms/AnalyticCycleBasis.lean:257`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 10 &nbsp;&nbsp; **Est:** ~1+ focused year, ~5000+ LOC (P1: Radó triangulation + 4g-gon classification)
**Blocked by:** `AX_IntersectionForm_alternating`, `AX_IntersectionForm_perfect`

**Statement (verbatim):**
```lean
/-- **Axiom.** Every compact connected Riemann surface admits a
piecewise-real-analytic symplectic ℤ-basis of `H_1(X, ℤ)`.

See the file header for motivation, proof sketches, and references.
Rating: Standard. Sources: SA (self-audit), scheduled for DT (deep
think). -/
axiom AX_AnalyticCycleBasis {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Nonempty (AnalyticCycleBasis X x₀)
```

(The companion structure `AnalyticCycleBasis` is at
`Jacobians/Axioms/AnalyticCycleBasis.lean:220–242`; it packages
`loops : Fin (2 * genus X) → AnalyticLoop X x₀`,
`isBasis : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)`, and the
symplectic identities `⟨α_i, α_j⟩ = ⟨β_i, β_j⟩ = 0`, `⟨α_i, β_j⟩ = δ_ij`
relative to `intersectionForm x₀` and the `αEmbed`/`βEmbed`
re-indexers at lines 198 and 205.)

**Why it's an axiom right now:** The file header (lines 66–124)
spells out three classical routes, none of which has the needed
infrastructure in Mathlib at the current pin. We previously considered Morse theory (P3), but this is a formalization trap requiring infinite-dimensional transversality and contains a fatal mathematical flaw regarding real-analyticity at critical point closures. Therefore, this recipe pursues the topological P1 route (Radó-triangulation plus the classification of compact oriented surfaces via the standard 4g-gon). The axiom packages a basis (subsuming `AX_H1FreeRank2g`) and equips it with piecewise-analytic representatives that downstream path integration (`pathIntegralAnalyticArc` in `Jacobians/RiemannSurface/PathIntegral.lean:79`) can consume.

**Proof recipe**

We follow the P1 (Radó triangulation + 4g-gon classification) route. Computing combinatorial intersection numbers on a topological 4g-gon via Hatcher-style algebraic topology firmly keeps this within the realm of algebraic topology, avoiding ODE stable manifolds, fractional asymptotics, and missing Mathlib transversality theorems entirely.

Sub-steps (P1):

1. **Radó's Triangulation Theorem.** Establish that the compact connected Riemann surface `X` admits a triangulation.
   **Deliverable:** `theorem exists_triangulation (X : …) : Nonempty (Triangulation X)`.

2. **Topological Surface Classification (4g-gon).** Prove that any compact, connected, orientable triangulated surface is homeomorphic to a standard $4g$-gon with its edges identified in pairs following the standard word $a_1 b_1 a_1^{-1} b_1^{-1} \dots a_g b_g a_g^{-1} b_g^{-1}$. This will require existing definitions of `genus X` (`Jacobians/RiemannSurface/Genus.lean` imported at `Jacobians/Axioms/AnalyticCycleBasis.lean:187`).
   **Deliverable:** `def surface_homeo_polygon (X : …) : X ≃ₜ PolygonQuotient (genus X)`.

3. **Piecewise Real-Analytic Representatives.** Lift the $2g$ topological edges of the $4g$-gon back to `X` via the homeomorphism, and use standard real-analytic approximation theorems on manifolds to homotope these topological loops to piecewise real-analytic arcs (using `IsAnalyticArc` at `Jacobians/RiemannSurface/AnalyticArc.lean:54`). Assemble these into `AnalyticLoop X x₀` (structure at `Jacobians/RiemannSurface/AnalyticArc.lean:95`). This will also require discharging the `concat`/`reverse` TODOs at `Jacobians/RiemannSurface/AnalyticArc.lean:101–105`.
   **Deliverable:** `def polygonLoops (X : …) (x₀ : X) : Fin (2 * genus X) → AnalyticLoop X x₀`.

4. **Cellular-to-Singular Basis Isomorphism.** The standard 4g-gon quotient gives a CW-structure with a single 0-cell, $2g$ 1-cells, and one 2-cell. Establish that the 1-cells freely generate cellular $H_1 \cong \mathbb{Z}^{2g}$, and transport this through the cellular-to-singular homology isomorphism to singular homology (`H1` at `Jacobians/RiemannSurface/Homology.lean:41`).
   **Deliverable:** `def polygonBasis (X : …) (x₀ : X) : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)`.

5. **Combinatorial Intersection Computation.** Instead of relying on non-existent algorithmic symplectic normalization, compute the intersection form purely combinatorially on the $4g$-gon CW complex. By the nature of the $a_i b_i a_i^{-1} b_i^{-1}$ identification word, algebraic topology directly gives the standard symplectic matrix $\left[\begin{smallmatrix}0 & I \\ -I & 0\end{smallmatrix}\right]$. Map this combinatorial cup product equivalent to the project's existing `intersectionForm` (`Jacobians/Axioms/IntersectionForm.lean:66` and `91`).
   **Deliverable:** `theorem polygonBasis_is_symplectic : (polygonBasis X x₀).isSymplectic`.

6. **Assemble and discharge.** Combine steps 1–5 into the final theorem.
   **Deliverable:** `theorem AX_AnalyticCycleBasis (x₀ : X) : Nonempty (AnalyticCycleBasis X x₀) := ⟨polygonLoops X x₀, polygonBasis X x₀, polygonBasis_is_symplectic⟩`.
   Replace `axiom` with `theorem` at line 257 of `Jacobians/Axioms/AnalyticCycleBasis.lean`.

**Recommended next discrete deliverable:** sub-step 1 (`exists_triangulation`). Building the formalization of abstract simplicial complexes, triangulations of topological spaces, and Radó's theorem is a cleanly bounded and independently valuable project.

**Textbook citations:**
* Forster, *Lectures on Riemann Surfaces*, **Ch. I §22** (Radó's triangulation theorem).
* Hatcher, *Algebraic Topology*, **Ch. 2.2** (Surface classification / CW structures) and **Ch. 3.3** (Poincaré Duality and intersection forms on surfaces via cup products — crucial for sub-step 5).
* Mumford, *Tata Lectures on Theta I*, **Ch. II §2** (statement of the symplectic basis property as required downstream).

**Files touched**
- `Jacobians/Axioms/AnalyticCycleBasis.lean` — replace `axiom AX_AnalyticCycleBasis` (line 257) with the theorem from sub-step 6.
- `Jacobians/Topology/Triangulation.lean` *(new)* — sub-step 1 (Radó).
- `Jacobians/Topology/SurfaceClassification.lean` *(new)* — sub-steps 2 and 4 (4g-gon CW decomposition and cellular basis).
- `Jacobians/Topology/SurfaceIntersection.lean` *(new)* — sub-step 5 (combinatorial intersection numbers on the 4g-gon mapping to singular cup product).
- `Jacobians/RiemannSurface/AnalyticArc.lean` — sub-step 3 (real-analytic approximation of topological loops and discharging `concat`/`reverse` TODOs at lines 101–105).

**Acceptance**
- `lake build Jacobians.Axioms.AnalyticCycleBasis` succeeds with `axiom AX_AnalyticCycleBasis` replaced by a `theorem`.
- `#print axioms AX_pushforwardAmbient_preserves_lattice` and `#print axioms AX_pullbackAmbient_preserves_lattice` (per `ROADMAP.md` rows at lines 187–188) no longer mention `AX_AnalyticCycleBasis`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (from 90 to 89).

**Risk / escalation triggers**
- If lifting purely topological edges of the $4g$-gon to piecewise real-analytic loops (sub-step 3) requires unattainable levels of Whitney real-analytic approximation theory, escalate. We may need to weaken the axiom to require only smooth or piecewise-$C^1$ representatives, which requires rebasing the downstream path integral.
- If establishing the strict isomorphism between the combinatorial CW-complex intersection numbers (from Hatcher) and the singular homology `intersectionForm` proves to be an infrastructure black hole, stop and surface.

## Gemini critique addressed:
- **Route Switch:** Changed proof recipe from Morse Theory (P3) to Radó triangulation + 4g-gon classification (P1), avoiding the fatal mathematical flaw where gradient flow closures fail to be real-analytic at critical point endpoints due to fractional asymptotics.
- **Effort Recalibration:** Increased Effort from 8 to 10 and timeline to "~1+ focused year, ~5000+ LOC", accurately reflecting the immense volume of algebraic and combinatorial topology required.
- **Removed Fake Mathlib Lemma:** Abandoned the gamble on a non-existent `Matrix.symplectic_normal_form` over $\mathbb{Z}$, utilizing the natural symplectic structure arising directly from the $a_i b_i a_i^{-1} b_i^{-1}$ polygon word identification.
- **Updated Citations:** Removed incorrect Forster Ch. III Morse theory references and integrated Hatcher Ch. 2.2 and 3.3 for rigorous surface classification and combinatorial cup product intersections.

---
**Vetting trail.** Critique: `_vetting/AX_AnalyticCycleBasis.md`. Verdict: reject. Revised: 2026-06-03.