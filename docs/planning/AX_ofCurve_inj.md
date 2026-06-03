# `AX_ofCurve_inj` — discharge recipe

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:257`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 9 &nbsp;&nbsp; **Est:** ~4–6 focused months for the full proof of Abel's theorem, with the immediate next infra step (Exponential Sheaf Sequence) being ~1–2 months, ~1000 LOC.
**Blocked by:** `AX_RiemannRoch`, `AX_SerreDuality`, `INFRA_ExponentialSequence`

**Statement (verbatim):**
```lean
/-- **Axiom (= Abel's theorem, curve side).** The Abel-Jacobi map is
injective when `genus X > 0`. -/
axiom AX_ofCurve_inj {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P : X) (_h : 0 < genus X) :
    Function.Injective (ofCurveImpl X P)
```

**Why it's an axiom right now:** This is the **point-level / curve side of Abel's theorem**: for a compact Riemann surface `X` of positive genus, the Abel-Jacobi map `P ↦ (∫_{P₀}^P ω_i)_i mod periods` is injective. Equivalently, two distinct points `P, Q ∈ X` are never linearly equivalent as degree-1 divisors, because `dim H⁰(X, O(P)) = 1`. This requires constructing a meromorphic function from analytic period data, bridging the analytic Jacobian and the algebraic Picard group. This construction is highly non-trivial and relies on missing infrastructure (the exponential sheaf sequence or differentials of the third kind).

**Proof recipe**

Following Griffiths–Harris (Principles of Algebraic Geometry, Ch 2.7) and standard sheaf-theoretic approaches, we discharge this via the cohomological route, constructing the meromorphic function explicitly rather than misapplying bilinear relations to open chains.

1. **Unfold the injectivity hypothesis.** Suppose `ofCurveImpl X P₀ P = ofCurveImpl X P₀ Q` for distinct `P, Q ∈ X`. Unfolding `ofCurveImpl` (`Jacobians/Axioms/AbelJacobiMap.lean:229–233`), this implies the vector `(∫_Q^P ω_1, …, ∫_Q^P ω_g) ∈ ℂ^g` lies in the period lattice $\Lambda$. This means the analytic Abel-Jacobi map maps the degree-zero divisor $P - Q$ to $0 \in \mathbb{C}^g / \Lambda$.
2. **Infrastructure prerequisites (Exponential Sheaf Sequence).** We require new bounded infrastructure: the short exact sequence of sheaves $0 \to \underline{\mathbb{Z}} \to \mathcal{O}_X \xrightarrow{\exp(2\pi i \cdot)} \mathcal{O}_X^\times \to 0$. By building the long exact sequence in cohomology, this yields the connecting homomorphism $H^1(X, \mathbb{Z}) \to H^1(X, \mathcal{O}_X) \to H^1(X, \mathcal{O}_X^\times)$.
3. **Isomorphism of the Jacobian and Picard Group.** Relate the analytic Jacobian $J(X) = H^0(X, \Omega^1)^*/H_1(X, \mathbb{Z})$ isomorphically to the cohomology group $H^1(X, \mathcal{O}_X) / \text{im}(H^1(X, \mathbb{Z}))$. Under this identification, the exact sequence from Step 2 injects the Jacobian into $H^1(X, \mathcal{O}_X^\times)$, which is identified with the Picard group $\text{Pic}(X)$ of line bundles.
4. **Construct the meromorphic function.** Because $P - Q$ maps to $0$ in $J(X)$, its image in $\text{Pic}(X)$ under the connecting homomorphism is the trivial line bundle. Therefore, the line bundle $\mathcal{O}_X(P - Q)$ is isomorphic to the trivial bundle $\mathcal{O}_X$. This isomorphism provides a global non-zero section of $\mathcal{O}_X(P - Q)$, which explicitly constitutes a global meromorphic function $g$ on $X$ with divisor precisely $P - Q$.
5. **Use Riemann–Roch + Serre duality to bound `dim H⁰(X, O(P))`.** The function $g \in H^0(X, \mathcal{O}(P)) \setminus H^0(X, \mathcal{O})$ implies $h^0(\mathcal{O}(P)) \ge 2$. Cite `AX_RiemannRoch` (`Jacobians/Axioms/RiemannRoch.lean:59`) applied to $\mathcal{O}(P)$:
   ```
   h⁰(O(P)) − h¹(O(P)) = deg(P) + 1 − g = 2 − g
   ```
   Apply `AX_SerreDuality` (`Jacobians/Axioms/SerreDuality.lean:54`) to identify $h^1(\mathcal{O}(P)) = h^0(K - P) \le h^0(K) - 1 = g - 1$ for genus $> 0$. This forces $h^0(\mathcal{O}(P)) \le 1$. The contradiction between $h^0(\mathcal{O}(P)) \ge 2$ (due to the existence of $g$) and $h^0(\mathcal{O}(P)) \le 1$ implies $P = Q$.
6. **Replace `axiom` with `theorem`.** Execute the discharge in `Jacobians/Axioms/AbelJacobiMap.lean:257` by chaining the line bundle trivialization (from the EES infrastructure) with the Riemann-Roch dimension bound.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` — replace `axiom AX_ofCurve_inj` (line 257) with `theorem`.
- `Jacobians/RiemannSurface/ExponentialSequence.lean` *(new, infra)* — defines $0 \to \underline{\mathbb{Z}} \to \mathcal{O}_X \to \mathcal{O}_X^\times \to 0$ and computes the associated long exact sequence in cohomology.
- `Jacobians/RiemannSurface/AbelTheorem.lean` *(new)* — ties the vanishing in the analytic Jacobian to the triviality of the line bundle $\mathcal{O}_X(P-Q)$, constructing the meromorphic function.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `#print axioms Jacobians.Challenge.<downstream theorem consuming injectivity>` no longer lists `AX_ofCurve_inj`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- **Sheaf cohomology mapping difficulty.** The translation from the analytic integration of paths (Abel-Jacobi map) to Čech cohomology classes in $H^1(X, \mathcal{O}_X)$ is technically demanding. If Mathlib's sheaf cohomology is not developed enough to prove this isomorphism for complex manifolds, escalate to a human to evaluate switching to the "differentials of the third kind" proof path.
- **Sheaf-cohomology layer not landed.** Step 5's invocation of `AX_RiemannRoch` requires the `Divisor` / `LineBundle` types. Escalate if these are not formalized yet.

### Gemini critique addressed
- Reclassified route to `needs-infra` and updated estimates to reflect the necessity of building bounded infrastructure (the Exponential Exact Sequence) rather than a trivial and faulty algebraic reduction.
- Scrapped the logically flawed steps from the original recipe that treated an open 1-chain as a closed 1-cycle and misapplied Riemann's bilinear relations to non-closed paths.
- Explicitly laid out the necessary cohomological construction of the meromorphic function $g$ via the EES connecting homomorphism to the Picard group, directly addressing the "circular reasoning" identified in the critique.
- Appended a requirement for `INFRA_ExponentialSequence` as a discrete sub-plan, providing a viable path forward that maps to standard textbook proofs (e.g., Griffiths-Harris).

## Sub-plans needed
- `INFRA_ExponentialSequence.md` — The exact sequence of sheaves $0 \to \underline{\mathbb{Z}} \to \mathcal{O}_X \to \mathcal{O}_X^\times \to 0$ and the extraction of its connecting homomorphism mapping $H^1(\mathcal{O}) / H^1(\mathbb{Z}) \to \text{Pic}(X)$.

---
**Vetting trail.** Critique: `_vetting/AX_ofCurve_inj.md`. Verdict: reject. Revised: 2026-06-03.