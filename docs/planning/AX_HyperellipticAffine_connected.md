# `AX_HyperellipticAffine_connected` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean:101`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~2–3 focused weeks, ~400 LOC (one new helper file plus ~30 LOC of discharge in `Basic.lean`)
**Blocked by:** none (no other project axioms; the infra piece — path-connectedness of the affine variety `{y² = f(x)}` — is purely topological and can be built directly from existing Mathlib + the squarefree hypothesis already carried by `HyperellipticData`)

**Statement (verbatim):**
```lean
/-- **Axiom (NOT VERIFIED).** The affine hyperelliptic curve is
connected. -/
axiom AX_HyperellipticAffine_connected (H : HyperellipticData) :
    ConnectedSpace (HyperellipticAffine H)

attribute [instance] AX_HyperellipticAffine_connected
```

**Why it's an axiom right now:** The docstring states only "the affine hyperelliptic curve is connected" with no proof sketch — it is a classical fact (squarefree `f` of degree `≥ 3` ⇒ the affine variety `{y² = f(x)} ⊂ ℂ²` is irreducible, hence connected in the classical topology), but the irreducibility argument requires either (a) an irreducible-variety-implies-connected bridge that Mathlib does not yet have at the analytic / classical-topology level, or (b) a direct path-connectedness argument that uses `H.h_squarefree` (`Basic.lean:30`) to control the branch locus. Load-bearing pieces: (i) the squarefree hypothesis (without it the curve can split into two components, e.g. `y² = x²` is two lines through the origin); (ii) the fact that the projection `π : (x,y) ↦ x` is two-to-one off the (finite) root set of `f`, with the two sheets exchanged by the holomorphic involution `(x,y) ↦ (x,-y)` (already available as `HyperellipticAffine.involution` at `Jacobians/Extensions/HyperellipticOdd.lean:63`). This is `docs/subprojects.md:120` "path/irreducibility connectedness of the affine curve" and `docs/definitions-completion-plan.md:45` ("classical fact for squarefree `f` of degree ≥ 3; axiomatize as a small `AX_HyperellipticAffine_connected` subfact").

**Proof recipe**

Two viable routes — the **path-connectedness route** (recommended for Lean) is concrete and self-contained; the **irreducibility route** is conceptually cleaner but requires more algebraic-geometry scaffolding. The recipe below executes the path-connectedness route, with the irreducibility route sketched as a fallback.

Follow **Forster §1** for the topological construction of Riemann surfaces.

1. **Infra prerequisite — a `HyperellipticAffine.PathConnected` helper file.** Create `Jacobians/ProjectiveCurve/Hyperelliptic/Connected.lean` (or extend `Basic.lean`) housing the explicit path-connectedness construction. Imports: `Mathlib.Topology.Connected.PathConnected` (provides `PathConnectedSpace`, `IsPathConnected`, `IsPathConnected.image` at `.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:423`, and the priority-100 instance `PathConnectedSpace.connectedSpace` at `:607` that yields `ConnectedSpace` for free); `Mathlib.Analysis.Complex.Basic`; `Mathlib.Analysis.SpecialFunctions.Exponential` (for universal cover `Complex.isCoveringMap_exp`); the existing `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean` (for `HyperellipticAffine`, `isClosed_carrier`, the `Nonempty` witness at `:84`).

2. **Establish that `HyperellipticAffine H` is locally path-connected.** The carrier is a closed subset of `ℂ × ℂ` (`Basic.lean:63` `isClosed_carrier`). Avoid the chart machinery (since `Hyperelliptic.instChartedSpace` is not a prerequisite). Use the projection `π : HyperellipticAffine H → ℂ`, `π p := p.val.1` (already defined inline at `Basic.lean:111` inside the noncompact-space proof; lift it to a top-level `def` in the new file).

3. **Build the "two-sheets-glued-along-roots" path-construction.** Concretely: given two points `P₀ = (x₀, y₀)` and `P₁ = (x₁, y₁)` on the curve, exhibit a continuous path `γ : [0,1] → HyperellipticAffine H` from `P₀` to `P₁`. Strategy:
   - **Sub-step 3a — lift a path avoiding roots on a half-open interval.** Pick a path $x(t)$ in $\mathbb{C}$ from your starting point to a root $a$, such that $f(x(t)) \neq 0$ for $t < 1$ (the finite zero-locus is $R := \{x \in \mathbb{C} : f(x) = 0\}$; finite since `H.f ≠ 0` and `f.natDegree ≥ 3`, `Basic.lean:31`, `:88`). Map the unbranched portion $t \in [0, 1)$ through $f$ to get a path in $\mathbb{C}^\times$. Lift this path to the universal cover (the log plane) using Mathlib's `Complex.isCoveringMap_exp` and `IsCoveringMap.exists_path_lift` (taking exhaustion limits for the half-open interval). Define your continuous square root on the half-open interval as $\exp(\text{lift}(t) / 2)$.
   - **Sub-step 3b — topological limit at the branch point.** At $t=1$, the path in the base reaches the root $a \in R$. Define the path value at $t=1$ in the curve to be $(a,0)$. Prove continuity at $t=1$ purely from the ambient topology of $\mathbb{C}^2$: since $x(t) \to a$, the curve equation forces $y(t)^2 = f(x(t)) \to 0$, hence $y(t) \to 0$. This trivially completes the continuous lift without needing implicit function theorems or charts.
   - **Sub-step 3c — concatenate.** Any two points are connected by paths threading through roots: a path from $x_0$ to a root $a_1$, an identical path on the opposite sheet if a switch is needed (since $(a,0)$ is fixed by the involution `Jacobians/Extensions/HyperellipticOdd.lean:63`), and a path from $a_1$ to $x_1$. Connect these via `Path.trans` (Mathlib `Topology.Connected.PathConnected`). Squarefreeness ensures the roots exist and are distinct, preventing singularities that might disconnect the space.

4. **Package as `PathConnectedSpace` then transfer to `ConnectedSpace`.** Conclude with:
   ```lean
   instance pathConnectedSpace_HyperellipticAffine (H : HyperellipticData) :
       PathConnectedSpace (HyperellipticAffine H) := by
     refine ⟨inferInstance, fun P Q => ?_⟩    -- nonempty from Basic.lean:84
     exact ⟨constructedPath H P Q, ...⟩
   ```
   The `ConnectedSpace` instance then comes for free from the priority-100 instance `PathConnectedSpace.connectedSpace` in `.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:607`.

5. **Discharge.** In `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean` lines 99–104, replace
   ```lean
   axiom AX_HyperellipticAffine_connected (H : HyperellipticData) :
       ConnectedSpace (HyperellipticAffine H)
   attribute [instance] AX_HyperellipticAffine_connected
   ```
   with
   ```lean
   /-- Squarefree `f` of degree ≥ 3 ⇒ the affine hyperelliptic curve is
   path-connected, hence connected. -/
   instance AX_HyperellipticAffine_connected (H : HyperellipticData) :
       ConnectedSpace (HyperellipticAffine H) :=
     PathConnectedSpace.connectedSpace
   ```
   (using the instance built in Step 4; the name is kept so downstream `Hyperelliptic-instConnectedSpace` and `AX_Hyperelliptic_genus` references still resolve).

**Fallback: irreducibility route.** Mumford Red Book Ch. I §6 / Hartshorne I.1.6: an irreducible affine algebraic variety over `ℂ` is connected in the classical topology. Sub-steps: (a) show the ideal `(y² − f(x)) ⊂ ℂ[x,y]` is prime when `f` is squarefree (Reid §2.2 Lemma; reduces to: `y² − f(x)` is irreducible in `ℂ[x][y]` because it is degree-2 in `y` and `f` has no square factor, so it has no factorization `(y − g(x))(y + g(x))`); (b) invoke "irreducible affine variety ⇒ connected in classical topology" (Mumford Ch. I §6 Cor 1; Hartshorne I.1.6). This route is preferable if the project later acquires an irreducible-affine-variety-implies-connected lemma; it is *not* recommended now because that bridge is not in Mathlib.

**Next discrete deliverable.** **Sub-step 3a/3b alone** — prove the existence of a continuous lift to the curve for a path in $\mathbb{C}$ that ends at a root, using `Complex.isCoveringMap_exp` on the half-open interval and subspace limit continuity at the endpoint.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean` — replace `axiom AX_HyperellipticAffine_connected` (lines 99–104) with an `instance` whose body is `PathConnectedSpace.connectedSpace` (or `inferInstance` if the path-connected instance is registered in `Connected.lean`).
- (new) `Jacobians/ProjectiveCurve/Hyperelliptic/Connected.lean` — houses the `PathConnectedSpace (HyperellipticAffine H)` instance (Steps 2–4); the sub-step 3a universal cover lift lemma; the sub-step 3b limit continuity lemma.
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — no signature change, but the existing axiom `Hyperelliptic.instConnectedSpace` (ROADMAP line 41, effort 1, `provable-from-other-axioms`) collapses to a one-liner now that the underlying affine connectedness is real.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.Basic` succeeds with the axiom replaced by an instance (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticAffine.instConnectedSpace` (or any downstream consumer such as `Hyperelliptic.instConnectedSpace`) no longer lists `AX_HyperellipticAffine_connected`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (or 2 if `Hyperelliptic-instConnectedSpace` is discharged in the same PR).

**Risk / escalation triggers**
- Formalizing the exhaustion limit on the half-open interval (Sub-step 3a) might require manual topology/limit API work if Mathlib's `Path` and `IsCoveringMap` infrastructure does not elegantly glue half-open lifts. Escalate if topological bookkeeping for the limits explodes.
- If the statement needs to change shape (e.g. to `PathConnectedSpace` directly, or to a `connectedSpace_iff` form), do **not** silently rewrite it — escalate, because the existing instance attribute `attribute [instance] AX_HyperellipticAffine_connected` at `Basic.lean:104` is consumed by `Hyperelliptic.instConnectedSpace` and `AX_Hyperelliptic_genus` downstream.

### Gemini critique addressed:
- **Effort estimate increased:** Bumped from 6 to 8 and updated lines of code to ~400 LOC to reflect the complexity of gluing paths and formalizing limits on half-open intervals.
- **Fixed path continuity (Sub-step 3a):** Replaced the mathematically flawed `Complex.sqrt` branch-cut approach with a rigorous path lifting argument using the universal cover via `Complex.isCoveringMap_exp` and `IsCoveringMap.exists_path_lift`.
- **Simplified branch point crossing (Sub-step 3b):** Removed the unnecessary and overcomplicated Implicit Function Theorem (IFT) approach, utilizing purely ambient subspace convergence in $\mathbb{C}^2$ to establish continuity at the roots.
- **Decoupled dependencies:** Eliminated the false dependency on `OddAtlas` local chart blockers.

---
**Vetting trail.** Critique: `_vetting/AX_HyperellipticAffine_connected.md`. Verdict: reject. Revised: 2026-06-03.