# `Hyperelliptic.instIsManifold` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:87`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~3 focused weeks, ~800 LOC. Builds on top of `instChartedSpace` defined as a strict pullback; the bulk of the work is discharging the four chart-transition compatibility axioms in the odd atlas using the Implicit Function Theorem, plus the two cross-summand ones in the even atlas.
**Blocked by:** `Hyperelliptic`, `Hyperelliptic.instChartedSpace`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`, plus the transition-compatibility axioms listed below.

**Statement (verbatim):**
```lean
axiom Hyperelliptic.instIsManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H)
attribute [instance] Hyperelliptic.instIsManifold
```

**Why it's an axiom right now:** Per `docs/hyperelliptic-atlas-plan.md` §H4.2, the analytic structure requires all pairwise chart transitions in the atlas of `Hyperelliptic H` to lie in `contDiffGroupoid ω 𝓘(ℂ)`. On the even side `Hyperelliptic/EvenAtlas.lean:275-284` already produces `instance instIsManifold` via `isManifold_of_contDiffOn` + `chartAt_compat`, but it depends on two still-axiomatized cross-summand transitions (`affineLiftChart_compat_infinityLiftChart`, `infinityLiftChart_compat_affineLiftChart`, `EvenAtlas.lean:243-257`). On the odd side, the corresponding theorem does not yet exist: there is no `chartAt_compat` for `HyperellipticOdd` because four transitions through the infinity chart are still axioms (`OddAtlas/InfinityChart.lean:66-111`).

**Proof recipe**

Bounded infrastructure on top of `instChartedSpace`. Four sub-blocks; once they land, the parity-dispatch transport is algebraic.

1. **Block A — odd atlas transitions via IFT (the missing analytic core).** Discharge the four "infinity-chart × affine-chart" compatibility axioms in `Hyperelliptic/OddAtlas/InfinityChart.lean` using the Analytic Implicit Function Theorem. *Do not use formal power series inversion.* Reference: **Miranda, "Algebraic Curves and Riemann Surfaces" (Chapter II.1)**.
   - `infinityChart_compat_affineLiftProjX` (lines 66–75) — Prove analyticity on the punctured-disk overlap. Use uniformizer $t = x^g/y$ and variable $u = 1/x$. From the hyperelliptic curve equation, derive $t^2 F(u) - u = 0$ where $F$ is a polynomial with $F(0) \neq 0$.
   - Show the derivative with respect to $u$ at $(0,0)$ is non-zero.
   - Invoke the Analytic Implicit Function Theorem (via Mathlib's `PartialHomeomorph` inverse / IFT API) to conclude $u(t)$ is analytic. 
   - Deduce $x(t) = 1/u(t)$ is analytic for $t \neq 0$.
   - `affineLiftProjX_compat_infinityChart` (lines 78–87) — symmetric direction; $x \mapsto y/x^{g+1}$ on the overlap, follows from basic operations on analytic functions.
   - `infinityChart_compat_affineLiftProjY` (lines 90–99) and `affineLiftProjY_compat_infinityChart` (lines 102–111) — same proofs through the `y`-projection branch chart `HyperellipticAffine.affineChartProjY`.
   - Same-summand transitions (affine × affine through the smooth locus) follow from `HyperellipticAffine.affineChartAt_compat` directly, mirroring `EvenAtlas.lean:199-211`.
   - Assemble into an odd-side `chartAt_compat (H h) (q q' : HyperellipticOdd H h) : ContDiffOn ℂ ω ...` by `OnePoint.rec` on both `q` and `q'`, then `instance : IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h)` via `isManifold_of_contDiffOn`, port of `EvenAtlas.lean:275-284`.
2. **Block B — finish the even atlas.** Discharge `affineLiftChart_compat_infinityLiftChart` (`EvenAtlas.lean:243-248`) and `infinityLiftChart_compat_affineLiftChart` (`EvenAtlas.lean:252-257`). Per the file docstrings (`EvenAtlas.lean:232-242`), these split into four sub-cases (`projX/Y × projX/Y`); the smoothness of `x ↦ 1/x` is from `Inv.contDiffOn` style, and the polynomial-root cases use `polynomialLocalHomeomorph` machinery from `OddAtlas/AffineChart.lean`. These need `squareLocalHomeomorph_zero_notMem_source` (`AffineForm.lean:66`) and `polynomialLocalHomeomorph_no_critical_in_source` (`AffineForm.lean:247`) — which share a common Mathlib-API gap (`contDiffOn_symm_toOpenPartialHomeomorph`, see `docs/planning/contDiffOn_symm_toOpenPartialHomeomorph.md`).
3. **Block C — parity-dispatched lift.** Ensure `Hyperelliptic.instChartedSpace` is defined as a strict topological pullback (e.g., pulling back the atlas via `Homeomorph`).
   ```lean
   noncomputable instance Hyperelliptic.instIsManifold (H : HyperellipticData) :
       IsManifold 𝓘(ℂ, ℂ) ω (Hyperelliptic H) := by
     by_cases h : Odd H.f.natDegree
     · -- Transport through AX_Hyperelliptic_oddEquiv
       sorry
     · haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩
       -- Mirror through AX_Hyperelliptic_evenEquiv
       sorry
   ```
   Because `instChartedSpace` is a strict pullback along homeomorphism `e`, the transition maps on the domain are exactly `(e.trans phi).symm.trans (e.trans psi)`. This simplifies algebraically (via associativity and `e.symm.trans e = id`) to `phi.symm.trans psi`. Thus, the transition maps are propositionally identical partial homeomorphs on $\mathbb{C}$, so no custom analytic transport lemmas are needed; `chartAt_compat` from the codomain instantly solves `chartAt_compat` on the domain.
4. Replace `axiom Hyperelliptic.instIsManifold` with `noncomputable instance ...` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean` (drop line 89 `attribute [instance]`).

**Gemini critique addressed:**
- Replaced the formal power series inversion/Laurent approach in Block A with the proper algebraic Analytic Implicit Function Theorem strategy (citing Miranda Ch II.1) to avoid an impossible formalization trap.
- Updated LOC estimate to ~800 to accurately reflect the overhead of formalizing the algebraic IFT equations.
- Removed proposed analytic transport steps in Block C; specified that `Hyperelliptic.instChartedSpace` must be a strict topological pullback so that transition maps trivially simplify via partial homeomorph associativity.

**Sub-axioms to discharge first**
- `Hyperelliptic.instChartedSpace` (`Hyperelliptic.lean:81-83`; see `Hyperelliptic-instChartedSpace.md`) — *must* be implemented as an atlas pullback.
- Four OddAtlas/InfinityChart transition axioms (`OddAtlas/InfinityChart.lean:66, 78, 90, 102`; their own recipes — all effort 3).
- Two EvenAtlas cross-summand axioms (`EvenAtlas.lean:243, 252`; recipes `affineLiftChart_compat_infinityLiftChart.md`, `infinityLiftChart_compat_affineLiftChart.md`, effort 6/5).
- Two `AffineForm.lean` IFT-chart-source axioms (`AffineForm.lean:66, 247`; recipes `squareLocalHomeomorph_zero_notMem_source.md`, `polynomialLocalHomeomorph_no_critical_in_source.md`, effort 6 each — both share the `contDiffOn_symm_toOpenPartialHomeomorph` blocker).

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — convert the 4 transition axioms (lines 66–111) to theorems using algebraic IFT.
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — add `chartAt_compat` and `instance instIsManifold` for `HyperellipticOdd`.
- `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` — convert lines 243–257 to theorems.
- `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean` — convert lines 66, 247 to theorems.
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace `axiom Hyperelliptic.instIsManifold` (lines 87–89) with a `noncomputable instance` doing parity dispatch via structural pullback.
- `docs/hyperelliptic-atlas-plan.md` — mark Phase H4 complete.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `Hyperelliptic.instIsManifold`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (and clears the way for `AX_Hyperelliptic_genus`).

**Risk / escalation triggers**
- If `contDiffOn_symm_toOpenPartialHomeomorph` cannot be supplied locally (the AffineForm prerequisites refuse to discharge), the AffineForm IFT-chart-source axioms become a Mathlib-API blocker; escalate to either upstream-patch Mathlib or accept a 4–6 week delay.
- If `Hyperelliptic.instChartedSpace` was not or cannot be defined as a strict topological pullback, Block C will require massive manual `chartAt_compat` unfolding. Stop and refactor `instChartedSpace` first.
- If the derivative non-vanishing condition for the algebraic relation $t^2 F(u) - u = 0$ is surprisingly painful to prove in Mathlib's polynomial/derivative API, Block A could stall.

---
**Vetting trail.** Critique: `_vetting/Hyperelliptic-instIsManifold.md`. Verdict: revise. Revised: 2026-06-03.