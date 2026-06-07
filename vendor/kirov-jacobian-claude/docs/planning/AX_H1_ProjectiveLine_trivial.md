# `AX_H1_ProjectiveLine_trivial` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Line/Witnesses.lean:43`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~4–6 focused weeks, ~700–900 LOC (one new helper file `Jacobians/ProjectiveCurve/Line/SimplyConnected.lean` carrying `SimplyConnectedSpace (Metric.sphere 0 1 ⊂ EuclideanSpace ℝ (Fin 3))` plus the bespoke fundamental-groupoid-colimit → vertex-group reduction this proof requires; ~20 LOC of trivial discharge inside `Witnesses.lean`). Alternatively, **route can collapse to `provable-from-other-axioms`** if a Mathlib PR adding `instance : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n+2)) 1)` (or just the `n = 2` case) is upstreamed first; then this recipe reduces to steps 2–4 only (~50 LOC, effort 3).
**Blocked by:** none (no other project axioms; the upstream gap is missing Mathlib infrastructure — `SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)` is absent at the pin, and so is any usable `FundamentalGroupoid.vanKampen` lemma — both must be built in-repo, or upstreamed, before discharge is possible)

**Statement (verbatim):**
```lean
/-- **Axiom.** The first homology of `ProjectiveLine` vanishes. Classically:
`ProjectiveLine ≃ₜ S²` (via `ProjectiveLine.stereographic`), and `S²` is
simply connected, so π₁ is trivial and `H_1 = 0`. Simple-connectedness
of `S²` is not in Mathlib at the pin, so we record the consequence for
`ProjectiveLine` directly.

Retired to a theorem when `SimplyConnectedSpace (Metric.sphere 0 1)`
lands in Mathlib (or when we choose to prove it). -/
axiom AX_H1_ProjectiveLine_trivial (x₀ : ProjectiveLine) :
    Subsingleton (H1 ProjectiveLine x₀)
```

**Why it's an axiom right now:** The docstring is candid: this is the standard `H₁(ℙ¹) = 0` fact, which (via the project's `H1 := Additive (Abelianization (FundamentalGroup _ _))` definition at `Jacobians/RiemannSurface/Homology.lean:41–42`) reduces to `π₁(ℙ¹) = 1`. The repo already realizes `ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` (`Jacobians/ProjectiveCurve/Line.lean:279–281`) via Mathlib's `onePointEquivSphereOfFinrankEq`, so the only load-bearing missing piece on the topology side is `SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`. As of the pinned Mathlib commit, `grep -r "SimplyConnectedSpace" --include="*.lean"` in the repo finds **zero** uses of `SimplyConnectedSpace` outside of this file's own docstring (`Jacobians/ProjectiveCurve/Line/Witnesses.lean:41`); ROADMAP correctly flags this as `mathlib-now [review]` because the cited Mathlib decl is absent and the effective route is `needs-infra` at effort 8 (see Gemini critique below).

**Realistic chain.** The discharge factors into four steps:
  (i)   prove `SimplyConnectedSpace (Metric.sphere 0 1)` via a van-Kampen argument on a two-disk cover (the bulk of the work, and where the effort comes from);
  (ii)  apply Hurewicz at degree 1 to extract `H₁(S²) = 0` from `π₁(S²) = 1` — concretely, `SimplyConnectedSpace → Subsingleton (FundamentalGroup …) → Subsingleton (Abelianization …) → Subsingleton (Additive …)`;
  (iii) lift the whole package along `ProjectiveLine.stereographic` (`Jacobians/ProjectiveCurve/Line.lean:279–281`) to get `SimplyConnectedSpace ProjectiveLine`;
  (iv)  extract `Subsingleton (H1 ProjectiveLine x₀)` to discharge the axiom.
Steps (ii)–(iv) are ≤ 50 LOC total; step (i) is the ~700+ LOC piece.

**Proof recipe**

Follow **Forster, *Lectures on Riemann Surfaces*, §27** ("Simple connectivity of the sphere") for the high-level structure: cover `S²` by two contractible hemispheres glued along an annulus, then van Kampen forces `π₁(S²) = 1`. The Mathlib bridge is **Hurewicz at degree 1**.

1. **Infra prerequisite — a `SimplyConnectedSpace` proof for `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.** Create `Jacobians/ProjectiveCurve/Line/SimplyConnected.lean`. Imports: `Mathlib` (for `SimplyConnectedSpace`, `FundamentalGroup`, `FundamentalGroupoid`, `Metric.sphere`, `EuclideanSpace`, `isPathConnected_sphere`). Goal:
   ```lean
   instance : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
   ```
   This is the load-bearing piece. Two viable routes; **route A is the only realistic one at the current Mathlib pin**:

   - **Route A — direct van Kampen on two hemispheres (recommended).** Cover `S²` by `U := {x ∈ S² : x 0 > -1/2}` (open upper-ish hemisphere) and `V := {x ∈ S² : x 0 < 1/2}`. Both `U` and `V` are homeomorphic to open disks in `ℝ²` and hence contractible. `U ∩ V` is an open annulus, path-connected. **At this Mathlib pin (verified by `find .lake/packages/mathlib -path "*FundamentalGroupoid*" -name "*.lean"`), there is NO `FundamentalGroupoid.vanKampen` lemma; the only `VanKampen` decl lives in `Mathlib.CategoryTheory.Limits.VanKampen` and is the colimit-theoretic notion, with no bridge to fundamental groupoids.** So the project must either upstream the van Kampen theorem for fundamental groupoids, or build a **bespoke, hand-rolled `simply_connected_of_two_simply_connected_cover` lemma** that bypasses the groupoid colimit entirely. The bespoke approach (recommended) proves directly: *given a path-connected space `X` with an open cover `X = U ∪ V` where `U, V` are open and simply connected and `U ∩ V` is path-connected, every loop in `X` is null-homotopic.* The proof subdivides any loop using a Lebesgue-number argument on the cover, then concatenates null-homotopies in `U` and `V`. **Sub-step 1a — show each hemisphere is contractible:** use the projection `(x_0, x_1, x_2) ↦ (x_1, x_2)` from the hemisphere to an open disk in `ℝ²` (in the equatorial plane), establish it as a homeomorphism, and combine with `Convex.contractibleSpace` from `Mathlib.Topology.Homotopy.Contractible` on the disk. **Sub-step 1b — package as instance.** Mathlib's `SimplyConnectedSpace` class is defined at `.lake/packages/mathlib/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:38` as `class SimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where`, where the underlying assertion is `Nonempty (FundamentalGroupoid X ≃ DiscreteCategory PUnit)`. This is **not** the elementary `PathConnectedSpace + Subsingleton (FundamentalGroup …)` form: an extra unpacking step is needed via `simply_connected_iff_paths_homotopic` (line 86) or `simply_connected_iff_loops_nullhomotopic` (line 104) of the same file, both of which **do** give the elementary characterization. Pick `simply_connected_iff_loops_nullhomotopic` and discharge directly via the bespoke lemma.

   - **Route B — Mayer–Vietoris / cellular `CWComplex` of `S²`.** Not viable at the current Mathlib pin — the `CWComplex` API in `Mathlib.AlgebraicTopology.RelativeCellComplex.*` is partial and does not deliver `π₁(S²) = 1` via cellular approximation. **Do not pursue.**

   **Path-connectedness of `S²`.** `SimplyConnectedSpace` in Mathlib **does not** auto-derive from path-connectedness — it's the other way around: `instance (priority := 100) SimplyConnectedSpace.toPathConnectedSpace` (`SimplyConnected.lean:68`) goes `SimplyConnectedSpace → PathConnectedSpace`. So we cannot dispatch `PathConnectedSpace S²` via `inferInstance`; we must construct it. Mathlib's `isPathConnected_sphere` (`.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Connected.lean:209`) gives `IsPathConnected (Metric.sphere x r)` when `1 < Module.rank ℝ E`; for `EuclideanSpace ℝ (Fin 3)` the rank is 3 so the hypothesis fires. We then upgrade `IsPathConnected` on the set to `PathConnectedSpace` on the subtype — a one-liner via `IsPathConnected.pathConnectedSpace_coe` or equivalent. **This step is small (~20 LOC) but must be tracked explicitly** — the original recipe glossed it as `inferInstance`, which fails.

2. **Transport `SimplyConnectedSpace` along `ProjectiveLine.stereographic`.** With the infra of step 1 in hand, in `SimplyConnected.lean` prove:
   ```lean
   instance : SimplyConnectedSpace ProjectiveLine :=
     (ProjectiveLine.stereographic.toHomotopyEquiv).symm.simplyConnectedSpace
   ```
   The Mathlib API `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` (`.lake/packages/mathlib/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:52`) transports `SimplyConnectedSpace` across a homotopy equivalence. A `Homeomorph` gives a `HomotopyEquiv` via `Homeomorph.toHomotopyEquiv` (verify in `Mathlib.Topology.Homotopy.Equiv`). `ProjectiveLine.stereographic` lives at `Jacobians/ProjectiveCurve/Line.lean:279–281`.

3. **Apply Hurewicz at degree 1 to discharge the axiom.** Recall `H1 ProjectiveLine x₀ = Additive (Abelianization (FundamentalGroup ProjectiveLine x₀))` (`Jacobians/RiemannSurface/Homology.lean:41–42`). Chain:
   - `SimplyConnectedSpace ProjectiveLine` ⟹ `Subsingleton (FundamentalGroup ProjectiveLine x₀)` (this is one of the elementary characterizations packed in `simply_connected_iff_paths_homotopic`, `SimplyConnected.lean:86–91`).
   - `Subsingleton G ⟹ Subsingleton (Abelianization G)`: if Mathlib lacks `Abelianization.instSubsingleton` (the repo grep above shows it absent in the searched range), inline a 3-line proof — `Abelianization G = G ⧸ commutator G`, and a subsingleton's quotient is a subsingleton via `Subsingleton.intro`.
   - `Subsingleton α ⟹ Subsingleton (Additive α)`: `Additive` is a type synonym, so `inferInstance`.
   Combine into the final theorem in `Witnesses.lean`:
   ```lean
   theorem AX_H1_ProjectiveLine_trivial (x₀ : ProjectiveLine) :
       Subsingleton (H1 ProjectiveLine x₀) := by
     haveI : SimplyConnectedSpace ProjectiveLine := inferInstance
     haveI : Subsingleton (FundamentalGroup ProjectiveLine x₀) := by
       -- via simply_connected_iff_paths_homotopic
       sorry  -- one-step unpack
     exact inferInstance  -- Additive (Abelianization (subsingleton)) is subsingleton
   ```
   (The `sorry` here is illustrative of the unpack; in the real file it becomes a one-liner once the right Mathlib name is located.)

4. **Replace `axiom` with `theorem` in `Witnesses.lean` lines 43–44.** The signature stays identical; only the body changes. The consumer `projectiveLineCycleBasis` at `Witnesses.lean:76–90` calls `AX_H1_ProjectiveLine_trivial x₀` as a term — no callsite change needed. Also delete the `Retired to a theorem when …` paragraph at lines 41–42 of the docstring.

**Gemini critique addressed.**

The Gemini 3.1 Pro critique (in `_vetting/AX_H1_ProjectiveLine_trivial.md`, verdict **revise**) raised three substantive concerns, all of which are now reflected in this revision:

1. *"Effort 6 (~250 LOC) is a massive underestimate. This is Effort 8 / 800+ LOC."*  →  **Recalibrated to effort 8, ~700–900 LOC**, with explicit breakdown: ~300–400 LOC for the topology of the hemispheres + their intersection, and ~400+ LOC for the fundamental-groupoid-colimit reduction (or its bespoke equivalent).
2. *"The plan says 'apply [vanKampen] with two contractible opens' — but Mathlib's `FundamentalGroupoid.vanKampen` does not exist at this pin; the categorical `VanKampen` in `Mathlib.CategoryTheory.Limits.VanKampen` is a colimit notion with no fundamental-groupoid bridge. Deducing `Subsingleton (FundamentalGroup X x)` from the groupoid colimit is formally brutal."*  →  **Step 1 Route A now explicitly notes the missing Mathlib decl and prescribes the bespoke `simply_connected_of_two_simply_connected_cover` lemma route (Lebesgue-number subdivision of any loop, concatenated null-homotopies in `U` and `V`), bypassing the groupoid colimit entirely.** This is the most realistic path at the current pin. The alternative — upstream `FundamentalGroupoid.vanKampen` to Mathlib first — is noted as a route that would collapse this recipe to a `provable-from-other-axioms` shape.
3. *"`SimplyConnectedSpace` packs `PathConnectedSpace`; you cannot `inferInstance` path-connectedness of the sphere — you need `Fact (1 < finrank)` and the right subtype upgrade."*  →  **Step 1 now has an explicit "Path-connectedness of `S²`" paragraph** citing `isPathConnected_sphere` (`Mathlib/Analysis/Normed/Module/Connected.lean:209`) with the `1 < Module.rank ℝ E` hypothesis discharged for `EuclideanSpace ℝ (Fin 3)`, plus the `IsPathConnected → PathConnectedSpace` subtype upgrade.

The mathematical route (Forster §27 + Hurewicz) is unchanged and endorsed by Gemini; only the formalization difficulty has been recalibrated.

**Forster pointer.** Forster §27 ("Simply connected Riemann surfaces") is where the classical proof `π₁(S²) = 1` appears in the textbook canon. The Lean port follows the same Lebesgue-number-subdivision-of-loops outline.

**Next discrete deliverable.** **Step 1, Route A, sub-step 1a alone** — prove each hemisphere `{x ∈ Metric.sphere 0 1 : x 0 > -1/2}` (in `EuclideanSpace ℝ (Fin 3)`) is contractible. This is a ~150 LOC standalone lemma in the new `SimplyConnected.lean` file, depends only on standard Mathlib (no van Kampen / no fundamental groupoid machinery yet), and unblocks sub-step 1b. The bespoke `simply_connected_of_two_simply_connected_cover` lemma (sub-step 1b) is the second, larger PR (~400+ LOC); steps 2–4 collapse to one short PR once step 1 is in.

**Files touched**
- `Jacobians/ProjectiveCurve/Line/Witnesses.lean` — replace `axiom AX_H1_ProjectiveLine_trivial` (lines 43–44) with a `theorem` whose body chains `SimplyConnectedSpace ProjectiveLine → Subsingleton (FundamentalGroup _ _) → Subsingleton (Abelianization _) → Subsingleton (Additive _)`; trim the docstring's "Retired to a theorem when …" sentence (lines 41–42); the call site at `Witnesses.lean:79–80` inside `projectiveLineCycleBasis` is left untouched.
- (new) `Jacobians/ProjectiveCurve/Line/SimplyConnected.lean` — houses:
  * the bespoke `simply_connected_of_two_simply_connected_cover` helper lemma (~400+ LOC including Lebesgue-number / subdivision plumbing);
  * `instance : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)` from `isPathConnected_sphere`;
  * contractibility of each open hemisphere (~150 LOC);
  * `instance : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`;
  * the transport `instance : SimplyConnectedSpace ProjectiveLine` along `ProjectiveLine.stereographic`.
  Imports: `Mathlib`, `Jacobians.ProjectiveCurve.Line`.
- `Jacobians/ProjectiveCurve/Line.lean` (no change to declarations, but downstream `Witnesses.lean` adds `import Jacobians.ProjectiveCurve.Line.SimplyConnected` at the top).

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Line.Witnesses` succeeds with the axiom replaced by a theorem (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.projectiveLineCycleBasis` no longer lists `AX_H1_ProjectiveLine_trivial`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the bespoke `simply_connected_of_two_simply_connected_cover` proof balloons past ~600 LOC, or if the Lebesgue-number / subdivision plumbing turns out to require additional Mathlib infrastructure that is itself missing, **escalate**: at that scale it is more cost-effective to (a) upstream a `FundamentalGroupoid.vanKampen` lemma to Mathlib, or (b) re-axiomatize this as `mathlib-now-pending` with the upstream PR identifier tracked. **Do not silently pivot to a CW / cellular route (Route B)**; the `CWComplex` API is even less mature at the pin.
- If `Abelianization.instSubsingleton` (or the trivial fact "subsingleton's abelianization is subsingleton") is not in Mathlib, this is a ≤ 5-line local lemma — fine to inline, do **not** escalate. But if a deeper `Quotient` API gap forces an extended detour, escalate.
- If the statement of `AX_H1_ProjectiveLine_trivial` would need to change shape (e.g. demanding `IsEmpty (H1 ProjectiveLine x₀)` instead of `Subsingleton`), **escalate** — the downstream `projectiveLineCycleBasis` at `Witnesses.lean:76–90` uses `Subsingleton (H1 …)` plus `Module.Basis.empty _` to build the cycle basis, and a shape change would force a rewrite of that witness as well.

---
**Vetting trail.** Critique: `_vetting/AX_H1_ProjectiveLine_trivial.md`. Verdict: revise. Revised: 2026-06-03.
