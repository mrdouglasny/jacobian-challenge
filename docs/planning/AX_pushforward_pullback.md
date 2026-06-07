# `AX_pushforward_pullback` — discharge recipe

> ## ⟳ Substrate refresh — 2026-06-07
>
> **Corrected blockers (the 2026-06-03 "Blocked by" line below is stale):**
> `AX_BranchLocus` is now a **theorem** (`Jacobians/Axioms/BranchLocus.lean:202`, discharged 2026-06-04), so the fiber-degree multiplication input — the common degree `d` with `∀ q, (∑' p, localOrder f p q) = d` and finite branch locus (layer A1 / step 2) — is now **available as a theorem**, not a prerequisite axiom. The **real remaining gate is still `pushforwardOneForm` becoming a real `def`** (layer A2): until the trace map has a body, the 1-form identity `f_* ∘ f^* = deg·id` is unreachable and this Jacobian-level statement cannot be proved.
>
> _Recipe below retained for the route; read it through this refresh._

**Location:** `Jacobians/Axioms/AbelJacobiMap.lean:679`
**Route:** genuine-textbook &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~4–6 focused weeks once prerequisites land, ~400–700 LOC of project code (excluding the prerequisite trace construction and the manifold-Sard / open-mapping infrastructure that must arrive first)
**Blocked by:** `pushforwardOneForm` (`Jacobians/Axioms/AbelJacobiMap.lean:146`, currently axiomatic — must be a real `def` first), `AX_BranchLocus` (`Jacobians/Axioms/BranchLocus.lean:100`), and a project-side trace identity for `pushforwardOneForm ∘ pullbackOneForm` (currently nowhere — see step 2 below). Transitively: the manifold-level Open Mapping Theorem / a Mathlib-or-bespoke Sard's lemma for non-constant holomorphic maps `X → Y` between compact Riemann surfaces (Mathlib v4.28 has Sard only for finite-dim real vector spaces, e.g. `Mathlib/MeasureTheory/Function/Jacobian.lean:598, 647` and the Hausdorff-dim version at `Mathlib/Topology/MetricSpace/HausdorffDimension.lean:560, 568` — none on manifolds).

**Statement (verbatim):**
```lean
/-- **Axiom.** The composition "pullback then pushforward" multiplies by degree. -/
axiom AX_pushforward_pullback {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (P : Jacobian Y) :
    pushforwardImpl X Y f hf (pullbackImpl X Y f hf P) = (degreeImpl f hf) • P
```

**Why it's an axiom right now:** This is the *projection / trace-degree* identity `f_* ∘ f^* = deg(f) · id` for a finite holomorphic map of compact Riemann surfaces. The classical content lives at the 1-form level — `(pushforwardOneForm f hf).comp (pullbackOneForm f hf) = (degreeImpl f hf : ℂ) • LinearMap.id` on `HolomorphicOneForm Y` — and from there the Jacobian-level statement is genuinely just contravariant dualization plus `QuotientAddGroup.map` (the linear-algebra moves in steps 5–6 below). The reason the Jacobian-level statement is not yet a theorem is *not* the abstract nonsense — it is that the 1-form identity is unreachable today: `pushforwardOneForm` (`Jacobians/Axioms/AbelJacobiMap.lean:146`) is itself a Lean `axiom` with no body, and the kernel cannot "unfold" its docstring's fiberwise sum description. The honest trace identity requires (a) `pushforwardOneForm` realized as a `noncomputable def` from the fibre-sum-with-multiplicities construction (see `docs/planning/pushforwardOneForm.md`), and (b) an honest fibre-counting computation against `AX_BranchLocus` (`Jacobians/Axioms/BranchLocus.lean:107–109`: `∀ q : Y, (∑' p : X, localOrder f p q) = d`).

**Gemini critique addressed:** The previous recipe (rejected) attempted to "unfold an axiom's docstring" and proposed inserting a *new* helper axiom `pushforwardOneForm_apply_pullback` for the fibre-sum identity. Both moves are illegitimate: Lean's kernel does not read docstrings, and replacing one axiom with another is a refactor, not a discharge. This revised plan therefore:

1. Reclassifies the route from `provable-from-other-axioms` (effort 6) to `genuine-textbook` (effort 8), reflecting that the real content sits in honest infrastructure (Sard-for-Riemann-surfaces / manifold open mapping → branch-locus regular values → fiberwise trace identity) that must be built, not asserted.
2. Refuses to introduce any helper axiom. The recipe now explicitly waits on `pushforwardOneForm` becoming a `def` (a *prerequisite* with its own discharge plan, `docs/planning/pushforwardOneForm.md`); the discharge here begins only once that def exists.
3. Lays out the real discharge chain: `AX_BranchLocus` → fiber-degree multiplication via `localOrder` → trace formula on holomorphic 1-forms via Sard + integration over generic regular-value fibres → push∘pull = deg·id by fiber counting → Jacobian-level identity via `dualMap` contravariance and `QuotientAddGroup.map`.
4. Calls out the parallel Kirov-side axiom `ambientPhi_ambientPsi_eq` (`docs/planning/ambientPhi_ambientPsi_eq.md`, ROADMAP line 269, classified `genuine-textbook`, effort 8) as the *same* mathematical content seen through the Kirov cotangent-bundle-section bridge: the right move is to prove the form-level identity once and discharge both. The recipe specifies which side carries the work.

**Proof recipe**

Textbook references: Forster Ch. I §4 (open mapping for non-constant holomorphic maps; finite fibres); Forster Ch. II §17 (trace of meromorphic differentials, residue formula, projection formula); Mumford Vol I §II.2–§II.3 ("trace of meromorphic differentials"); Griffiths–Harris Ch. 2.3 ("the trace map of a finite map", Prop. p. 137, the projection formula).

The discharge has three layers. Layers (A) and (B) are prerequisites that must land first; layer (C) is what this recipe actually closes once (A) and (B) exist.

### Layer (A) — Prerequisites that are *not* in this recipe

These are tracked by separate discharge recipes and roadmap entries; this plan is blocked until they land.

- **(A1) Manifold-level open mapping / Sard for non-constant holomorphic maps between compact Riemann surfaces.** Powers `AX_BranchLocus`. Current Mathlib has Sard only for finite-dim real vector spaces (`Mathlib/MeasureTheory/Function/Jacobian.lean:598, 647`), not between manifolds. Either: (i) lift one of these to `ChartedSpace ℂ X → ChartedSpace ℂ Y` via charts (project-side infrastructure), or (ii) prove `AX_BranchLocus` directly from the 1-dim open-mapping theorem for holomorphic functions in `ℂ` (Mathlib has `AnalyticOnNhd.isOpen_image`-style results in `Mathlib/Analysis/Analytic/...`), combined with the compactness of `X` to extract finite fibres and the connectedness of `Y` to propagate the common degree. See `docs/planning/AX_BranchLocus.md`. The output we need here is the existential body of `AX_BranchLocus`: a common degree `d : ℕ` with `0 < d`, `∀ q : Y, (∑' p : X, localOrder f p q) = d`, and finiteness of the branch locus (`Jacobians/Axioms/BranchLocus.lean:107–109`).
- **(A2) `pushforwardOneForm` as a real `noncomputable def`.** Today it is `axiom pushforwardOneForm : … HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y` (`Jacobians/Axioms/AbelJacobiMap.lean:146–151`). The discharge plan for *that* axiom (`docs/planning/pushforwardOneForm.md`, ROADMAP effort 8, genuine-textbook) constructs the trace fiberwise on regular values of `f` (steps 1–2 of that plan: unramified sum on `Y \ B`, then removable-singularity extension across the finite branch locus `B = { q : Y | ∃ p, f p = q ∧ localOrder f p q > 1 }`, finite by `AX_BranchLocus` clause 2). Until that body exists, the kernel cannot use the fiber-sum law of `pushforwardOneForm` and no proof of the 1-form trace identity in step (B) can be written. Tracking entry: ROADMAP line 173, 182.

The recipe deliberately refuses the previously-rejected "introduce a helper axiom" shortcut. If (A2) is far away, the correct status of `AX_pushforward_pullback` is *blocked*, not "easy".

### Layer (B) — The honest 1-form trace identity (prerequisite, but provable from (A))

This is the load-bearing mathematical step. It is mathematically the projection / trace–degree formula on `Ω¹`. It needs to be added as a `theorem` (not an axiom) once (A2) lands. There is also a parallel statement on the Kirov side: `ambientPhi_ambientPsi_eq` (`docs/planning/ambientPhi_ambientPsi_eq.md`, ROADMAP line 269, effort 8). Both express the *same* underlying fact and should share the same underlying argument.

Goal (target lemma, to be added either next to `pushforwardOneForm` in `Jacobians/Axioms/AbelJacobiMap.lean` or in a new file `Jacobians/RiemannSurface/OneFormTrace.lean`):

```lean
theorem oneForm_trace_pullback
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    (pushforwardOneForm f hf).comp (pullbackOneForm f hf)
      = (degreeImpl f hf : ℂ) • LinearMap.id
```

Real-content sub-steps (post (A1)+(A2)):

1. **Split `f` constant vs non-constant** matching `degreeImpl`'s case split (`Jacobians/Axioms/AbelJacobiMap.lean:566–573`).
   - **Constant case** (`∃ c : Y, ∀ x : X, f x = c`): `degreeImpl f hf = 0`, and `pushforwardOneForm f hf = 0` from the body of (A2) (the `pushforwardOneForm.md` recipe step 4 specifies the constant branch). Then both sides of the claim equal `0`. This is a small derived lemma `pushforwardOneForm_of_constant`; record it as a separate theorem once (A2) lands. (Symmetrically, `pullbackOneForm` is also `0` on a constant `f`, since the Kirov pullback `pullbackForm` is the zero linear map on constant maps; the corresponding Kirov-side lemma should be added in `Jacobians/Vendor/Kirov/HolomorphicForms.lean` and cited via the bridge `bridgeFormEquiv` used in `pullbackOneForm` at `Jacobians/Axioms/AbelJacobiMap.lean:130–138`.)
   - **Non-constant case** (`hnc : ¬ ∃ c, ∀ x, f x = c`): `degreeImpl f hf = Classical.choose (AX_BranchLocus f hf hnc)` and `0 < degreeImpl f hf`. Proceed to step 2.

2. **Trace formula on regular values (the heart).** Let `B := { q : Y | ∃ p, f p = q ∧ localOrder f p q > 1 }`. By `AX_BranchLocus` clause 2 (`Jacobians/Axioms/BranchLocus.lean:109`), `B` is finite, hence has empty interior (in the connected, T2 `Y`). Off `B`, every `q ∉ B` is a *regular value* in the Sard sense: each `p ∈ f⁻¹(q)` has `localOrder f p q = 1`, so `f` is a local biholomorphism at `p` (via `Vendor.Wallace.HolomorphicForms.mapAnalyticOrderAt`; `Jacobians/Axioms/BranchLocus.lean:69–72`). Let `d := degreeImpl f hf`; by `AX_BranchLocus` clause 1, `f⁻¹(q)` has exactly `d` points and each contributes multiplicity 1.

   At such `q ∉ B`, write `f⁻¹(q) = {p_1, …, p_d}`. The body of `pushforwardOneForm` (from (A2)) on a regular value is the unramified fibre sum
   ```
   (pushforwardOneForm f hf ω)(q) = Σ_{i=1}^{d} ((f|_{U_i})⁻¹)^* ω at q
   ```
   where each `U_i` is a chart neighbourhood at `p_i` on which `f` is a biholomorphism (cf. `docs/planning/pushforwardOneForm.md` step 1, citing `Jacobians/Vendor/Wallace/HolomorphicForms/BranchedCover.lean:115, 121–127` for `BranchedCoverData.ramificationIndex_eq_mapAnalyticOrderAt`). Now compute the composite for `ω = pullbackOneForm f hf η` with `η : HolomorphicOneForm Y`:
   ```
   ((f|_{U_i})⁻¹)^* (pullbackOneForm f hf η) at q
     = ((f|_{U_i})⁻¹)^* (f^* η) at q
     = (f ∘ (f|_{U_i})⁻¹)^* η at q                    -- contravariance of pullback (AX_pullbackOneForm_comp at AbelJacobiMap.lean:173)
     = (id_{V_i})^* η at q                            -- because f ∘ (f|_{U_i})⁻¹ = id on a neighbourhood V_i of q
     = η at q                                          -- AX_pullbackOneForm_id at AbelJacobiMap.lean:162
   ```
   Summing over the `d` regular preimages,
   ```
   (pushforwardOneForm f hf ∘ pullbackOneForm f hf) η at q = d · η at q.
   ```
   This is the fiber-counting argument from Griffiths–Harris Ch. 2.3 (the projection formula `f_*(f^*η · ω) = η · f_* ω` in the special case `ω = 1`, equivalently the trace of `f^*η`). The discharge in Lean uses the body of `pushforwardOneForm` from (A2) — which is now an honest `def`, hence unfoldable — and the existing `AX_pullbackOneForm_id` / `AX_pullbackOneForm_comp` theorems (no new axioms).

3. **Extend to all `q ∈ Y` by removability.** The identity proved in step 2 holds on the open dense `Y \ B` (`B` finite ⇒ `Y \ B` dense in a connected, T2, locally Euclidean `Y`). Both sides — `(pushforwardOneForm f hf).comp (pullbackOneForm f hf)` applied to any `η`, and `(degreeImpl f hf : ℂ) • η` — are *holomorphic* 1-forms on `Y` (the LHS by the analytic-continuation step in the body of (A2) — `pushforwardOneForm.md` step 2; the RHS trivially). Two holomorphic 1-forms agreeing on a dense set agree everywhere (cite identity theorem for holomorphic functions on a connected complex manifold; Mathlib has the 1-dim version via `AnalyticOn` `frequently_zero_iff_eventually_zero` style lemmas, e.g. via `Mathlib/Analysis/Analytic/IsolatedZeros.lean`). Conclude the equality as `HolomorphicOneForm Y` elements, hence as a `LinearMap` identity.

   **This step is the genuine textbook content that the rejected plan tried to handwave.** It cannot be done by docstring-reading; it requires both the (A2) body and identity-theorem-style propagation.

4. **Package as `oneForm_trace_pullback`.** Add the theorem in the relevant file. *No new axiom* is introduced. If the parallel Kirov-side statement `ambientPhi_ambientPsi_eq` is what is structurally easier in the project's actual Kirov module layout (`Jacobians/Vendor/Kirov/HolomorphicForms.lean`), do the heavy lifting there and transport across `Jacobians.Bridge.bridgeFormEquiv` (the bridge used by `pullbackOneForm` at `Jacobians/Axioms/AbelJacobiMap.lean:130–138`) to obtain `oneForm_trace_pullback`. Either way, exactly *one* underlying theorem.

### Layer (C) — Lifting the 1-form identity to Jacobians (the part this recipe owns)

Once layer (B)'s `oneForm_trace_pullback` is in hand, the Jacobian-level identity is honest contravariant dualization plus `QuotientAddGroup.map`. This is the *only* part that is genuinely "easy" (effort 3–4 in isolation, but the recipe's total effort is dominated by (A)+(B)).

5. **Ambient-linear-map identity.** Show
   ```lean
   theorem pushforwardAmbientLinear_comp_pullbackAmbientLinear
       (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
     (pushforwardAmbientLinear f hf).comp (pullbackAmbientLinear f hf)
       = (degreeImpl f hf : ℂ) • LinearMap.id
   ```
   (note the direction: `pushforwardAmbientLinear f hf : (Fin (genus X) → ℂ) →ₗ (Fin (genus Y) → ℂ)` at `Jacobians/Axioms/AbelJacobiMap.lean:272–284`, `pullbackAmbientLinear f hf : (Fin (genus Y) → ℂ) →ₗ (Fin (genus X) → ℂ)` at lines 289–301, so the composite goes `(Fin (genus Y) → ℂ) → (Fin (genus Y) → ℂ)` matching the Jacobian-level direction `Jacobian Y → Jacobian X → Jacobian Y`).

   Discharge: unfold both `pushforwardAmbientLinear` and `pullbackAmbientLinear`. The middle factor is
   ```
   (pullbackOneForm f hf).dualMap ∘ (pushforwardOneForm f hf).dualMap
     = ((pushforwardOneForm f hf).comp (pullbackOneForm f hf)).dualMap
   ```
   by `LinearMap.dualMap_comp_dualMap` (already cited at `Jacobians/Axioms/AbelJacobiMap.lean:514, 535` in `pushforwardAmbientLinear_comp` and `pullbackAmbientLinear_comp`). Then apply `oneForm_trace_pullback` (layer (B)) and `(c • LinearMap.id).dualMap = c • LinearMap.id` (`Mathlib.LinearAlgebra.Dual`: `LinearMap.dualMap_id`, `LinearMap.dualMap_smul`). The `eY.toLinearMap ∘ eY.symm.toLinearMap = id` collapse mirrors the existing `_id`/`_comp` pattern at `Jacobians/Axioms/AbelJacobiMap.lean:483–537`.

6. **`jacobianHomOfAmbient` of scalar multiplication.** Add a new lemma
   ```lean
   theorem jacobianHomOfAmbient_natSmul (X : Type u) … (n : ℕ) (hL : …) (P : Jacobian X) :
     jacobianHomOfAmbient X X ((n : ℂ) • LinearMap.id) hL P = n • P
   ```
   in `Jacobians/Axioms/AbelJacobiMap.lean` next to the existing `jacobianHomOfAmbient_id_apply` and `jacobianHomOfAmbient_comp_apply` (lines 383, 416). Proof skeleton: `Quotient.inductionOn` on `P`, then unfold to `QuotientAddGroup.map_mk'`. The lattice-preservation hypothesis `hL` is immediate from `Submodule.smul_mem` on the period lattice (the `periodLatticeInBasis _` is a `Submodule ℤ`, and `(n : ℂ) • v ∈ L` whenever `v ∈ L` since `ℂ`-scalar action of an integer agrees with the `ℤ`-scalar action). The scalar `(degreeImpl f hf : ℂ)` is `((n : ℕ) : ℂ)` with `n := degreeImpl f hf`, matching the natural-number scalar action on the abelian quotient `Jacobian Y`.

7. **Combine.**
   ```lean
   theorem AX_pushforward_pullback (f : X → Y) (hf : …) (P : Jacobian Y) :
       pushforwardImpl X Y f hf (pullbackImpl X Y f hf P) = (degreeImpl f hf) • P := by
     -- pullbackImpl : Jacobian Y → Jacobian X is jacobianHomOfAmbient Y X (pullbackAmbientLinear f hf) …
     -- pushforwardImpl : Jacobian X → Jacobian Y is jacobianHomOfAmbient X Y (pushforwardAmbientLinear f hf) …
     unfold pushforwardImpl pullbackImpl
     rw [← jacobianHomOfAmbient_comp_apply]            -- composite via line 416, instantiated Y → X → Y
     apply (jacobianHomOfAmbient_congr_apply (Y := Y)).symm.trans
     · exact pushforwardAmbientLinear_comp_pullbackAmbientLinear f hf  -- step 5
     · -- residual goal: jacobianHomOfAmbient Y Y ((degreeImpl f hf : ℂ) • LinearMap.id) … P = (degreeImpl f hf) • P
       exact jacobianHomOfAmbient_natSmul …                              -- step 6
   ```
   The exact tactic sequence will mirror the existing `AX_pushforward_comp_apply` proof at `Jacobians/Axioms/AbelJacobiMap.lean:599–628` (which uses the same `jacobianHomOfAmbient_comp_apply` / `jacobianHomOfAmbient_congr_apply` chain).

8. **Replace `axiom` with `theorem` at `Jacobians/Axioms/AbelJacobiMap.lean:679`.** No new axioms anywhere — verified by `python3 gate.py --repo jacobian-challenge --build Jacobians`.

**Files touched**
- `Jacobians/Axioms/AbelJacobiMap.lean` —
  - Add `pushforwardAmbientLinear_comp_pullbackAmbientLinear` (step 5) next to `pushforwardAmbientLinear_comp` / `pullbackAmbientLinear_comp` (lines 497–537).
  - Add `jacobianHomOfAmbient_natSmul` (step 6) next to `jacobianHomOfAmbient_id_apply` / `_comp_apply` (lines 383, 416).
  - Replace `axiom AX_pushforward_pullback` (line 679) with `theorem`, proof following step 7.
  - Add `pushforwardOneForm_of_constant` (constant-case helper for layer (B)) **only after (A2) lands** — it is the `pushforwardOneForm`-side analog of the existing `pullbackOneForm`-constant argument; needs the Kirov-side counterpart in `Jacobians/Vendor/Kirov/HolomorphicForms.lean`.
- `Jacobians/RiemannSurface/OneFormTrace.lean` (new file, or alongside the (A2) construction) — `oneForm_trace_pullback` (layer (B)).
- `Jacobians/Axioms/BranchLocus.lean` — no change here, but `AX_BranchLocus` (`line 100`) is structurally cited; ensure its discharge (`docs/planning/AX_BranchLocus.md`) lands before this one.
- `Jacobians/Vendor/Kirov/HolomorphicForms.lean` — coordinate with `ambientPhi_ambientPsi_eq` (`docs/planning/ambientPhi_ambientPsi_eq.md`): do the layer (B) work once, on whichever side is structurally easier, and transport via `Jacobians.Bridge.bridgeFormEquiv`.

**Acceptance**
- `lake build Jacobians.Axioms.AbelJacobiMap` succeeds.
- `grep -r AX_pushforward_pullback Jacobians` shows no consumer references the axiom (currently none; the new `theorem` is forward-looking infrastructure).
- `#print axioms <downstream theorem>` for any consumer — e.g. anything that ends up depending on the projection formula — does not list `AX_pushforward_pullback`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1, *and* does not gain any new helper axiom (gate enforces the net-axiom-decrease invariant — the previous rejected plan would have violated this).

**Risk / escalation triggers**
- **Hard block on (A2).** If `pushforwardOneForm` is still an axiom when this plan is picked up, stop and route to `docs/planning/pushforwardOneForm.md` first; do **not** introduce any helper axiom to bridge the gap. This is the exact failure mode of the previous plan.
- **Hard block on (A1) / `AX_BranchLocus`.** The fibre-counting step 2 needs `AX_BranchLocus` clause 1 with the *specific* `Classical.choose` witness `d = degreeImpl f hf` (`Jacobians/Axioms/AbelJacobiMap.lean:566–573`). If `AX_BranchLocus` is still an axiom, that is acceptable — it is one of the standing axioms — but if there is signature drift in `AX_BranchLocus` (e.g. weakening clause 1 from `∑' p : X, localOrder f p q = d` for *all* `q` to "for `q` in some generic set"), revisit step 2's regular-value extension argument.
- **Identity-theorem availability.** Step 3 needs an identity-theorem style result: a holomorphic 1-form on a compact connected complex 1-manifold vanishing on a dense open set is zero. Mathlib has the 1-dim point version in `Mathlib/Analysis/Analytic/IsolatedZeros.lean`; lifting to manifold-valued / sectionwise vanishing may need a small project-side lemma (≤ 50 LOC). If that lemma is not derivable from existing project / Mathlib pieces, escalate — it is genuine infrastructure, not a docstring claim.
- **Kirov-side coordination.** The parallel axiom `ambientPhi_ambientPsi_eq` (`docs/planning/ambientPhi_ambientPsi_eq.md`, ROADMAP line 269) is the same math. Before duplicating layer (B) here, check whether the Kirov module already has progress on its side; if so, transport the Kirov statement via `Jacobians.Bridge.bridgeFormEquiv` (`Jacobians/Axioms/AbelJacobiMap.lean:130–138`) instead of redoing the trace identity from scratch.

---
**Vetting trail.** Critique: `_vetting/AX_pushforward_pullback.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
