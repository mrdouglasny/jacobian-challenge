# Codex plan — the quotient descent `hyperellipticEvenInvol_contMDiff`

*Authored 2026-06-02 (Claude session). This is the executable recipe for the one
remaining piece of **Mσ.2**: descending the affine-summand smoothness of the
hyperelliptic involution to the quotient curve `HyperellipticEvenProj H`. The
affine halves are already done (see below). Everything here is grounded against
real Mathlib lemma signatures — no exploratory search needed.*

File to edit: `Jacobians/ProjectiveCurve/Hyperelliptic/Involution.lean`.

## Goal

```lean
theorem hyperellipticEvenInvol_contMDiff (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (hyperellipticEvenInvol H)
```

## What you can rely on (already in the file / repo)

- `HyperellipticAffine.contMDiffAt_invol (a) : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω invol a`
  and `HyperellipticAffine.contMDiff_invol`, `HyperellipticAffineInfinity.contMDiff_invol`
  — the summand smoothness, **axiom-free**, proven.
- `hyperellipticEvenInvol_mk (p) : σ ⟦p⟧ = ⟦involPre p⟧` (`rfl`, `@[simp]`). This is
  the computable handle for σ — **use it, never reason through `Quotient.out`.**
- `hyperellipticEvenInvol_continuous H`.
- In `EvenAtlas.lean` (namespace `…HyperellipticEvenProj`):
  - `affineLiftChart H h a = (HyperellipticAffine.affineChartAt a).lift_openEmbedding (isOpenEmbedding_proj_inl H h)`
  - `infinityLiftChart H h b = (HyperellipticAffine.affineChartAt (H := reverseData H h) b).lift_openEmbedding (isOpenEmbedding_proj_inr H h)`
  - `proj H p = Quotient.mk (hyperellipticEvenSetoid H) p`; `isOpenEmbedding_proj_inl`, `isOpenEmbedding_proj_inr`.
  - Four compat theorems — `affineLiftChart_compat_affineLiftChart`,
    `infinityLiftChart_compat_infinityLiftChart` (proven), and the two
    cross-summand **axioms** `affineLiftChart_compat_infinityLiftChart`,
    `infinityLiftChart_compat_affineLiftChart`. Each delivers exactly
    `ContDiffOn ℂ ω ((c.symm.trans c') : ℂ→ℂ) (c.symm.trans c').source`.
  - `instChartedSpace`: `atlas = Set.range (chartAt H hf.out)`, `chartAt = chartAt H hf.out`.
  - `instIsManifold` (already proven via `isManifold_of_contDiffOn` + `chartAt_compat`).

## Scoping (READ THIS FIRST)

- **Do NOT require axiom-freeness.** `genus_HyperellipticEven_eq` already depends on
  the two cross-summand compat *axioms*; σ built on the EvenProj manifold structure
  adds nothing to the even-genus footprint. Use `chartAt`/`extChartAt`/`IsManifold`/
  the maximal atlas freely. (`#print axioms hyperellipticEvenInvol_contMDiff` may
  legitimately list `affineLiftChart_compat_infinityLiftChart` etc. — that is fine.)
- **The `Quotient.out` trap.** `EvenAtlas.chartAt q` is `affineLiftChart … (out q)` /
  `infinityLiftChart … (out q)` with `out q` an *arbitrary* class representative —
  so `extChartAt ⟦inl a⟧` is **not** `affineLiftChart a` in general. The route below
  sidesteps this entirely by computing `ContMDiffAt` against the chart
  `affineLiftChart H h a` for the rep `a` we choose via `Quotient.inductionOn`, using
  the **maximal-atlas** independence lemma rather than `chartAt`.

## Route — maximal atlas (chosen; cleanest given the compat lemmas already exist)

The pivotal Mathlib lemma:

```lean
contMDiffWithinAt_iff_of_mem_maximalAtlas
    (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I' n M')
    (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
  ContMDiffWithinAt I I' n f s x ↔
    ContinuousWithinAt f s x ∧
      ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
        ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x)
```
(`Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:376`). With `s = univ`,
`ContMDiffAt = ContMDiffWithinAt … univ`. The model is `𝓘(ℂ,ℂ)` (self), so
`range I = univ`, `extend` is `↑chart` up to `mfld_simps`.

The whole point: pick **`e = affineLiftChart H h a`** on the source and
**`e' = affineLiftChart H h a.invol`** on the target. Then the written-in-chart
representative `e'.extend ∘ σ ∘ (e.extend).symm` is *literally the affine
representative* `affineChartAt(a.invol) ∘ invol ∘ affineChartAt(a).symm`, whose
`ContDiffWithinAt` is exactly what `HyperellipticAffine.contMDiffAt_invol a`
produces (extract it with the *same* lemma applied on the affine manifold).

### Step 1 — lift charts are in the maximal atlas

```lean
theorem affineLiftChart_mem_maximalAtlas (H) (h : ¬ Odd H.f.natDegree)
    [Fact (¬ Odd H.f.natDegree)] (a : HyperellipticAffine H) :
    affineLiftChart H h a ∈ maximalAtlas 𝓘(ℂ,ℂ) ω (HyperellipticEvenProj H)
```
Proof: `rw [maximalAtlas, mem_maximalAtlas_iff]` (HasGroupoid.lean:104 —
`e ∈ G.maximalAtlas ↔ ∀ e' ∈ atlas, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G`).
`intro e' he'`; `he'` unfolds to `e' = chartAt H hf.out q'` for some `q'`;
`rcases Quotient.out q' with a' | b'` splits `e'` into `affineLiftChart H h a'`
/ `infinityLiftChart H h b'`. Each of the two goals
`e.symm ≫ₕ e' ∈ contDiffGroupoid ω 𝓘(ℂ,ℂ)` is discharged by:
- the matching compat theorem (`affineLiftChart_compat_affineLiftChart a a'`,
  `affineLiftChart_compat_infinityLiftChart a b'`, and the swapped `a' a` / `b' a`
  for the `e'.symm ≫ₕ e` direction), packaged into groupoid membership with the
  same glue the `instIsManifold` proof uses — model the membership step on the
  pregroupoid characterization: `rw [mem_groupoid_of_pregroupoid]` then supply the
  `ContDiffOn` from compat (with `simpa [mfld_simps]` to strip the self-model
  `range id`/`preimage id`, mirroring `instIsManifold`'s `simpa only [...]`).

  **Shortcut:** factor a private lemma
  `mem_cdg_of_compat (c c' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ)
   (hcc' : ContDiffOn ℂ ω ↑(c.symm.trans c') (c.symm.trans c').source) :
   c.symm ≫ₕ c' ∈ contDiffGroupoid ω 𝓘(ℂ,ℂ)` once; `≫ₕ` is `.trans`. Reuse it 4×.

Prove `infinityLiftChart_mem_maximalAtlas` identically (compat lemmas
`infinityLiftChart_compat_{infinity,affine}…`).

### Step 2 — the chart representative is the affine one

Helper (the heart of the descent):

```lean
lemma affineLift_writtenInExtend_invol (H) (h) (a : HyperellipticAffine H) :
    ((affineLiftChart H h a.invol).extend 𝓘(ℂ,ℂ)) ∘ hyperellipticEvenInvol H ∘
        ((affineLiftChart H h a).extend 𝓘(ℂ,ℂ)).symm
      =ᶠ[𝓝 (((affineLiftChart H h a).extend 𝓘(ℂ,ℂ)) (proj_inl-image of a))]
    (HyperellipticAffine.affineChartAt a.invol).extend 𝓘(ℂ,ℂ) ∘
        HyperellipticAffine.invol ∘ ((HyperellipticAffine.affineChartAt a).extend 𝓘(ℂ,ℂ)).symm
```
(or prove the stronger pointwise `=` on the target set, whichever is easier to
feed `ContDiffWithinAt.congr`). The computation, pointwise in `z`:
- `(affineLiftChart H h a).extend.symm z` = `(proj∘inl) ((affineChartAt a).symm z)`
  via `lift_openEmbedding_symm : (e.lift_openEmbedding hf).symm = f ∘ e.symm`
  (`Constructions.lean:402`) + self-model `extend_symm = chart.symm`.
- `σ (proj (inl p)) = proj (inl p.invol)` via `hyperellipticEvenInvol_mk`
  (`σ⟦inl p⟧ = ⟦involPre (inl p)⟧ = ⟦inl p.invol⟧`) — note `proj = Quotient.mk` and
  `⟦inl p.invol⟧ = (proj∘inl) p.invol`.
- `(affineLiftChart H h a.invol).extend (proj (inl q)) = (affineChartAt a.invol) q`
  via `lift_openEmbedding_apply : (lift e hf) (f x) = e x` (`Constructions.lean:388`)
  with `f = proj∘inl`, `q = (affineChartAt a).symm z |>.invol`.
So the composite is `affineChartAt(a.invol) (invol ((affineChartAt a).symm z))` =
exactly the affine written-in-extend rep. `lift_openEmbedding_apply` needs the
point in `e.source`; restrict to the open `(affineLiftChart H h a).target` (a nbhd
of the base point) so all three rewrites apply — `filter_upwards` with that target,
exactly as the existing `contMDiffAt_invol` proof does with `e.target ∈ 𝓝 …`.

### Step 3 — assemble

```lean
theorem hyperellipticEvenInvol_contMDiff (H) [hf : Fact (¬ Odd H.f.natDegree)] :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (hyperellipticEvenInvol H) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    rcases p with a | b
    · -- q = ⟦inl a⟧, σ q = ⟦inl a.invol⟧
      rw [contMDiffAt_iff_contMDiffWithinAt_univ,            -- or work with ContMDiffAt directly
          contMDiffWithinAt_iff_of_mem_maximalAtlas
            (affineLiftChart_mem_maximalAtlas H hf.out a)
            (affineLiftChart_mem_maximalAtlas H hf.out a.invol)
            (hx := ⟨a, ChartedSpace.mem_chart_source a, rfl⟩)   -- ⟦inl a⟧ ∈ affineLiftChart source
            (hy := …)]                                          -- σ⟦inl a⟧ = ⟦inl a.invol⟧ ∈ target source
      refine ⟨(hyperellipticEvenInvol_continuous H).continuousWithinAt, ?_⟩
      -- goal: ContDiffWithinAt of the lifted rep; congr to the affine rep (Step 2),
      -- then it's exactly the rep extracted from `contMDiffAt_invol a` via the SAME
      -- maximalAtlas lemma on the affine manifold (source chart `affineChartAt a`,
      -- target `affineChartAt a.invol`, both in `subset_maximalAtlas`).
      …
    · -- q = ⟦inr b⟧: identical with infinityLiftChart + HyperellipticAffineInfinity.contMDiffAt_invol
      …
```

`hx`/`hy` source-membership: `(affineLiftChart H h a).source = (proj∘inl) '' (affineChartAt a).source`
(`lift_openEmbedding_source`, `rfl`), and `⟦inl a⟧ = (proj∘inl) a` with
`a ∈ (affineChartAt a).source` by `ChartedSpace.mem_chart_source`. For `hy`,
`σ⟦inl a⟧ = ⟦inl a.invol⟧ = (proj∘inl) a.invol`, similarly in the target chart's source.

To get the affine-side `ContDiffWithinAt` to feed Step 3: apply
`(contMDiffWithinAt_iff_of_mem_maximalAtlas …).mp (HyperellipticAffine.contMDiffAt_invol a …)`
on the **affine** manifold with `e = affineChartAt a`, `e' = affineChartAt a.invol`
(both `∈ maximalAtlas` via `subset_maximalAtlas (chart_mem_atlas …)`), yielding
`ContDiffWithinAt ℂ ω (affineChartAt(a.invol).extend ∘ invol ∘ affineChartAt(a).extend.symm) … (…)`.
Then `ContDiffWithinAt.congr_of_eventuallyEq` with Step 2 (and a point-equality for
the base point) closes the EvenProj goal. Mind that the *base points* match:
`(affineLiftChart a).extend ⟦inl a⟧ = affineChartAt a a` by `lift_openEmbedding_apply`.

## Fallback if `IsManifold`-level ContMDiff fights back

Everything downstream (Mσ.3 `pullbackInvolution`) needs only `MDifferentiable`, so a
usable intermediate target is `MDifferentiable 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) (hyperellipticEvenInvol H)`
— same proof with `mdifferentiableWithinAt_iff_of_mem_maximalAtlas` (if present) or
derived from the ContMDiff rep via `.mdifferentiableWithinAt (mod_cast le_top)`. Prefer
the full `ContMDiff` (ω) if Step 2's congr lands; drop to `MDifferentiable` only if the
`extend`/`range`/`mfld_simps` bookkeeping on the self-model becomes a tar pit.

## Alternative route (only if Step 1's groupoid glue is painful)

`proj∘inl` and `proj∘inr` are `ContMDiff` open local diffeomorphisms onto their
(open) images; `σ` restricted to `image(proj∘inl)` equals
`(proj∘inl) ∘ invol ∘ (proj∘inl).localInverse`. Build `IsLocalDiffeomorphAt`
(`Mathlib/Geometry/Manifold/LocalDiffeomorph.lean`) for `proj∘inl` from the lifted
chart, then compose smooth maps. More machinery to set up than the maximal-atlas
route, but avoids hand-packaging groupoid membership. Use only as a fallback.

## Verify-as-you-go (CLAUDE.md pre-push rule)

- Per declaration during development: `lean_run_code` with a `#check`/`example`
  exercising the *exact* signature shape (instance args, not `haveI` in the test
  TYPE — see CLAUDE.md sub-rule; `[Fact (¬ Odd …)]` is an instance arg).
- Before any push of ≥20 LOC real Lean: **`lake env lean
  Jacobians/ProjectiveCurve/Hyperelliptic/Involution.lean`** (the reliable check),
  then `lake build` for CI parity. Do NOT trust `lean_diagnostic_messages` empty
  `items` as "clean".
- After it compiles: `#print axioms hyperellipticEvenInvol_contMDiff` — expect the
  core three **plus** the two cross-summand `…_compat_…` axioms (acceptable per the
  scoping note); flag anything else (esp. `sorryAx`).

## Then continue Mσ

Back to [`Msigma-codex-handoff.md`](Msigma-codex-handoff.md) §Mσ.3 → Mσ.5 → L2.
Mσ.3's `pullbackInvolution` is defined directly on the coefficient cocycle
(`(σ*ω).coeff q z := ω.coeff (σ q) z`) — do **not** use the `pullbackOneForm`
axiom. With `hyperellipticEvenInvol_contMDiff` in hand, the cocycle-transfer and
analyticity-transfer obligations in Mσ.3 have the smooth chart-iso they need.
