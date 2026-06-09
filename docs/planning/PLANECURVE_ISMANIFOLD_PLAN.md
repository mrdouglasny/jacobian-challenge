# Discharge plan — `PlaneCurve.instIsManifold` (#52)

*2026-06-09. Claimed via comment on #52 (with a redirect offer to @daouid, whose
#117 built the underlying atlas). Scoped against the in-repo template: the
even-hyperelliptic `instIsManifold` (`EvenAtlas.lean:1205`).*

## Obligation

`IsManifold 𝓘(ℂ,ℂ) ω (PlaneCurve H)` over the #117 `ChartedSpace` instance,
whose atlas is `Set.range (chartAt H)` (`PlaneCurve/Atlas.lean:1184`). Via
`isManifold_of_contDiffOn` this reduces to: for all `q q'`,

```
ContDiffOn ℂ ω ((chartAt H q).symm.trans (chartAt H q') : ℂ → ℂ)
  ((chartAt H q).symm.trans (chartAt H q')).source
```

— exactly the shape of the even-atlas `chartAt_compat` (`EvenAtlas.lean:1191`).

## Chart inventory (from #117)

- 3 affine patches: `PlaneCurveAffine` (z=1), `PlaneCurveAffineY` (y=1),
  `PlaneCurveAffineX` (x=1), each an open embedding into `PlaneCurve H`
  (`toPlaneCurve`, `toPlaneCurveY`, `toPlaneCurveX`; ranges = `U 2/1/0`).
- Per patch, `prefChart` (Classical dite on the smooth locus) selects one of
  2 IFT charts (project to the coordinate whose ∂F ≠ 0):
  `affineChartProjY/X` (central), `affineChartProjZ_Y/X_Y` (Y-patch),
  `affineChartProjZ_X/Y_X` (X-patch) — 6 chart families, each built by
  `ContDiffAt.toOpenPartialHomeomorph` (the #99 IFT, both-sides analytic).
- `chartAt H q` picks the patch containing `q` (3-way) and lifts `prefChart`
  through the patch embedding (`centralLiftChart`/`yLiftChart`/`xLiftChart`).

## Proof structure (mirror of EvenAtlas)

1. **Per-pair compat lemmas** `*LiftChart_compat_*LiftChart` — 3×3 patch
   pairs, each with the 2×2 `prefChart` dite sub-cases ⇒ ≈ up to 36 leaf
   cases (symmetry + shared helpers reduce the distinct work, but the
   even-atlas analog needed ~90 lines for ONE cross-family pair).
2. **Same-patch pairs** (3 diagonal cases): both charts lift through the SAME
   embedding, so `lift_openEmbedding` transition = base transition on the
   affine surface; the base transition is (IFT chart)′ ∘ (IFT chart)⁻¹ —
   compositions of the #99-analytic maps. EASIEST; do first as the template.
3. **Cross-patch pairs** (6 off-diagonal up to symmetry): the transition
   threads through the projectivization coordinate change (rational maps
   `(x,y) ↦ (x/y, 1/y)` etc., with nonvanishing denominators ON the overlap
   `U_i ∩ U_j`). Analogous to the even atlas's affine↔infinity pair (the
   hard kind). Key needed lemmas: the overlap membership ⇒ coordinate ≠ 0
   extraction (cf. `proj_inr_eq_proj_inl_iff` in the even case), plus
   `ContDiffOn.div`/`inv` chains.
4. **`chartAt_compat`**: case-split on the patch selector of `chartAt` at
   both points (3×3) + the `prefChart` dites, dispatching to (1).
5. **Instance**: `isManifold_of_contDiffOn` + `rcases` on atlas membership,
   verbatim from `EvenAtlas.lean:1205-1218`.

## Key reusable assets

- `ContDiffAt.toOpenPartialHomeomorph_coe` + `contDiffOn_symm_toOpenPartialHomeomorph`
  (#99) — both directions of every base chart are analytic.
- `OpenPartialHomeomorph.lift_openEmbedding_{source,target,symm}` — unwrap
  lifted transitions (used throughout the even-atlas compat proofs).
- `range_toPlaneCurve*_eq_U*` + `isOpen_U` — overlap descriptions.
- Even-atlas compat proofs as line-by-line templates.

## Estimate & sequencing

Comparable to (likely larger than) the even-atlas compat effort — **multi-PR,
~1.5–2.5k LOC**: PR 1 = same-patch diagonal (template + 3 cases + scaffold of
`chartAt_compat` with the 6 off-diagonal cases as named `sorry`-free deferred
lemmas... NO — no sorries on main: PR 1 must keep `instIsManifold` an axiom and
only land the proved compat lemmas + infrastructure); PR 2..n = cross-patch
pairs; final PR = assemble `chartAt_compat`, convert the axiom, count 41 → 40.

## Risks

- The `prefChart` Classical dite makes the leaf case-split 2×2 per pair; need
  dite-stable simp lemmas (`affineChartAt_of_not_mem_smoothLocus*` analogs —
  check what #117 already provides).
- Cross-patch nonvanishing extraction is where the even-atlas proof spent its
  effort; expect the same.
