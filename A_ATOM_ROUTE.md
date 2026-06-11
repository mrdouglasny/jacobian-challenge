# A-lane route decision — `CanonicalForm17Data.ResidueAtom`

*2026-06-11, branch `feat/residue-atom` (A-lane, third launch).*

## Decision: Route 2 (trace-to-ℙ¹), structured as a frame-trace datum + proven consumer

The atom `∑_{p ∈ supp(div F) ∪ supp K} Res_p(F·ω₀) = 0` (planar coefficients) is discharged
through the Miranda §VIII.3 trace route, mirroring the PROVEN Gate-A shape
(`FormResidueTheorem.FormResidueTrace` → `residueSum_eq_zero_of_formResidueTrace`), with the
holomorphic-frame integrand `coeffAt α` replaced by the meromorphic-frame integrand
`formCoeff ω₀` of the atom itself.

### Why not the alternatives

* **Cheap route** — CONFIRMED CIRCULAR by the maintainer's inventory (`pairFun_tailMap_eq_zero`
  consumes `resSum_ext`); not touched.
* **Route 1 (engine generalization)** — the §5 slit tower (`SerreResidueRamified*`,
  `SerreResidueGateA*`, `FormTrace*`, ~40+ files) is parameterized by
  `ω₀ : HolomorphicOneForms X` end-to-end (`fibreTrace ω₀ f D`, `valueChartTrace ω₀ f Φ`,
  `AdaptedFRamified ω₀ g`, …). Re-parameterizing over `formCoeff ω₀` is the multi-week route
  recorded in `G0_BLOCKER.md`; out of reach for one session.
* **Route 3 (Tate/GACC II)** — self-contained but requires building finite-potent trace +
  commensurability theory from scratch; reserve.

### What is reusable TODAY (frame-agnostic, proven, unconditional)

* `FibreTrace` + `FibreTrace.resAt_traceCoeff'` (Lemma 3.2, one-variable, NO hypothesis —
  `residueChangeOfVariables` is discharged) — `KirovDolbeault/MeromorphicTrace.lean`,
  `ResidueChangeOfVariables.lean`.
* `finiteResidueSum_trace_eq_zero_of_fibres'` (the sphere-side combine, unconditional).
* `resAt_eq_planarCoeff_neg_one` (the contour ↔ planar local-residue bridge).
* The fibrewise `Finset` regrouping pattern (`residueSum_eq_fiberwise` /
  `residueSum_eq_infty_add_finite`) — pure combinatorics, frame-free.
* The planar down-payments: `planarCoeff_neg_one_deriv` (local `Res(dh) = 0`,
  `TailFrameGenus0.lean`) and the `deg_div` logarithmic route.

### Deliverable structure (this session)

New file `KirovDolbeault/Dolbeault/ResidueAtom.lean`:

1. `frameRes data F p` — the atom's per-point planar residue, named.
2. `frameRes_eq_zero_of_not_mem` — off `supp(div F) ∪ supp K` the integrand has nonnegative
   order, so the residue vanishes (lets the trace datum carry any superset `S`).
3. Fibrewise regrouping of `∑ frameRes` along `f.toRiemannSphere` (proven).
4. `FrameResidueTrace data F` — the trace datum (mirror of `FormResidueTrace` with the
   meromorphic-frame integrand): a `LaurentForm L` for `Tr_F(F·ω₀)`, per-centre `FibreTrace`s,
   Lemma-3.2 bookkeeping `hL32`, and the `infty_eq`/`finite_eq` fibre-residue identifications.
5. **PROVEN consumer**: `frameResSum_eq_zero_of_trace` and
   `residueAtom_of_frameTrace : (∀ F, Nonempty (FrameResidueTrace data F)) → data.ResidueAtom`.
6. **The single residual named lemma**: `FrameTraceHypothesis data :=
   ∀ F, Nonempty (FrameResidueTrace data F)` — the §VIII.3 trace assembly for the meromorphic
   frame. For `ω₀ = df` the per-sheet integrand collapses to the PLAIN value trace
   (`(f ∘ sheet)' = 1`), which is the intended closure route (the slit tower's section
   machinery `FibreRegularData g f b` is frame-free; only `fibreTrace` needs a df-analog).
7. Down-payment toward 6: the local branch-trace residue normalization at a ramification
   point (`z ↦ z^e` Laurent bookkeeping): `Res₀(ψ(z)·e·z^{e−1}) = e·a_{−e}(ψ)` — the "key new
   lemma" of the plain-trace route, proven by monomial shifting on `laurentCoeff`.

Atom status target: **conditional on exactly `FrameTraceHypothesis (canonical df datum)`**,
all other links kernel-verified; full proof if time permits via the df collapse.

## Session outcome (2026-06-11, end of A-lane session 3)

DELIVERED, all kernel-verified standard-3 (`[propext, Classical.choice, Quot.sound]`,
no `sorryAx`, no project axioms), `KirovDolbeault/Dolbeault/ResidueAtom.lean`:

1. **Skeleton complete and consumer PROVEN** (items 1–6 above): `frameRes`,
   `frameRes_eq_zero_of_not_mem`, regrouping, `FrameResidueTrace`,
   `frameResSum_eq_zero_of_trace`, `residueAtom_of_frameTraceHypothesis`, keystone
   corollaries (`h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frameTrace`,
   `exists_serreDualityData_of_genus_zero_of_frameTrace`).
2. **STRONGER than planned — positive-genus closure for EVERY datum**:
   `frameRes_eq_formFnResidue` (covector-ratio factorization `F·ω₀ = α·((F·(ω₀/α)).repair)`),
   `CanonicalForm17Data.residueAtom_of_holForm`, `residueAtom_of_kirovGenus_pos`,
   `residueAtom_of_genus_split`.  The residual `FrameTraceHypothesis` is now consumed at
   `kirovGenus X = 0` ONLY — exactly the engine-unreachable case.
3. **Down-payments toward the genus-0 closure**: `planarCoeff_neg_one_branch` (the X-side
   local branch-trace normalization at a ramification point, `e·a_{−e}`),
   `frameRes_df_read` (the `ω₀ = df` integrand collapse), `frameRes_eq_zero_of_exact_read`
   (local exactness brick), `frameRes_self_eq_zero` (`f·df = d(f²/2)` worked instance).

**Atom status: conditional on exactly ONE named residual,
`CanonicalForm17Data.FrameTraceHypothesis`, needed at `kirovGenus X = 0` only.**

Remaining for full discharge (next session): construct `FrameResidueTrace` for the
`ω₀ = df` datum — the plain value trace of `F` along `f`'s sheets (sections machinery
`FibreRegularData g f b` of the slit tower is frame-free; per-sheet integrand is
`F ∘ sheet` by `frameRes_df_read` + section-inverse `(f ∘ sheet)' = 1`), assembled per
sphere centre with `planarCoeff_neg_one_branch` at the ramified clusters.
