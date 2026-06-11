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

## T-lane session (2026-06-11, branch `feat/frame-trace`): the trace datum — wall pushed to Miranda step 1

New file `KirovDolbeault/Dolbeault/FrameTrace.lean` (wired into the aggregator).  PROVEN layers
(single residual `sorry` remains, see below):

1. **Principal-part reduction** (`frameResidueTrace_of_laurentForm`): the `FibreTrace` fields of
   `FrameResidueTrace` are a representation device — the principal-part fibre
   (`principalPartFibre L p`: one identity sheet carrying `L.R`) discharges `hL32` and the
   finite-centre trace residues definitionally.  A `FrameResidueTrace data F` exists as soon as a
   `LaurentForm L` realizes the two residue transports (**fin**: `∑_{centres} Res(L.R) = ` the
   finite-fibre `frameRes` sums; **inf**: `Res_∞(L.R) = ` the `∞`-fibre sum).
2. **Unramified frame-fibre layer** (mirror of `FormTraceFibre` with the atom's integrand):
   `frameChartIntegrand` + bridge `resAt_frameChartIntegrand` (contour ↔ planar),
   `frameFibreTrace` over a `FibreRegularData` (frame-free, reused as-is), Lemma 3.2
   `resAt_traceCoeff_frameFibreTrace`, `Finset` re-indexing `frameFibreResidueSum_eq_filter`.
3. **The `df` value-trace collapse** (`frameFibreTrace_summand_df`,
   `frameFibreTrace_traceCoeff_df`): for `ω₀ = df` and cover `= f`, the per-sheet pushforward is
   the PLAIN VALUE `F ∘ sheet` (section Jacobian `(f̂∘sheet)' = 1`), so the fibre trace
   coefficient is germ-equal to the plain value trace `w ↦ ∑ᵢ F(sheet i w)`.
4. **One-variable rationality reduction** (Miranda §VIII.3 steps 2–3,
   `exists_laurentForm_of_traceData`): from `T : ℂ → ℂ` analytic off a finite `C ⊆ ball 0 ρ` and
   meromorphic at each centre, the principal-part `LaurentForm` (`tailLaurentForm`, uniform-depth
   padding) has the SAME finite residues and the SAME `∞`-residue (junk-repaired remainder is
   entire; Cauchy–Goursat kills its large contour).  No Liouville/vanishing needed — only the
   residues transfer, which is all the trace datum requires.
5. **Assembly** (`exists_traceLaurentForm_of_functionData` → `exists_traceLaurentForm_df` →
   `frameTraceHypothesis_of_df` → `exists_canonicalData_frameTraceHypothesis`): the keystone's
   exact input shape, proven over the single residual.

### THE RESIDUAL (single named `sorry`): `exists_frameTraceFunctionData_df`

`∃ S ⊇ supp(div F) ∪ supp K, Nonempty (FrameTraceFunctionData data F f S)` — the Miranda
step-1 trace-FUNCTION datum for the plain value trace of `F` through `f`:

* `T : ℂ → ℂ`, `C : Finset ℂ` (exceptional values), `ρ` with `C ⊆ ball 0 ρ`;
* `hoff` — `T` analytic off `C` (IFT sections + conservation of number at unexceptional
  values; brick 3 above identifies the local model);
* `hmero` — `T` meromorphic at each exceptional value (the cluster/symmetric-descent argument;
  the port's `SymmetricFunctionDescent` has the weighted version — the value trace needs the
  UNWEIGHTED power-sum collapse `∑_j ζ^{jn} = m·[m|n]`, same toolbox);
* `hres` — Lemma 3.2 at each exceptional value: `Res_c T = ∑_{fibre} frameRes` (unramified part
  = brick 2+3; ramified clusters = `planarCoeff_neg_one_branch`'s `e·a₋ₑ` normalization);
* `hcover`, `hinf` — value coverage + Lemma 3.2 at `∞` (reciprocal chart).

All LaurentForm/residue bookkeeping is DONE; what remains is genuinely the trace-function
geometry (T's definition + its local analytic facts).  Next session: define `T` from the
fibre `Finset` of `f.toRiemannSphere` (`ProperMapDegreeSheets` has fibre finiteness +
`holoRepr` machinery), prove `hoff` at regular non-pole values from conservation of number,
and attack `hmero`/`hres` per exceptional class (F-pole over regular value; ramified;
`∞`-fibre).

## T2-lane session (2026-06-11, branch `feat/frame-trace-wall`): THE WALL IS CLOSED

`exists_frameTraceFunctionData_df` is **PROVEN** — no sorry anywhere in the chain.  Route: the
direct Miranda §VIII.3 step-1 construction over the proven multiplicity-patching engine, with a
fibre-saturated pole superset.  New files (all sorry-free):

1. `FrameTraceWallEngine.lean` — `valueTrace` (the junk-free plain value trace, a finsum of
   `F.holoRepr` over the fibres), the `MultiplicityPatchingData` slice decomposition (no-escape +
   disjointness as a `Finset` partition), slice enumeration by counting (each preimage has
   `localDeg ≥ 1`; `m` exhibited distinct preimages exhaust a weight-`m` slice), the regularity
   bridges (`localDeg = 1 ⟺ holoRepr-pullback derivative ≠ 0`; `K x = 0 ⟹ unramified` for
   `ω₀ = df` data), and the unramified section-sum identification (`hoff`).
2. `FrameTraceWallDescent.lean` — the UNWEIGHTED symmetric descent (mirror of the weighted
   `analyticAt_weightedSymSum_descent`, `m ∣ n` collapse), `descTail` (the descended principal
   part at an arbitrary centre `c₀`), and the meromorphic capstone
   `meromorphicAt_plainSymSum_descent`: `∑_j ψ(ζʲu) = H(c₀ + uᵐ)` with
   `planarCoeff (−1) H c₀ = m·a₋ₘ(ψ)`.
3. `FrameTraceWallCluster.lean` — `cluster_descent`: per fibre point over any finite centre (any
   multiplicity), the slice sum descends to `H` meromorphic with `Res_c H = frameRes data F r`
   (CoV along the §5 normal form `η` + `planarCoeff_neg_one_branch`); per-centre assembly
   `valueTrace_meromorphicAt_and_resAt` (`hmero` + `hres`, ramified clusters included).
4. `FrameTraceWallInfty.lean` — `infCluster_descent` (the reciprocal normal form
   `1/f̂ = ηᵐ` at each pole, weighted integrand `Q̃ = −u^{−2m}Q` rotation-invariant, residue
   `−m·aₘ(Q)` on both sides) and `valueTrace_resAtInfty_df` (Lemma 3.2 at `∞`: contour moved
   outward by annulus Cauchy, reciprocal principal part picks out `−2πi·b₁`, analytic remainder
   killed by decay + annulus invariance).

`FrameTrace.lean` assembles the datum in place (S := fibre saturation of
`supp(div F) ∪ supp K` plus the `∞`-fibre; C := the finite `f`-values of the base support —
contains every branch value since `supp K` holds all ramification points and poles), and adds
the unconditional keystone corollary `exists_canonicalData_residueAtom`.

**Atom status: UNCONDITIONAL.**  `exists_canonicalData_frameTraceHypothesis` and
`exists_canonicalData_residueAtom` are sorry-free; kernel verification recorded in
`docs/planning/T_LANE_PROGRESS.log`.
