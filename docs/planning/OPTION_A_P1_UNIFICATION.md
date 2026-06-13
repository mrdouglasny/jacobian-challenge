# Option A — unify ℙ¹ on Kirov's `RiemannSphere` instance

> **STATUS (2026-06-13, branch `feat/p1-unify`).** Steps 1–5 IMPLEMENTED and
> per-file verified. Our `ChartedSpace`/`IsManifold` instances on
> `ProjectiveLine` are deleted; `chart0`/`chart1`/`chartAt` are now
> `@[reducible] noncomputable def` aliases of Kirov's
> `RiemannSphere.{chartCoe,chartInfty,chartAtRS}`, so the build has a single
> ℙ¹ instance. `Line`, `Line/OneForm` (Liouville), `Line/Genus`,
> `MeromorphicToP1` (`toP1_contMDiff`) and `DegreeOneGenusZero` all build;
> `DegreeOneGenusZero` needed **no** edits (the relocate's Divisor shims /
> qualified casts were band-aids for the diamond, now unnecessary). The light
> route held: no `genus_eq_kirovGenus`/`bridgeKDFormEquiv` import. One real
> wrinkle handled: the port's `chartInfty (↑0)` is junk (≠ `0`), unlike our
> old `chart1`, so `chart1_coe`/`eca_infty_coe` gained a `z ≠ 0` hypothesis
> and `hrel`'s transition derivative is computed via `EventuallyEq.fderiv_eq`
> on a punctured nbhd. Remaining: full `lake build` + `#print axioms` on the
> 24 (this PR is a pure refactor — axiom set unchanged), then Step 6 (the
> headline rewire off `AX_PeriodCycleBasis`) as a separate PR.

**Goal.** Eliminate the duplicate `ChartedSpace ℂ (OnePoint ℂ)` /
`IsManifold` instances so the whole build has **one** complex-manifold
structure on the projective line. This removes the instance diamond that
blocks the axiom-free rewiring (`DegreeOneGenusZero` line 471, and the
`toP1` flip at line 457), letting the 24 headlines drop
`AX_PeriodCycleBasis` cleanly.

**Decision (MRD, 2026-06-13).** Do option A: redirect all ℙ¹ instances to
Kirov's definition. We already depend on the port for the axiom-free
period-lattice discreteness; maintaining a *parallel* ℙ¹ that collides on
the same underlying type is the worst of both worlds.

---

## 0. Why this is cheap (the key finding)

Both projective lines are the **same type**:

| ours | port |
|------|------|
| `abbrev ProjectiveLine := OnePoint ℂ` (`Line.lean:38`) | `abbrev RiemannSphere := OnePoint ℂ` (port `ProjectiveLine.lean:55`) |

So there is *nothing to convert at the type level* — the only clash is two
`ChartedSpace ℂ (OnePoint ℂ)` instances (`Line.lean:158` vs port `:250`) and
two `IsManifold` instances (`Line.lean:187` vs port).

The port's ℙ¹ module is **light**: its transitive closure is **15 modules**
(Mathlib + `KirovDolbeault.{Genus,SmoothPathCore}`) and does **not** contain
the Serre/`FormTrace` residue chain. The 303-module explosion that bit the
relocate comes from K-LITE's *residue* dependency, **not** from ℙ¹. So
importing the port's ℙ¹ into our foundational `Line.lean` costs ~15 light
modules — acceptable.

The two atlases are essentially the same maps:

- our `chart0 = (OnePoint.isOpenEmbedding_coe).toOpenPartialHomeomorph.symm`
  ≡ port `chartCoe` (same construction — defeq or one-line `ext`);
- our `chart1` (`∞↦0`, `z↦z⁻¹`, manual `where`) = port `chartInfty`
  (same map, built via `invMap`) — **propositionally** equal, not defeq;
- our `chartAt = if p = ∞ …` vs port `chartAtRS = p.elim …` — agree
  pointwise, different definition (decidability vs eliminator).

⇒ The instances are **not** defeq, so we cannot just `inferInstance` across
them. The robust move is to **delete ours and adopt the port's**, aliasing
our chart *names* to the port's so downstream proofs survive with minimal
churn.

---

## 1. What we reuse — and what we deliberately AVOID

**Reuse (light, 15-module ℙ¹ closure):**
- Port `RiemannSphere.{chartCoe, chartInfty, chartAtRS}` + its
  `ChartedSpace`/`IsManifold` instances (port `ProjectiveLine.lean`).
- Our own **direct Liouville** `HolomorphicOneForm_projectiveLine_eq_zero`
  (`Line/OneForm.lean`) — re-proved over the port atlas — for the
  `Subsingleton`/genus facts.

**AVOID (heavy, 375-module closure — would re-explode the build):**
- `genus_eq_kirovGenus` (`KirovDolbeaultLattice.lean:58`) and
  `bridgeKDFormEquiv` (`KirovDolbeaultTrace.lean:58`) — their closure is the
  full Serre/residue port. Do **not** import these into `Line*`/genus files.
- `KirovHolomorphicEquiv` and the port's own `genus_eq_zero`/`Subsingleton`
  (in port form-space `HolomorphicOneForms`) — using them forces a
  form-space-namespace reconciliation **and** pulls weight. Not needed: our
  light Liouville lemma already gives the same facts in *our* form space.

---

## 2. Blast radius

Only **three** files touch our charts / instance directly:

1. `Jacobians/ProjectiveCurve/Line.lean` — defines the instances (the source
   of the duplication).
2. `Jacobians/ProjectiveCurve/Line/OneForm.lean:243` —
   `instSubsingletonHolomorphicOneFormProjectiveLine`.
3. `Jacobians/RiemannSurface/MeromorphicToP1.lean` — `toP1` /
   `toP1_contMDiff` (~600 lines of chart-local analysis); the meaty redirect.

Plus the consumer that *uses* `genus ProjectiveLine = 0`:
- `Line/Genus.lean:29` `genus_projectiveLine_eq_zero`
- `Line/Witnesses.lean` (reuses the genus fact)
- `DegreeOneGenusZero.lean:471` (the failing calc — fixes itself once the
  instance is unified and `toP1_contMDiff` holds over the port's atlas).

All other 13 `ProjectiveLine` references are type-level only and need no
change.

---

## 3. Plan of record (canonical-instance, alias the chart names)

### Step 1 — make `Line.lean` import and re-export the port's ℙ¹ structure
- Add `import KirovDolbeault.ProjectiveLine` to `Line.lean`.
- Keep `abbrev ProjectiveLine := OnePoint ℂ` (unchanged — same type as
  `RiemannSphere`, so the port's `ChartedSpace ℂ RiemannSphere` /
  `IsManifold` instances now apply to `ProjectiveLine` automatically).
- **Delete** our `instance : ChartedSpace ℂ ProjectiveLine` (`:158`) and
  `instance : IsManifold 𝓘(ℂ) ω ProjectiveLine` (`:187`), plus the manual
  continuity/transition obligations they carried (port already proves them).
- Replace our chart defs with thin aliases so downstream names keep working:
  - `noncomputable def chart0 : OpenPartialHomeomorph ProjectiveLine ℂ := RiemannSphere.chartCoe`
  - `noncomputable def chart1 : OpenPartialHomeomorph ProjectiveLine ℂ := RiemannSphere.chartInfty`
  - re-export `chartAt`/the homeomorphism-to-`S²` from the port, or keep ours
    proven equal to the port's (`chartAt = chartAtRS`).
- Migrate our `chart0_*`/`chart1_*` simp lemmas to thin wrappers over the
  port's `chartCoe_*`/`chartInfty_*` simp lemmas (`chartCoe_apply_coe`,
  `chartInfty_apply_coe`, sources/targets) so any `simp` call downstream that
  named our lemmas still fires.

### Step 2/3 — KEEP THE LIGHT DIRECT ROUTE for genus/forms (do **not** use the bridge)

> **Corrected after vetting.** The obvious move — prove `genus ProjectiveLine
> = 0` via `genus_eq_kirovGenus` — is a **trap**: that bridge's import closure
> is **375 modules** (the full Serre/residue port), so routing genus=0 through
> it drags the heavy port into a foundational genus file and *throws away* the
> 15-module win. **Avoid `genus_eq_kirovGenus` / `bridgeKDFormEquiv` /
> `KirovHolomorphicEquiv` for the ℙ¹ facts entirely.**

The repo already has the **light** route and we keep it:
- `Line/OneForm.lean:243` proves `Subsingleton (HolomorphicOneForm
  ProjectiveLine)` directly from `HolomorphicOneForm_projectiveLine_eq_zero`
  — a **Liouville argument, axiom-free**, importing only `Line` +
  `RiemannSurface.OneForm` (no port, no bridge).
- `genus ProjectiveLine = 0` follows from that `Subsingleton` (a finite-rank
  module that is a subsingleton has `finrank = 0`), so `genus_projectiveLine_eq_zero`
  rests on the light lemma, **not** on the bridge.

So the only real work here is: **re-prove the single Liouville lemma
`HolomorphicOneForm_projectiveLine_eq_zero` over the port's atlas** (it reads
the form in the affine chart; migrate our `chart0` readout to port
`chartCoe`). Stays in the light 15-module world. `Subsingleton` and
`genus_projectiveLine_eq_zero` then go through unchanged.

This makes the earlier "form-space namespace" question (old-vendored-Kirov
`HolomorphicOneForms` vs dolbeault-port `HolomorphicOneForms`) **moot** — we
touch neither bridge.

### Step 4 — re-establish `toP1_contMDiff` over the port atlas
(`MeromorphicToP1.lean`)
- `toP1 : X → ProjectiveLine` is unchanged (target type identical).
- `toP1_contMDiff` and the chart-local lemmas (`toP1Rep_chartLocal_*`,
  `toP1Rep_contMDiffAt_of_chartLocal`) reason via `chartAt`/`chart0`/`chart1`
  on the **target**. Because Step 1 aliases `chart0 := chartCoe`,
  `chart1 := chartInfty`, the chart *readouts* are now the port's; the proofs
  should go through after swapping our chart simp-lemma names for the port's
  (Step 1's wrappers make most of this automatic).
- **Primary tactic:** rebuild via the Step-1 simp-lemma wrappers — mechanical.
- **Fallback (if a step is stubborn):** prove the local compat lemmas
  `chart0 = chartCoe`, `chart1 = chartInfty` (OpenPartialHomeomorph `ext`:
  same `toFun`/`invFun`/`source`/`target`) and `rw` them at the few
  chart-readout points, rather than redoing the analysis.

### Step 5 — `DegreeOneGenusZero.lean` falls out
With one instance, line 471's calc
`genus X = genus ProjectiveLine = 0` typechecks (no competing instance for
`genus_eq_of_biholo`/`genus_projectiveLine_eq_zero` to disagree on), and the
line-457 `toP1_contMDiff` flip is gone (single atlas). Drop the temporary
`Divisor` export-shim / qualified casts added during the failed relocate if
they're no longer needed.

### Step 6 — finish the headline rewiring (the former relocate, now diamond-free)
The `relocate-finish` work (point `Construction`/period-lattice instances at
the T-GEN route `PeriodLatticeTGen → … → K-LITE`) now composes: K-LITE drags
the port's ℙ¹ instance, and *that is the same instance* our `ProjectiveLine`
uses, so no diamond anywhere. Complete the rewire, then:
- delete the now-unused `AX_PeriodCycleBasis`;
- regenerate `docs/axiom-report.txt` (CI-diffed);
- update `AXIOM_AUDIT.md`: challenge-critical 1 → 0;
- update `README` status counts (coordinate with README owner).

---

## 4. Verification (per CLAUDE.md pre-push rule)

1. After Steps 1–3: `lake env lean Jacobians/ProjectiveCurve/Line.lean` and
   `…/Line/Genus.lean`, `…/Line/OneForm.lean`.
2. After Step 4: `lake build Jacobians.RiemannSurface.MeromorphicToP1` then
   `lake build Jacobians.RiemannSurface.DegreeOneGenusZero`.
3. After Step 6: **clean full build** (`lake build Jacobians`) — the diamond
   was masked by stale oleans before, so a clean build is mandatory.
4. `#print axioms` on all 24 headlines (via `scripts/axiom_report.lean`):
   must be exactly `[propext, Classical.choice, Quot.sound]`. Do **not**
   trust agent summaries — rebuild oleans + kernel-verify.
5. Re-run the axiom-consistency checker; confirm `axiom-report.txt` matches
   the kernel.

---

## 5. Risks / watch-list

- **Instance-priority illusion.** Do *not* fix any residual ambiguity with
  `attribute [local instance N]` priority bumps (explicitly rejected — they
  break later). The whole point is *one* instance; if two remain, a delete
  was missed.
- **`chart1` ≠ `chartInfty` defeq.** They're the same map, different build.
  If a downstream proof relied on our `chart1`'s definitional shape
  (`p.elim 0 (·⁻¹)`), use the Step-4 fallback compat lemma rather than
  forcing defeq.
- **`genus_eq_kirovGenus` instance args.** It needs
  `[Nonempty]`-free but `[T2][Compact][Connected][Charted][IsManifold]`.
  Confirm `OnePoint ℂ` synthesizes all five under the port instance before
  relying on Step 2.
- **Import weight creep.** `Line.lean` is foundational; adding the 15-module
  port ℙ¹ pulls those into every `ProjectiveLine` consumer. Acceptable, but
  re-check the clean-build wall-clock doesn't balloon (it shouldn't —
  15 light modules).
- **Independence framing.** This deepens the port dependency by design
  (MRD-approved). Note it in `docs/cross-repo-adoption.md` and the README
  provenance: ℙ¹'s manifold structure is now Kirov's, bridged to our genus.

---

## 6. Sequencing

Do this on a **fresh branch off `main`** (`feat/p1-unify`), *not* on the
abandoned `relocate-finish` (being cleaned up). Land ℙ¹ unification
(Steps 1–5) as one reviewable PR first — it stands alone as "remove the
duplicate ℙ¹ instance" and is independently verifiable. Then Step 6
(headline rewire + axiom deletion) as a second PR that links the
`AX_PeriodCycleBasis` tracker.
