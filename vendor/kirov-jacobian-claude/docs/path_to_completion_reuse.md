# Path to completion — the maximal-reuse audit

Living research doc (2026-06-04). Question: *given everything already proven in this repo, what is the
minimal net-new work to close each remaining wall, maximally reusing what exists?* Companion to
`deg_div_research.md`, `cech_finiteness_research.md`, `hodge_bridge_research.md`.

Discipline: grounded (`file:line` + exact names), skeptical (no "reusable" claim without reading the
statement). Sections marked **[agent pending]** are being deep-audited by parallel read-only agents and
will be merged.

---

## 0. The thesis (why the walls are not 5 fresh theorems)

The repo is ~48.7k LoC / 137 files. The five remaining walls do **not** each require a major theorem from
scratch — they are *assemblies + a few focused atoms* on a large, **mostly-proven shared substrate**. The
single most important structural fact, found this audit:

> **`Jacobians/Discharge/Manifold/` is 11.6k LoC across 53 files and is essentially SORRY-FREE** (only two
> `:= sorry` hits, both in comments). It is a complete holomorphic degree/fibre/multiplicity apparatus.

That one directory de-risks W2 (deg_div) and feeds W1b (#1b degree). The other walls sit on similarly-built
substrates (residue calculus, flat-Stokes, the Montel FA spine, the period lattice, the Dolbeault
comparison). The work that remains is concentrated in a handful of *bridges* and *assemblies*, not broad
new theory.

---

## 1. The cross-cutting reusable substrate (what is proven and shared)

| Substrate | Location (key names) | Status | Walls it feeds |
|---|---|---|---|
| **Holomorphic degree / fibre / multiplicity** | `Discharge/Manifold/` (53 files, 11.6k LoC): `degreeFiber_eq_card_of_regularWitness`, `criticalValues_finite_general`, `localMultiplicityOne_preimage_card{,_with_radius,_on_closedBall}`, `localMultiplicity_one_locally_injective`, Hurwitz patching, `FibreCardLocallyConstant…`, `RegularValueExistsReg…` | **sorry-free** | **W2** deg_div, **W1b** #1b |
| **Disk argument principle / k-th root** | `Discharge/Manifold/ArgumentPrincipleDiskProof.lean` (`argumentPrinciple_disk_statement_holds`), `AnalyticKthRoot.lean:126` (`analytic_kth_root_branch_exists_statement`) | **both DONE, axiom-clean** | **W2** |
| **Residue calculus** | `Dolbeault/{Residue,FormCoeff,MittagLeffler,SerreDuality}.lean`: `resAt`, `residueSum`, `Res(holo)=0`, §17.9 litmus `subspaces_inf_ne_bot_of_finrank_add_gt`, `serre_surjectivity_dim_core`, §17.6 witness | sorry-free | **W2** (global Res), **W1** (Serre pairing) |
| **Flat Stokes / box-divergence / circleIntegral** | Mathlib `integral_divergence_*`, `integral_boundary_rect_*`, `circleIntegral.*`; repo `CutSurface.lean`, `rectBoundaryIntegral_handleSum` | proven (Mathlib + repo) | **W3** #7, **W2** arg-principle, **W1** Serre residue |
| **Finiteness FA spine (Montel/Schwartz)** | `Montel/Compactness.lean` (1.1k), `Montel/Complete.lean` (0.9k), `Dolbeault/CechFinitenessWiring.lean`, the `BddHol` Banach + compact-operator atoms | spine proven; manifold instantiation in progress (FunctionDiskAcyclic) | **W1** finiteness |
| **Dolbeault comparison + ∂̄ operators** | `Dolbeault/DolbeaultComparison{,Proof,Inverse,Equiv}.lean` (`cechH1 ≅ H^{0,1}`), `RealForms.lean` (`differential`, `dbar` both sorry-free) | comparison ~closed; `RealForms` sorry-free | **W1** Serre, **W1b** de Rham |
| **RR interface** | `RiemannRoch.lean`: `lDim`, `linearSystem`, faithfulness, `lDim_eq_zero_of_deg_neg`, genus-0 endgame; `DegDivResidue.lean` (deg_div PROVEN from `exists_properMapDegree`) | proven mod the 2 named inputs | **W1**, headline |
| **Period lattice / Jacobian torus** | `PeriodLattice.lean` (1.6k), `ZLatticeQuotient.lean` (0.8k) | substantial | **W3** #7, **W4** #3 Abel |
| **Trace / pushforward** | `TracePullback.lean` (2.6k), `TraceForm.lean` (2.5k) | proven (S8 trace fix) | S8 `pushforward_pullback` |

Reading: a large fraction of the 48.7k LoC is *reusable proven substrate*. The walls draw on overlapping
columns of this table — e.g. flat-Stokes serves three walls; the residue calculus serves W2 and W1.

---

## 2. W2 — `deg_div` / `exists_properMapDegree` (the closest, after finiteness)

**Status: the two irreducible atoms are DONE; what remains is one bridge + one assembly, both reuse-heavy.**

`deg_div` is PROVEN from the single node `exists_properMapDegree` (`DegDivResidue.lean:214`). That node sits
on the sorry-free 11.6k-LoC degree apparatus. The chain, with current status:

1. `argumentPrinciple_disk_statement` (`LocalNormalForm:543`) — **DONE** (`ArgumentPrincipleDiskProof:168`, axiom-clean, this run).
2. `analytic_kth_root_branch_exists_statement` (`LocalKFoldMultiplicity:123`) — **DONE** (`AnalyticKthRoot:126`, in the sorry-free dir).
3. `argumentPrinciple_implies_rouche_statement` (`LocalNormalForm:574`) — **OPEN.** The next atom: argument
   principle + k-th-root + open-mapping ⟹ the Rouché preimage count. The simple-zero (`g − w`) passage the
   `deg_div` recon §5.3 described. Both its inputs are now proven, so this is a focused bridge.
4. `localMultiplicity_eq_localOrder_statement` (`LocalNormalForm:386`) — **OPEN**, follows from (3): local
   degree = order.
5. `exists_properMapDegree` (`DegDivResidue:214`) — the final fibre-count assembly: `zerosCount = polesCount
   = d`, reusing `degreeFiber_eq_card_of_regularWitness` + `criticalValues_finite_general` + (4) for the
   ramified fibres over `0`/`∞`.

**Reuse verdict:** very high. The two hardest pieces (argument principle, k-th-root branch) are proven; the
remainder is the open-mapping Rouché bridge (3)→(4) plus a fibre-count assembly (5) over an essentially-
complete degree library. This is the **single best effort-to-impact wall to finish next** after the
finiteness atom — a few hundred LoC of bridge+assembly, almost entirely wiring proven results. (Caveat from
`deg_div_research.md §6.3`: W2 is needed for *general* RR, not the bare genus
headline — but per the "build everything" scope it is in-scope regardless.)

---

## 3. W1 — Serre / RR (the make-or-break)

**Top-line: NO hidden Hodge/elliptic wall** (the Weyl/elliptic-regularity fear is retracted and well-
supported — the entire §17 *local* calculus compiles with only `circleIntegral` + Cauchy–Goursat, no PDE,
no `*`-operator, no manifold 2-form integration). But W1 is **not** pure reuse: it splits into assembly
(reuse) + **two genuinely-new but PDE-free, bounded classical theorems**.

`riemannRoch_equality_of_ladder` (`DolbeaultLadder.lean:74`, **PROVEN**) composes RR from four leaves + deg_div:
```
l(D) − l(K−D) = deg D + 1 − g
  via  cohomological_riemannRoch (χ)  +  h0Dim_eq_lDim  +  serre_h1_eq  +  arithmeticGenus_eq_genus
```

| Leaf | Verdict | State |
|---|---|---|
| `h0Dim_eq_lDim` (h⁰ = l bridge) | **DONE** | ✅ sorry-free now (`CechH0`; the doc-listed `:513` sorry is discharged — **stale doc**) |
| Dolbeault comparison `cechH1 ≅ H^{0,1}` | **DONE** | ✅ sorry-free now (`DolbeaultComparisonEquiv.comparison_linearEquiv:648`; the `DolbeaultComparison:227` sorry is a **stale wiring stub**) |
| `cohomological_riemannRoch` ⟸ `exists_skyscraperLES` (`CohomologicalRR:334`) | **ASSEMBLY** | snake + `e0` (`H⁰(Q)≅ℂ`) + `subsingleton_H1Q` all axiom-clean; needs a **1-line wire** `⟨skyscraperLES_of_localRealization (localRealizationData_of_chartDisk …)⟩` + cover hyps (`hstar`/`hWsrc`/`hDsupp`) + an H⁰-finiteness instance |
| `finiteDimensional_cechH1` ⟸ `exists_cechModel` (`CechFinitenessWiring:287`) | **ASSEMBLY** | FA spine (Montel compact-op + Schwartz + `leray_surjective`) all proven; only the chart-disk Leray **model construction** remains — *the FunctionDiskAcyclic agent is building exactly this now* |
| `arithmeticGenus_eq_genus` / `serre_h1_eq` — EASY half (`genus ≤ h1Dim 0`) | **MOSTLY-NEW** | §17.6 residue-1 witness (`exists_formFnResidue_eq_one…`) ✅; needs the global `Res`-on-classes + the `ι₀` pairing map (the `ω·ξ` product) — unbuilt |
| `arithmeticGenus_eq_genus` / `serre_h1_eq` — HARD half (§17.9 surjectivity) | **GENUINE NEW — THE make-or-break** | the abstract pigeonhole `serre_surjectivity_dim_core` is axiom-clean but **has ZERO instantiators**; instantiating surfaces an unbuilt global meromorphic-1-form space `H⁰(Ω_{nP})` + **`ω₀`-existence** (a nonconstant meromorphic 1-form, recursively gated on RR/finiteness). Forster §17.9. "Never attempted." |
| `exists_riemannRoch_divisor` wire (`RiemannRoch:287`) | trivial + obligation | NOT yet wired to the ladder; ~1-line `exact riemannRoch_equality_of_ladder` **modulo a proven Leray cover** `𝔘.IsLeray` on a compact RS (Leray-cover *existence* is itself an unproven repo lemma) |

**Reusable §17 assets (a real ~40% head-start, all axiom-clean):** `Residue.lean` (`resAt` + ℂ-linearity +
`Res(holo)=0` + radius-independence), `FormCoeff.lean` (`coeffAt`, the §17.6 residue-1 witness),
`MittagLeffler.lean` (`res`/`res_holomorphic`/`res_smul` — the global residue as a ℂ-linear functional of the
distribution), `SerreDuality.lean` (BOTH finite-dim cores: `finrank_le_of_injective_to_dual` EASY-half +
`serre_surjectivity_dim_core` §17.9 pigeonhole).

**Net-new for W1 (PDE-free, bounded, ~1–2k LoC — `hodge_bridge_research.md:388`):** the global `Res : cechH1 Ω
→ ℂ` well-defined on classes (gated on the **1-form residue theorem** `∑Res(α)=0` via the **trace-to-ℙ¹** route — Miranda *Algebraic Curves and Riemann Surfaces* §VIII.3, reusing `TraceForm`/`pushforwardForm` + the RR-branched cover; **NOT `deg_div`** — see ⚠ correction at end of §3), the `ω·ξ` pairing + `ι₀`, the global
meromorphic-1-form space `H⁰(Ω_{nP})`, and **`ω₀`-existence** — the latter is the singular risk.

**Verdict:** the comparison being done does NOT move the Serre leaf (it gives only the *first* iso, the
tautology `2·h1Dim = 2·h1Dim`; Serre is the independent *second* iso `H^{0,1}≅Ω`). W1 = 3 assembly leaves
(one done, two ~1-line-wire-modulo-hyps) + 2 genuine-new PDE-free theorems (the §17 pairing with `ω₀`, and
the **1-form residue theorem** for the global `Res` — via trace-to-ℙ¹, **not** `deg_div`; see ⚠ below). The
make-or-break is the §17.9 surjectivity's `ω₀`-existence — bounded and classical, but untested (nobody has
instantiated the pigeonhole).

> ⚠ **CORRECTION (2026-06-04, verified vs Forster §17 + Miranda §VIII.3).** The global `Res : cechH1 Ω → ℂ`
> is **NOT gated on `deg_div`** — that was a conflation in `MittagLeffler.lean`'s plan and the earlier audit.
> `deg_div` (`∑ ord f = 0`, the `df/f` case) ≠ the **general 1-form residue theorem** `∑Res(α)=0` that the
> Serre `Res` descent needs (residues of `α=ω₀·f` are Laurent coefficients, not orders). Forster proves the
> latter via `(2πi)⁻¹∬_X` (manifold Stokes, which this repo avoids); the **PDE-free fix is Miranda §VIII.3's
> algebraic residue theorem via the trace to ℙ¹**: `∑Res_X(ω)=∑Res_{ℙ¹}(Tr ω)=0`, reusing the built
> `TraceForm`/`pushforwardForm` + the RR-branched cover + one "residue-of-a-trace" lemma (Miranda Lemma 3.2)
> + the elementary ℙ¹ residue theorem. So Serre `Res` ← **trace-residue theorem** (a separate, bounded,
> reuse-heavy node), and `deg_div` keeps only its own consumers (`lDim_eq_zero_of_deg_neg`, general degree).

---

## 4. W3 #7 cut-surface · W4 #3 Abel · W1b #1b backward (the independent walls)

### W3 — `exists_cutSurface` (`CutSurfaceRelations.lean:161`) — **MOST reuse-collapsible**
- Consumption (all sorry-free): `exists_cutSurface` → `toCanonicalDissection` → `exists_canonicalDissection`
  → `exists_periodLattice_realBasis` (`PeriodLattice.lean:856`) → the lattice full-rank API. Discharging
  it closes #7 outright. Tighter scaffold: `exists_cutSurface_of_topology` (`CutSurfaceRecon.lean:114`)
  reduces it to `Nonempty (CutSurfaceTopology X)`.
- **Reuse (the whole analytic half is built, axiom-clean):** both Riemann bilinear relations
  `cutSurface_R1`/`_R2` (`CutSurfaceRelations.lean:126,135`) PROVEN from the boundary-word fields;
  `periodVec_linearIndependent` (`Dissection.lean:108`, posDef ⟹ 2g vecs ℝ-indep); the Green/box engine
  (`rectBoundaryIntegral*`, `boundaryForm`, `GreenPositivity`) on Mathlib `DivergenceTheorem` +
  `integral_boundary_rect_eq_zero` + `Convex.exists_forall_hasDerivWithinAt`; the handle aggregation
  `rectBoundaryIntegral_handleSum` (`CutSurfaceRecon.lean:170`).
- **Net-new (either route):** construct the 14 `CutSurfaceTopology` fields — the symplectic loop basis
  (`H₁≅ℤ^{2g}`), the holomorphic cut-chart to a `4g`-gon, and the gluing/monodromy "boundary word". The
  analytic half (bilinear relations + matrix core + Green) is reused *regardless of route*.

**Two routes to those topology fields (+ a third, rejected):**
- **Route A — Radó cut-surface (RR-independent):** build the symplectic basis + `4g`-gon from scratch via
  Radó triangulability + classification of surfaces. Startable in parallel NOW. ~2–4k LoC, but Mathlib has
  *zero* surface-topology API — the repo's own notes call Radó "the highest-variance, no-Lean-prior-art
  tar-pit" (a hard, general Jordan–Schoenflies-flavored theorem). **High, independent risk.**
- **Route B — branched-cover via RR (RR-gated):** a nonconstant meromorphic function (the `ω₀`/RR keystone)
  makes `X` a branched cover of `S²`; lift `S²`'s explicit triangulation. The *classical, constructive* way
  to triangulate a Riemann surface (general Radó is never invoked). **Reuses RR + the 11.6k-LoC sorry-free
  `Discharge/Manifold` degree machinery (Riemann–Hurwitz / Euler-char → genus) + `S²`'s triangulation.**
  Shorter and lower-variance on the topology; risk is *inherited* from `ω₀`/RR (already the critical-path
  bet — adds no new project risk).
- **Route C — Hodge-reuse (`STATUS.md:148`, `docs/archive/dolbeault_hodge_feasibility.md §3`): REJECTED.**
  Get the period lattice from the Hodge/period-matrix instead of cutting. Tagged the "highest-variance
  tar-pit" earlier, and this session's finding *reinforces* the rejection: W1's Serre route is PDE-free, so
  it does NOT build the harmonic/Hodge `∗`-machinery this route would need — no piggyback, strictly costlier.

> **DECISION (2026-06-04): Route B (branched-cover), build DEFERRED behind RR.** Shorter + lower-variance +
> maximal reuse; the RR-gating is free because RR is the critical-path bottleneck anyway. Do NOT speculatively
> build Radó (Route A) — spend the parallel slots on the genuinely-independent, lower-variance fronts (W2
> Rouché bridge, `SimplyConnectedSpace S²`) instead. **Trigger:** scope Route B's branched-cover lift when
> finiteness + `ω₀` land (RR in sight); fall back to Route A only if RR is abandoned (challenge-blocked
> scenario anyway). **Watch:** extracting the symplectic `H₁≅ℤ^{2g}` basis from the CW pullback — if that
> turns into its own tar-pit, reassess, with RR in hand either way.

- **Verdict: ~70% of the classical proof already proven; residue is pure topology, built via Route B
  (branched-cover) once RR lands.**

### W4 — `abelJacobi_twoPoint_ne_zero` (`Abel.lean:671`) — **reduction reused, core greenfield**
- Consumed only by `ofCurve_inj` (the #3 theorem), proven modulo this leaf. `AbelRecon.lean` proves the
  whole route EXCEPT Abel's theorem, axiom-clean: `abelJacobi_twoPoint_ne_zero_of_abel` (`:153`) derives the
  target from `AbelStatement X` (`:134`) + the genus-0 fact. So **W4 is pinned to exactly `AbelStatement X`**
  (Abel *sufficiency*: `abelJacobi(P−Q)=0 → ∃ f, HasSingleSimplePole Q`).
- **Reuse:** the full reduction (`AbelRecon`) + `abelJacobi_twoPointDivisor` (`Abel.lean:595`). The trace
  layer powers Abel *necessity* — the half NOT needed here.
- **Net-new = `AbelStatement`**, the HARD half that constructs `f`. No RR-free *and* Hodge-free elementary
  proof exists. Route A (Forster §20): weak divisor solution + **`∂̄`-solvability `H¹(X,𝒪)`** (the Dolbeault
  tower). Route B (G–H): third-kind differential `ω_{PQ}` + reciprocity — gated on **RR** + ∑Res=0;
  reciprocity reuses the `CutSurface`/`boundaryForm` toolkit (shared with W3).
- **Verdict: ~3–6k+ LoC, the deepest of the three; reduction done, core absent.** W3 ⊥ W4 (logically
  independent — the lattice says nothing about whether the open-path period is a lattice point; that
  non-membership IS Abel). **Leverage:** Route B's RR input is exactly what the Dolbeault agents target — RR
  unlocks W4 + the genus-comparison + forward #1 simultaneously.

### W1b — `genus_zero_of_nonempty_homeo_sphere` (`DegreeOneSphere.lean:675`) — **a trap + the de Rham wall**
- The `mpr` of `genus_eq_zero_iff_homeo`. Reuse already built: `RiemannSphere.genus_eq_zero` (`ProjectiveLine.lean:614`,
  via Liouville — the entire `Ω(ℂℙ¹)=0` content, DONE & in scope), `homeoSphere`, and Step-1/Step-5 transport
  in `GenusSphereBackward.lean` (`exists_ne_zero_holomorphicOneForm_of_genus_pos`, `simplyConnectedSpace_of_homeo_sphere`).
- **KEY FINDING — the genus-transport shortcut is BLOCKED.** One wants `X ≃ₜ S² ≃ₜ ℂℙ¹ ⟹ genus X = 0` for
  free; it FAILS because `genus := finrank ℂ HolomorphicOneForms` is **complex-analytic** (transports across a
  *biholomorphism*, not a homeomorphism), and the endgame only ever produces a *topological* `X ≃ₜ S²`. So
  `RiemannSphere.genus_eq_zero` is unreachable for this hypothesis. The honest route is the contrapositive
  `genus ≥ 1 ⟹ X ≄ₜ S²` via de Rham, with two greenfield nodes: **(1) `SimplyConnectedSpace S²`** (absent —
  only a Mathlib `proof_wanted`; we build it) and **(2) closed-not-exact ⟹ ∃ loop `∮_γ ω ≠ 0`** (manifold
  loop-integration + homotopy-invariance — no Mathlib scaffolding; the repo even deleted the local version).
- **Verdict: ~1.5–3k LoC across two absent nodes.** `SimplyConnectedSpace S²` is a clean, self-contained,
  **Dolbeault-independent** sub-target (cheapest *isolated* win; also a `proof_wanted` Mathlib would accept) —
  but alone it does NOT close W1b without the de Rham period slice (the same Hodge/∂̄-flavored gap as W4-A).

---

## 5. Reuse-leverage ranking (W1 Serre verdict still **[agent pending §3]**)

Ordered by effort-to-impact / reuse-collapsibility:

1. **W1 finiteness atom** (`FunctionDiskAcyclic`) — building now; pure reuse of `primFn`/`cechTerm` post-clash-fix.
2. **W2 Rouché bridge + fibre assembly** — both hard atoms (arg-principle, k-th-root) DONE; residue is the
   open-mapping bridge `argumentPrinciple_implies_rouche_statement` + `exists_properMapDegree` assembly over
   the 11.6k sorry-free degree dir. Highest effort-to-impact of the *open* items. ~few hundred LoC.
3. **W3 #7 cut-surface** — most reuse-collapsible *classical* wall: ~70% proven (bilinear relations + matrix
   core + box-Green + handle-sum); residue = the topology fields, **built via Route B (branched-cover via RR),
   deferred behind RR** — NOT the Radó tar-pit. Reuses the degree machinery + `S²` triangulation.
4. **`SimplyConnectedSpace S²`** (a W1b sub-node) — clean, self-contained, **Dolbeault-independent**; the
   cheapest *isolated* topology win (also a Mathlib `proof_wanted`). Does NOT alone close W1b.
5. **W1 Serre §17 pairing + `ω₀`-existence** — the make-or-break. §3 verdict: **PDE-free (no Hodge wall)**,
   but GENUINE-NEW and untested (the §17.9 pigeonhole `serre_surjectivity_dim_core` has zero instantiators;
   instantiation surfaces `H⁰(Ω_{nP})` + `ω₀`-existence). ~1–2k LoC.
6. **W1b de Rham period slice** — manifold loop-integration + homotopy-invariance; no Mathlib scaffolding.
7. **W4 #3 Abel** (`AbelStatement`) — deepest: reduction reused (axiom-clean), but the core is a multi-k-LoC
   greenfield `∂̄`/RR theorem.

Plus the **cheap assembly wires** (not "walls" but real obligations): `exists_skyscraperLES` 1-line wire +
cover hyps + H⁰-finiteness; `exists_riemannRoch_divisor` 1-line wire + Leray-cover existence;
`exists_cechModel` (building now). These convert several 🔴 sorries to 🟢 once the geometry hyps are supplied.

### Cross-wall structural insights (the highest-value findings)
- **RR is the single highest-leverage missing theorem.** Building it (the Dolbeault tower the agents target)
  discharges W1, **and** W4 Route B (`AbelStatement` via `ω_{PQ}` + reciprocity), **and** the genus-comparison
  /forward-#1 — three walls at once. It does NOT give W3 (deliberately PDE-free Green-on-polygon) or
  `SimplyConnectedSpace S²` (pure homotopy).
- **The genus-invariance trap (W1b):** `genus` is complex-analytic; the only available equivalence is
  topological — so the "transport from `ℂℙ¹`" shortcut is false-as-applied. Forces the de Rham wall.
- **Three sub-targets are Dolbeault-INDEPENDENT** and can proceed in parallel with the Serre tower: W2's
  Rouché bridge+assembly, W3's surface topology, and `SimplyConnectedSpace S²`. These are the "keep the
  other fronts moving" candidates.
- **The "one shared Hodge build" hope is FALSE (resolved by §3).** W1's Serre route is **PDE-free** (Čech-
  residue, no manifold-∂̄), so it does NOT collapse W1b's de Rham period slice (manifold loop-integration) or
  supply W4-Route-A's `∂̄`-solvability. The three are **distinct builds**, linked only through **RR as the
  keystone** (which unlocks W4-Route-B + the genus-comparison + forward-#1). No grand shared-analysis
  collapse — but also no Hodge abyss.

---

## 6. Bottom line — the synthesized path

**The biggest schedule risk is RULED OUT.** The PDE-free Serre route has no hidden Hodge/elliptic wall — the
single scariest scenario for this project is off the table (well-supported: the §17 local calculus compiles
with only `circleIntegral`+Cauchy–Goursat). Every remaining piece is classical, PDE-free, and bounded.

**The repo is materially further along than the memory/docs indicated.** Stale-doc corrections found this
audit: `h0Dim_eq_lDim` is sorry-free; the Dolbeault comparison `cechH1 ≅ H^{0,1}` is sorry-free; the entire
skyscraper-LES (χ-additivity) content is proven *bar a 1-line wire*; the finiteness FA spine is complete. So
the RR ladder is **PROVEN modulo its leaves**, and 3 of those leaves are assembly (one already done).

**What is genuinely-new remaining (all PDE-free, all bounded):**
1. **The §17 Serre pairing + `ω₀`-existence** — the make-or-break keystone (`ι₀` pairing, global `Res`-on-
   classes, `H⁰(Ω_{nP})`, and the nonconstant meromorphic-1-form `ω₀`). Untested (zero instantiators). ~1–2k.
2. **W2 deg_div** — both hard atoms done; residue = Rouché bridge + fibre-assembly. Closest. ~few-hundred.
3. **W3 #7 surface topology** — via **Route B (branched-cover via RR)**, deferred behind RR; reuses the
   degree machinery + `S²` triangulation, avoiding the Radó tar-pit (analysis already done).
4. **W1b** — `SimplyConnectedSpace S²` + de Rham period slice. ~1.5–3k.
5. **W4 `AbelStatement`** — or, cheaper, *fall out of RR* (Route B). ~3–6k standalone.

**RR is the keystone.** Closing the §17 pairing (1) ⟹ RR ⟹ also W4-Route-B + the genus-comparison +
forward-#1. So effort on the §17 pairing has 3–4× leverage.

**The maximal-reuse plan that falls out of this audit:**
- **(A) Harvest the assembly wires now** (cheap, high-certainty): supply the chart-disk-cover geometry hyps
  to fire the `exists_skyscraperLES` 1-line wire; finish `exists_cechModel` (building); prove Leray-cover
  existence + wire `exists_riemannRoch_divisor` to the ladder. This collapses the RR ladder to exactly two
  inputs: **{the §17 Serre pairing, deg_div}**.
- **(B) Three Dolbeault-INDEPENDENT fronts can run in parallel** with the Serre work: **W2's Rouché bridge +
  fibre-assembly** (closest), **W3's surface topology**, and **`SimplyConnectedSpace S²`**. None waits on RR.
- **(C) The keystone:** attack the §17.9 surjectivity (`ω₀`-existence) — the one untested, highest-leverage,
  make-or-break node. Its success cascades to W4 and forward-#1.

**Honest residual uncertainty:** exactly one node is both load-bearing and never-attempted — the §17.9
surjectivity's `ω₀`-existence (a nonconstant meromorphic 1-form, recursively gated on RR/finiteness). Whether
it closes cleanly by the built §17 atoms + finiteness, or needs a further construction, is the one genuine
unknown left in the path. Everything else is assembly, a bounded classical theorem, or both.
