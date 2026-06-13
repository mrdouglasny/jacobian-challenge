# K-FULL: re-point the Jacobian at the K-LITE lattice (close the challenge axiom-free)

**Goal.** Eliminate `AX_PeriodCycleBasis` from the closure of every Buzzard
declaration by re-pointing the `Jacobian`'s lattice from the axiom-laden
`periodLatticeInBasis` onto K-LITE's axiom-free `loopPeriodLattice`. Win
condition: `#print axioms Jacobian.ofCurve_inj` (and all 24 Buzzard decls)
shows standard-3 ONLY. Then delete the axiom (ledger 10→9, critical 1→0).

Owner-approved: Discussion #235. Branch: `feat/kfull-jacobian` off post-#233 main.

---

## Phase 0 — the map (where the axiom enters)

`#print axioms` (docs/axiom-report.txt) shows **even `Jacobians.Jacobian`
(the type)** carries `AX_PeriodCycleBasis`. So the axiom enters at the
**lattice instances** needed merely to FORM the torus, not only in the
injectivity proof. Trace:

```
Jacobian X                                        Challenge.lean:81  (= Jacobians.Jacobian)
  = Jacobians.Jacobian X                          Construction.lean:146  (ULift of …)
  = ULift (JacobianAmbient X)                      Construction.lean:132
JacobianAmbient X
  = ComplexTorus (Fin (genus X) → ℂ)
       (periodLatticeInBasis X (arbitrary X) (jacobianBasis X))   Construction.lean:132
```

`ComplexTorus V L` (ComplexTorus.lean:10) requires `[DiscreteTopology L]`
and `[IsZLattice ℝ L]`. For `L = periodLatticeInBasis …` those come from:

- `AX_PeriodLattice` (PeriodLattice.lean:57, `attribute [instance]`)
- `instPeriodLatticeDiscrete` (PeriodLattice.lean:43, `attribute [instance]`)

both proved in `Layer3/Periods.lean` from the chosen
`Classical.choice (AX_PeriodCycleBasis x₀)` witness's R1/R2 fields. **This is
the axiom entry point for the TYPE.**

The Abel-Jacobi map then quotients by the SAME lattice:

```
ofCurveImpl X P₀ : X → Jacobian X                 AbelJacobiMap.lean:548
  = fun P => ULift.up (QuotientAddGroup.mk' _ (ofCurveAmbient … - ofCurveAmbient …))
```

The quotient group `_` is `(JacobianAmbient X)`'s lattice (defeq
`periodLatticeInBasis`).

`ofCurve_inj` (Challenge.lean:140 → `AX_ofCurve_inj`,
OfCurveInjective.lean:15) uses:
- `ofCurveImpl_basepoint_independent` (AbelJacobiMap.lean:555), whose proof
  uses `Λ := periodLatticeInBasis …` and `AX_Period_Triangle` membership
  in `Λ`;
- `AX_AbelTheorem`, `principal_imp_eq_of_genus_pos` — **these do NOT carry
  `AX_PeriodCycleBasis`** (they live in the Divisor/Abel layer; to be
  kernel-confirmed). The injectivity's axiom dependence comes through
  `ofCurveImpl` / `_basepoint_independent` / `AX_Period_Triangle` only.

`AX_Period_Triangle` (AbelJacobiMap.lean:176) proves membership in
`periodLatticeInBasis` via
`loop_canonicalArcIntegral_mem_periodLatticeInBasis`
(LoopIntegralHom.lean:157), which routes through `loopIntegralToH1`
(= `Classical.choice (AX_PeriodCycleBasis x₀)`). **Axiom entry point for the
TRIANGLE / injectivity.**

### The K-LITE replacement (all axiom-free, #233)

`loopPeriodLattice x₀ b := span ℤ (range (loopPeriodVec x₀ b))`
(PeriodDiscreteness.lean:142), where
`loopPeriodVec x₀ b γ i = canonicalArcIntegral γ.arc (b i)` (line 126, `rfl`).

K-LITE proves UNCONDITIONALLY (PeriodDiscretenessKirovRoute.lean):
- `instDiscreteTopology_loopPeriodLattice` (1316, **global instance**)
- `isZLattice_loopPeriodLattice_unconditional` (1323, theorem — NOT yet an instance)
- `finrank = 2g`, `exists basis` (1329/1335)

**Key simplification.** For `loopPeriodLattice`, the loop-membership that
`AX_Period_Triangle` needs is `Submodule.subset_span ⟨closedLoop, rfl⟩`
(since `loopPeriodVec closedLoop ∈ span` by definition) — **completely
axiom-free**, replacing the `loopIntegralToH1` route.

---

## The re-plumb (minimal change set)

1. **New wrapper file** `Jacobians/Jacobian/LoopLatticeInstances.lean`
   (axiom-free): register `IsZLattice ℝ (loopPeriodLattice x₀ b)` as an
   `instance` (the discreteness instance already global). Re-export so
   `Construction.lean` imports ONLY this, not the heavy KirovRoute graph —
   actually `Construction` must transitively get KirovRoute's instances;
   measure import cost, fall back to importing KirovRoute directly if the
   thin file would still drag the same deps.

2. **`Construction.lean:132`** — swap `JacobianAmbient`'s lattice
   `periodLatticeInBasis X (arbitrary X) (jacobianBasis X)` →
   `loopPeriodLattice (arbitrary X) (jacobianBasis X)`. Drop the
   `import Axioms.PeriodLattice`, add the loop-lattice import. `ComplexTorus`
   now resolves its instances from K-LITE (axiom-free).

3. **`AbelJacobiMap.lean`** — re-point so the quotient matches:
   - `ofCurveImpl` quotient `_` becomes `loopPeriodLattice …` (it's the
     `JacobianAmbient` lattice, so this follows automatically from step 2 if
     the `_` is inferred; verify).
   - `ofCurveImpl_basepoint_independent`: `Λ := loopPeriodLattice …`;
     `AX_Period_Triangle` membership now in `loopPeriodLattice`.
   - `AX_Period_Triangle` (line 176): change the conclusion's lattice to
     `loopPeriodLattice (arbitrary X) (jacobianBasis X)` and replace
     `loop_canonicalArcIntegral_mem_periodLatticeInBasis` with
     `loopPeriodVec_mem_loopPeriodLattice` (`subset_span`). Statement shape
     for callers unchanged except the lattice name (internal; not Buzzard-facing).

4. **`AX_AbelTheorem` / `abelJacobiDiv` / `principal_imp_eq_of_genus_pos`** —
   kernel-check they are `AX_PeriodCycleBasis`-free; if any routes through
   the old lattice, re-point.

### Classification of the ~26 `loopIntegralToH1`/`periodLatticeInBasis` files

- **RE-POINT (on the Buzzard path):** Construction.lean, AbelJacobiMap.lean
  (ofCurveImpl, basepoint_independent, AX_Period_Triangle), OfCurveInjective.lean
  (inherits), PeriodLatticeBase.lean (def kept but off-path).
- **H1-route, become UNUSED on Buzzard path (stay, no longer in closure):**
  LoopIntegralHom.lean, LoopIntegral.lean, Layer3/Periods.lean,
  Layer3/PeriodLatticeDiscrete.lean, Axioms/PeriodLattice.lean,
  PeriodDiscretenessFromR2.lean, H1Composite.lean, etc.
- **AXIOM-FREE period machinery to REUSE:** PeriodDiscreteness.lean
  (loopPeriodLattice, loopPeriodVec, span_real_…),
  PeriodDiscretenessKirovRoute.lean (K-LITE instances),
  `span_loopPeriodFunctional_eq_top` (B-3, #182).
- **DO NOT USE:** `loopPeriodLattice_eq_periodLatticeInBasis`
  (PeriodLatticeDiscrete.lean:130) — axiom-laden bridge.

---

## Phase 1 — execution order (foundation-first, kernel-check each step)

- **S1.** wrapper instance file + `Construction.lean` lattice swap.
  Validate: `lake env lean Construction.lean`; `#print axioms Jacobians.Jacobian`
  → expect standard-3.
- **S2.** `AbelJacobiMap.lean` AX_Period_Triangle + ofCurveImpl +
  basepoint_independent re-point. `lake env lean AbelJacobiMap.lean`.
- **S3.** Closure-repair outward: OfCurveInjective, any `ofCurveAmbient`/
  divisor consumers. `lake build` the Jacobian module.
- **S4.** `#print axioms Jacobian.ofCurve_inj` and all 24 Buzzard decls →
  standard-3. If clean: delete `AX_PeriodCycleBasis`, regen axiom report,
  update ledger 10→9 / critical 1→0, run consistency guard.

### Risks / landmines
- **Quotient-type defeq.** `Jacobian X`'s `AddCommGroup`/`ChartedSpace`
  instances are `inferInstanceAs (… (ULift (JacobianAmbient X)))` — swapping
  the lattice changes `JacobianAmbient`, but all instances are derived from it,
  so they should follow. Watch for any place that names `periodLatticeInBasis`
  explicitly in an instance.
- **`ofCurveAmbient` lands in `Fin (genus X) → ℂ`** (the torus's `V`), not the
  lattice — unaffected by the swap. Good.
- **Does any OTHER axiom hide behind the swap?** If after S1–S3 a Buzzard
  decl still shows a non-standard axiom, NAME it (it'd be a genuinely
  H1-basis-needing fact K-FULL can't bypass) and report.

### What K-FULL genuinely cannot bypass (to watch for)
Anything that needs an actual ℤ-BASIS of `H₁(X,ℤ)` (not just the lattice in
`ℂ^g`) — e.g. if `AX_AbelTheorem` or the contMDiff proofs reach into the
chosen cycle basis. The image-route design (#206/#208) suggests they don't,
but this is the precise thing to confirm at S4.
