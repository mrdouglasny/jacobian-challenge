# Headline rewiring plan — make Buzzard's 24 axiom-free over the discharged T-GEN

*2026-06-13. T-GEN (`Jacobians.RiemannSurface.analyticLoopsGenerateH1`) is now an
unconditional standard-3 theorem (PR #248, PL route). This plan wires the 24
challenge headlines onto it so they drop the last axiom `AX_PeriodCycleBasis`.*

## Root cause (why it's not a one-liner)

The two global instances that give `Jacobian X` its manifold structure —
`instPeriodLatticeDiscrete` / `AX_PeriodLattice` in `Jacobians/Axioms/PeriodLattice.lean`
— are consumed **upstream** (by `Jacobian/Construction.lean`). Their axiom-free
proof needs the T-GEN bridge `periodLatticeInBasis_{discreteTopology,isZLattice}_of_tgen`
(`RiemannSurface/Path2Prototype.lean`), whose import cone reaches
`RiemannSurface/LoopIntegralHom.lean`, which imports **back** to
`Axioms/PeriodLattice.lean`. So importing the bridge into `PeriodLattice.lean`
closes a cycle:

```
Axioms.PeriodLattice → Path2Prototype → Layer3.PeriodLatticeDiscrete
                     → LoopIntegralHom → Axioms.PeriodLattice
```

**Minimal cut found:** `LoopIntegralHom` references only the *def*
`periodLatticeInBasis` (lines 66, 84), which lives in the lower
`Axioms/PeriodLatticeBase.lean` — **not** the instances. So the back-edge is
removable with no loss.

## Steps (build-verify each)

**Step 1 — break the back-edge.** In `LoopIntegralHom.lean`, change
`import Jacobians.Axioms.PeriodLattice` → `import Jacobians.Axioms.PeriodLatticeBase`.
If it relied on `PeriodLattice`'s transitive imports, add those explicitly.
Build-verify (`lake build Jacobians.RiemannSurface.LoopIntegralHom`). Check no
other bridge-cone file re-introduces the edge (candidate: `Bridge/KirovDolbeaultLattice.lean`).

**Step 2 — swap the instances.** In `Axioms/PeriodLattice.lean`, add
`import …Path2Prototype` + `…ChartFlatHomotopyWallProof` and repoint:
- `instPeriodLatticeDiscrete` → `periodLatticeInBasis_discreteTopology_of_tgen x₀ b (analyticLoopsGenerateH1 x₀)`
- `AX_PeriodLattice` → `periodLatticeInBasis_isZLattice_of_tgen x₀ b (analyticLoopsGenerateH1 x₀)`

The manifold headlines drop `AX_PeriodCycleBasis` automatically via instance synthesis.

**Step 3 — flip `ofCurve_inj`.** Repoint `Jacobian.ofCurve_inj` (and `AX_AbelTheorem`'s
⊆ half via `abel_subset`) onto `ofCurve_inj_of_tgen` / `abel_subset_basis_free`
fed with `analyticLoopsGenerateH1` (the #247 consumer-side fix). Separate axiom
entry from the instances.

**Step 4 — verify.** `#print axioms` (sorryAx-aware) on all 24 headlines =
`[propext, Classical.choice, Quot.sound]`, no `AX_PeriodCycleBasis`.

**Step 5 — cleanup.** Delete the now-unused `AX_PeriodCycleBasis` axiom; regenerate
`docs/axiom-report.txt`; update `AXIOM_AUDIT.md` (challenge-critical 1 → 0).

## Risk / confidence

- High confidence on Steps 2–3 (proven pieces, just wiring; swap was already
  type-checked compatible).
- The uncertain step is Step 1's transitive-import fallout and any second
  back-edge (`KirovDolbeaultLattice`) — both bounded; build-iteration resolves them.
- No definitions move, no math changes.
