# `bridgePath_continuous` — discharge recipe


> ✅ **DISCHARGED 2026-06-04** (branch `phase2-bridgepath`). Converted from `axiom` to a real `def`/`theorem` backed by `Jacobians/Bridge/BridgePath.lean` (smooth path-connectedness of a connected complex 1-manifold). See [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) → Recently discharged. The recipe below is retained as historical record.


**Location:** `Jacobians/Bridge/KirovLineIntegral.lean:167`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 2 &nbsp;&nbsp; **Est:** ~1 hour, ~5 LOC, in `Jacobians/Bridge/BridgePath.lean` (the new file created when `bridgePath` is discharged)
**Blocked by:** `bridgePath`

**Statement (verbatim):**
```lean
/-- The chosen path is continuous. -/
axiom bridgePath_continuous (P₀ P : X) : Continuous (bridgePath (X := X) P₀ P)
```

**Why it's an axiom right now:** Pure scaffolding around `bridgePath`. The docstring at `KirovLineIntegral.lean:108–114` is explicit that of the six `bridgePath*` axioms, only `bridgePath` and `bridgePath_lineIntegrable` are load-bearing in `kirovBackedFunctional` (per `#print axioms`); the four endpoint/regularity axioms (this one plus `_chart_differentiable`, `_at_zero`, `_at_one`) "are scaffolding for a future discharge route via `PathConnectedSpace.somePath` + smoothing". Once `bridgePath` is a real `def` built from a Mathlib `Path` via `Path.extend`, continuity is immediate.

**Proof recipe**

The recipe assumes `bridgePath` has been discharged per [`bridgePath.md`](bridgePath.md): `bridgePath P₀ P` is now `bridgePathOfPath (PathConnectedSpace.somePath P₀ P)` where `bridgePathOfPath : Path P₀ P → (ℝ → X)` is a chart-line concatenation, ultimately of the form `(γ.extend)` (or a finite `Path.trans` thereof, then extended).

1. **Reduce to continuity of `Path.extend`.** The route-A construction in [`bridgePath.md`](bridgePath.md) step 4 produces, in the simplest sub-case, `bridgePath P₀ P = (PathConnectedSpace.somePath P₀ P).extend`. For a `Path`, `Path.extend` is a `C(ℝ, X)` (bundled continuous map) — see `Mathlib/Topology/Path.lean:189`:
   ```lean
   def extend : C(ℝ, X) where
     toFun := IccExtend zero_le_one γ
     continuous_toFun := γ.continuous.Icc_extend'
   ```
   Continuity of the underlying function is exactly `Path.continuous_extend` (`Mathlib/Topology/Path.lean:199`):
   ```lean
   theorem continuous_extend : Continuous γ.extend
   ```

2. **Discharge the multi-piece case.** If `bridgePath` is a `Path.trans`-concatenation of chart-lines (route A in [`bridgePath.md`](bridgePath.md)), continuity follows because (a) each `chartLine` is a composition of continuous maps (the affine ℝ → ℂ map, then `(extChartAt _).symm` which is continuous on its target — `Mathlib/Geometry/Manifold/SmoothManifoldWithCorners.lean` ecosystem), and (b) `Path.trans` preserves continuity by construction (`Mathlib/Topology/Path.lean`; the `continuous_toFun` field of the resulting `Path` is checked by Mathlib). After `.extend`, apply `Path.continuous_extend` (`:199`).

3. **Tactic-level proof.**
   ```lean
   theorem bridgePath_continuous (P₀ P : X) :
       Continuous (bridgePath (X := X) P₀ P) := by
     unfold bridgePath           -- now bridgePathOfPath of a Mathlib Path
     exact Path.continuous_extend _   -- or `.continuous` if not pre-extended
   ```
   In the multi-chart case use `(constructed_path).continuous_extend` instead; both are single-line discharges.

4. **Replace `axiom` with `theorem` at `KirovLineIntegral.lean:167`.** The fact will live in `Jacobians/Bridge/BridgePath.lean` alongside `bridgePath`; remove the `axiom` line in `KirovLineIntegral.lean` and re-export.

**Files touched**
- `Jacobians/Bridge/BridgePath.lean` — add `theorem bridgePath_continuous` (4 lines).
- `Jacobians/Bridge/KirovLineIntegral.lean` — delete `axiom bridgePath_continuous` at `:167` (replaced by re-export from the new file, or by an `attribute` reshuffle).

**Acceptance**
- `lake build Jacobians.Bridge.KirovLineIntegral` succeeds.
- `#print axioms Jacobians.Bridge.kirovBackedFunctional` (`KirovLineIntegral.lean:301`) no longer lists `bridgePath_continuous` (it was not load-bearing per `:108–114`, so any downstream consumer that does depend on it gets the same treatment).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the `bridgePath` definition chosen in its parent recipe uses a route that does **not** factor through a Mathlib `Path` (e.g. a hand-rolled `ℝ → X` that's not a `Path.extend`), this recipe's one-line proof breaks. Escalate by re-deriving continuity from the concrete builder used in `bridgePath`'s discharge — still small, but no longer a one-liner.
