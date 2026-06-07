# `bridgePath_at_zero` — discharge recipe


> ✅ **DISCHARGED 2026-06-04** (branch `phase2-bridgepath`). Converted from `axiom` to a real `def`/`theorem` backed by `Jacobians/Bridge/BridgePath.lean` (smooth path-connectedness of a connected complex 1-manifold). See [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) → Recently discharged. The recipe below is retained as historical record.


**Location:** `Jacobians/Bridge/KirovLineIntegral.lean:188`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~10 minutes, ~2 LOC, in `Jacobians/Bridge/BridgePath.lean`
**Blocked by:** `bridgePath`

**Statement (verbatim):**
```lean
/-- The chosen path starts at `P₀`. -/
axiom bridgePath_at_zero (P₀ P : X) : bridgePath (X := X) P₀ P 0 = P₀
```

**Why it's an axiom right now:** Pure scaffolding around `bridgePath`. Per the docstring at `KirovLineIntegral.lean:108–114`, this is one of the four endpoint/regularity axioms that "are scaffolding for a future discharge route via `PathConnectedSpace.somePath` + smoothing" and is **not** load-bearing in `kirovBackedFunctional`. Once `bridgePath` is a real `def` built from a Mathlib `Path P₀ P`, the start-at-`P₀` property is `Path.source` (immediate from the `Path` structure).

**Proof recipe**

This recipe assumes `bridgePath` was discharged per [`bridgePath.md`](bridgePath.md): `bridgePath P₀ P = bridgePathOfPath (PathConnectedSpace.somePath P₀ P)` where `bridgePathOfPath` is a chart-line concatenation that, by construction, agrees with `(Path P₀ P).extend` at the endpoints.

1. **Reduce to `Path.extend_zero`.** For any `γ : Path P₀ P`, `γ.extend 0 = P₀` is `Path.extend_zero` (`Mathlib/Topology/Path.lean:218`):
   ```lean
   @[simp] theorem extend_zero : γ.extend 0 = x := by simp
   ```
   This already chains through `Path.source` (`Mathlib/Topology/Path.lean:95`: `γ 0 = x`).

2. **Discharge the multi-piece case.** If `bridgePath` is a chart-line concatenation (route A in [`bridgePath.md`](bridgePath.md)), the construction explicitly arranges the first piece to start at `P₀` (the `Path.trans` operator preserves source-of-first / target-of-last by definition; `Mathlib/Topology/Path.lean` Path.trans). Either way the discharge is `by simp [bridgePath]` followed by `Path.source`/`Path.extend_zero`.

3. **Tactic body.**
   ```lean
   theorem bridgePath_at_zero (P₀ P : X) : bridgePath (X := X) P₀ P 0 = P₀ := by
     unfold bridgePath
     simp [Path.extend_zero, Path.source]
   ```
   In the rare case the construction goes through a finer reparametrization, this becomes a 3-line `rfl`/`simp` chain rather than a one-liner — still effort-1.

4. **Replace `axiom` with `theorem` at `KirovLineIntegral.lean:188`.** Move into `Jacobians/Bridge/BridgePath.lean`.

**Files touched**
- `Jacobians/Bridge/BridgePath.lean` — add `theorem bridgePath_at_zero` (~2 LOC).
- `Jacobians/Bridge/KirovLineIntegral.lean` — delete `axiom bridgePath_at_zero` at `:188`.

**Acceptance**
- `lake build Jacobians.Bridge.KirovLineIntegral` succeeds.
- `#print axioms Jacobians.Bridge.kirovBackedFunctional` (`KirovLineIntegral.lean:301`) was already not depending on this axiom (see `:108–114`), but any downstream theorem that *does* mention `bridgePath_at_zero` (e.g. a forthcoming `kirovBackedFunctional_local_antiderivative` at `:357`) no longer lists it.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `bridgePath`'s parent recipe wraps the construction in a reparametrization that doesn't preserve endpoints (e.g. an aggressive smoothing schedule that defines `bridgePath P₀ P 0 := P₀` only definitionally-after-`unfold`), the proof becomes a chain of `simp` lemmas about the smoother; still trivial, but flag if the `unfold` doesn't fire.
