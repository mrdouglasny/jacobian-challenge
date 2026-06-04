# `bridgePath_at_one` — discharge recipe


> ✅ **DISCHARGED 2026-06-04** (branch `phase2-bridgepath`). Converted from `axiom` to a real `def`/`theorem` backed by `Jacobians/Bridge/BridgePath.lean` (smooth path-connectedness of a connected complex 1-manifold). See [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) → Recently discharged. The recipe below is retained as historical record.


**Location:** `Jacobians/Bridge/KirovLineIntegral.lean:191`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~10 minutes, ~2 LOC, in `Jacobians/Bridge/BridgePath.lean`
**Blocked by:** `bridgePath`

**Statement (verbatim):**
```lean
/-- The chosen path ends at `P`. -/
axiom bridgePath_at_one (P₀ P : X) : bridgePath (X := X) P₀ P 1 = P
```

**Why it's an axiom right now:** Mirror of [`bridgePath_at_zero`](bridgePath_at_zero.md). Per the docstring at `KirovLineIntegral.lean:108–114`, this is endpoint scaffolding around `bridgePath`, not load-bearing in `kirovBackedFunctional`. Once `bridgePath` is a real `def` built from a Mathlib `Path P₀ P`, the end-at-`P` property is `Path.target` (immediate from the `Path` structure).

**Proof recipe**

This recipe assumes `bridgePath` was discharged per [`bridgePath.md`](bridgePath.md): `bridgePath P₀ P = bridgePathOfPath (PathConnectedSpace.somePath P₀ P)`.

1. **Reduce to `Path.extend_one`.** For any `γ : Path P₀ P`, `γ.extend 1 = P` is `Path.extend_one` (`Mathlib/Topology/Path.lean:220`):
   ```lean
   @[simp] theorem extend_one : γ.extend 1 = y := by simp
   ```
   The underlying point identity is `Path.target` (`Mathlib/Topology/Path.lean:99`: `γ 1 = y`).

2. **Discharge the multi-piece case.** If `bridgePath` is a chart-line concatenation (route A in [`bridgePath.md`](bridgePath.md)), the construction explicitly arranges the **last** piece to end at `P`. `Path.trans` preserves target-of-last; the discharge is `by simp [bridgePath]` then `Path.target`/`Path.extend_one`.

3. **Tactic body.**
   ```lean
   theorem bridgePath_at_one (P₀ P : X) : bridgePath (X := X) P₀ P 1 = P := by
     unfold bridgePath
     simp [Path.extend_one, Path.target]
   ```
   Symmetric to [`bridgePath_at_zero`](bridgePath_at_zero.md) — if one works, the other works with `0 ↦ 1`, `P₀ ↦ P`, `extend_zero ↦ extend_one`, `Path.source ↦ Path.target`.

4. **Replace `axiom` with `theorem` at `KirovLineIntegral.lean:191`.** Move into `Jacobians/Bridge/BridgePath.lean`.

**Files touched**
- `Jacobians/Bridge/BridgePath.lean` — add `theorem bridgePath_at_one` (~2 LOC).
- `Jacobians/Bridge/KirovLineIntegral.lean` — delete `axiom bridgePath_at_one` at `:191`.

**Acceptance**
- `lake build Jacobians.Bridge.KirovLineIntegral` succeeds.
- `#print axioms` of any downstream consumer that mentions `bridgePath_at_one` no longer lists it.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Same as [`bridgePath_at_zero`](bridgePath_at_zero.md): if `bridgePath`'s parent recipe routes through a reparametrization that doesn't preserve the right endpoint definitionally, the proof is still trivial but needs the matching reparametrization lemma. Flag if `unfold bridgePath` does not reduce to a `Path.extend`-shaped expression.
