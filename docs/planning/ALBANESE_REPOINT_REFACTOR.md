# Refactor plan — repoint `ofCurve_isJacobian` onto the A1+AK interface

**Goal.** Make the Albanese categoricity headline `Jacobians.ofCurve_isJacobian`
rest on the minimal vetted interface — `AX_torus_uniformization` (A1) +
`AX_curve_image_subgroup_isOpen` (AK) — instead of the three legacy torus axioms
`AX_torus_self_albanese` / `AX_period_functoriality` / `AX_curve_generates_jacobian`.
G2/G3/G4 are **already proven** as theorems from A1+AK (in `AlbaneseClose.lean`,
`#print axioms`-verified: std-3 + A1 only for G2/G3; +AK for G4). This refactor only
**wires the proven theorems into the headline** and retires the legacy axioms.

Status precondition: do this as **its own commit from the current committed base**
(`64dd685`), nothing else in flight.

---

## The relevant import DAG (extracted, not guessed)

```
        Mathlib · Challenge · Bridge.KirovHolomorphicEquiv · Vendor.Kirov.ZLatticeQuotient
                                   │
                                   ▼
                        Axioms.TorusAlbanese
                        (3 legacy axioms + all torus defs/lemmas)
            ┌──────────────────────┼───────────────────────┐
            ▼                      ▼                        ▼
     UniversalProperty     Axioms.AlbaneseInterface   Axioms.UniversalProperty
     (ofCurve_isJacobian    (A1, AK)                   (DOC-ONLY — no decls,
      on 3 legacy axioms)         │                     just a docstring list)
            │      ┌──────────────┘
            ▼      ▼
       AlbaneseClose  (G2/G3/G4 from A1+AK)
       ◀── ORPHAN: imported by NOBODY (not even the root) ──▶

   Jacobians (root, Jacobians.lean) ─ imports UniversalProperty (+ Axioms.UniversalProperty);
                                       does NOT import AlbaneseClose.
```

### Verified facts (each checked against the tree)
1. **No cycle** for `UniversalProperty → Axioms.AlbaneseInterface`: AlbaneseInterface
   imports only `Axioms.TorusAlbanese`, whose cone (Challenge / KirovHolomorphicEquiv /
   ZLatticeQuotient / Mathlib) does **not** contain UniversalProperty. UniversalProperty
   already imports TorusAlbanese, so the only new node added is AlbaneseInterface itself.
2. **`AlbaneseClose` is an orphan** → safe to delete once its content is relocated; the
   proven G2/G3/G4 are currently **not in the headline closure** at all (CI builds them
   via the lib glob, but the root module never imports them).
3. **`Axioms.UniversalProperty` is doc-only** → deleting the 3 axioms breaks no term;
   just refresh its docstring.
4. All loop/bridge machinery the discharge needs already resolves in UniversalProperty's
   cone (`analyticLoopsGenerateH1`, `exists_isClosedSmoothLoop_…`,
   `loopIntegralToH1_loopToHomology_apply`, `port_lineIntegral_bridgeKD`,
   `bridgeKDFormEquiv`, `periodMap*`, `H1`, `jacobianBasis`, …). The earlier
   "`torusPathSpeed_comp_eq_mfderiv` missing" was a namespace false-alarm — it is
   `UniversalProperty.lean:217`.
5. **Axiom use-sites in `UniversalProperty.lean` (8):**
   - `AX_torus_self_albanese`: 138, 175 (descent `let P`), 367, 369 (factorize hyp), 375, 418 (`let S`)
   - `AX_period_functoriality P f hf`: 147, 184, 385 (each with `P` = the self-Albanese presentation)
   - `AX_curve_generates_jacobian x₀ hg`: 456 (uniqueness `eq_of_eqOn_dense`)
   - sole consumer of `ofCurve_isJacobian`: line 568 (`isJacobian_unique`), same file.

---

## The intrinsic constraint (why it's a reorder, not just an import)

`period_functoriality` (G3) is **consumed early** — line 147, inside
`jacobianUniversalPhi` — but its **proof lands late** (it needs
`torusPullback_pathIntegral_naturality` at 280 and the relocated bridge). G2 is trivial
(= A1) and G4 is consumed late (456), so G3 alone forces an ordering change. Confirmed
reorder-safe: lines 217 & 280 contain **no** references to `jacobianUniversalPhi` /
`_holo` / `_exists` (the 131–216 descent block), so the two blocks can be transposed.

Target declaration order inside `UniversalProperty.lean`:

```
[existing pre-131 content]
→ naturality block:  torusPathSpeed_comp_eq_mfderiv (217), torusPullback_pathIntegral_naturality (280),
                     torusAmbientLinear_ofCurveAmbient_sub (332)
→ interface block (relocated from AlbaneseClose, under `import Axioms.AlbaneseInterface`):
      torus_self_albanese (G2)
      torusLineIntegral_const_zero
      torusAlbaneseCoordinateOfFunctional_mem_lattice_of_loopPeriod (R2)
      torusPathSpeed_comp_eq_mfderiv_self
      torusComp_chartDifferentiableAt
      torusInvariantOneFormSection_translate
      torusLineIntegral_translate
      torusPullback_lineIntegral_naturality_of_closedSmoothLoop
      torusAmbientLinear_periodMapInBasis_eq
      torusAmbientLinear_periodMapInBasis_mem (the bridge)
      period_functoriality (G3)
      curve_generates_jacobian (G4)
→ descent block (moved down from 131–216):  jacobianUniversalPhi, _holo, _exists
→ factorize lemmas (357–440)
→ ofCurve_isJacobian, isJacobian_unique (462–568)
```

Two equivalent ways to achieve it — **(i) move naturality up** past the descent block,
or **(ii) move the descent block (131–216, ~85 lines) down** past naturality+interface.
**Recommend (ii):** the descent block is one contiguous 3-decl unit; moving it once is
less error-prone than threading the naturality lemmas through it.

---

## Step-by-step

1. **Commit base** — already at `64dd685`, clean. (done)
2. `import Jacobians.Axioms.AlbaneseInterface` in `UniversalProperty.lean`.
3. **Relocate** the entire body of `AlbaneseClose.lean` (the interface block above) into
   `UniversalProperty.lean`, placed after the naturality block. Namespace shift
   `Jacobians.RiemannSurface` → `Jacobians` (UniversalProperty's namespace); verify the
   `open Jacobians.Axioms` already present covers the references. The `curve_generates_jacobian`
   proof's `change IsTopologicalAddGroup (Jacobians.Jacobian X)` must still elaborate here
   (same instance context — verify).
4. **Reorder (ii):** move `jacobianUniversalPhi`/`_holo`/`_exists` (131–216) to directly
   before the factorize lemmas (357).
5. **Swap the 8 sites** to the theorems:
   - `(AX_torus_self_albanese (A := A))` → `(torus_self_albanese (A := A))`
   - `AX_period_functoriality P f hf` → `period_functoriality f hf`
     (works because `P` is bound to `(torus_self_albanese …).toTorusPresentation`; the
     existing `simpa [ΛX, L, Lc]` bridges the `Lc.toAddMonoidHom` vs `L.toAddMonoidHom` form)
   - `AX_curve_generates_jacobian x₀ hg` → `curve_generates_jacobian x₀ hg`
6. **Retire axioms:** delete `AX_torus_self_albanese` (TorusAlbanese:293),
   `AX_period_functoriality` (:325), `AX_curve_generates_jacobian` (:510) and their
   docstrings. Keep `TorusSelfAlbanesePresentation`, `torusAmbientLinear`,
   `torusAlbaneseCoordinateOfFunctional`, `torusLineIntegral`, etc. (still used).
7. **Delete** `AlbaneseClose.lean` (orphan). Refresh docstrings of
   `Axioms.UniversalProperty.lean` and `Axioms.AlbaneseInterface.lean`.
8. **Verify:** `lake build` green; then
   `#print axioms Jacobians.ofCurve_isJacobian` →
   expect `[propext, Classical.choice, Quot.sound, AX_torus_uniformization,
   AX_curve_image_subgroup_isOpen]` (3 legacy axioms gone).
9. **Docs:** update `UNIFIED_ALBANESE_DISCHARGE_PLAN.md`, `AXIOM_AUDIT.md`, README
   "Current Status" counts in the same commit.

---

## Axiom-footprint outcome

| Stage | `ofCurve_isJacobian` rests on |
|---|---|
| now (`64dd685`) | 3 legacy axioms (all sound; all proven-reducible to A1+AK) |
| after this refactor | **A1 (`AX_torus_uniformization`) + AK (`AX_curve_image_subgroup_isOpen`)** |
| after AK discharge (vendor Kirov `JacobiLocalMap`) | **A1 alone** |

The Kirov-AK discharge lands in the **same relocated interface block** (AK's proof needs
the Jacobian's rich context, just like G4), so it composes with this refactor — one
architectural home for both. Scope the `JacobiLocalMap` dependency cone for cycle-freeness
before that step (separate task).

---

## Risks
- **Namespace shift** (`RiemannSurface` → `Jacobians`) on relocated decls — references that
  relied on the `RiemannSurface` open may need qualification. Build-check after step 3.
- **`period_functoriality` form match** at the 3 sites — the `P`-explicit→`P`-fixed swap;
  if the `simpa` doesn't close, may need to unfold `torus_self_albanese = AX_torus_uniformization`.
- **G4 instance synthesis** in the new namespace context (the `change … (Jacobians.Jacobian X)`
  + `topologicalAddGroup_of_lieAddGroup` dance) — re-verify it elaborates.
- Headline file is large; do step-by-step `lake env lean Jacobians/UniversalProperty.lean`
  after each of steps 3/4/5 rather than one big-bang edit.
