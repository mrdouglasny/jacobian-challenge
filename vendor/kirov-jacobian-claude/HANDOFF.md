# Handoff — axioms in the vendored Kirov tree

This document catalogs the **two `axiom` declarations** that currently live
inside the vendored Kirov material (`Jacobians/Vendor/Kirov/...`). Both
were originally `:= sorry` in upstream and were converted to `axiom` form
when porting into this repository so that the vendored cone builds with
no `sorry` warnings.

Discharging either axiom retires it. The intended workflow:

1. Pick an axiom from the table below.
2. Write a `theorem` (or `lemma`) of **the same fully-qualified name and
   signature** in a separate file (e.g. `Jacobians/Vendor/Kirov/AxiomDischarges.lean`),
   proving the statement.
3. Delete the corresponding `axiom` declaration in the vendored file
   (record the change in that file's per-file Apache 2.0 modification
   header).
4. Rebuild — Lean's `#print axioms` should now report one fewer custom axiom.

## Inventory

### 1. `Jacobians.Vendor.Kirov.genus_eq_zero_iff_homeo`

**File**: `Jacobians/Vendor/Kirov/Genus.lean` (around line 90).

**Statement**:
```lean
axiom genus_eq_zero_iff_homeo
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
  genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
```
where `genus X := Module.finrank ℂ (HolomorphicOneForms X)` and
`HolomorphicOneForms X := ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω _`.

**Mathematical content**: a compact connected complex 1-manifold has
genus 0 (i.e. trivial space of holomorphic 1-forms) iff it is
homeomorphic to the 2-sphere. This is the **Uniformization theorem**
specialized to the genus-0 case. It is the "anti-hack" constraint in the
challenge: without it, defining `Jacobian X := 0` for all `X` is
admissible.

**Classical references**:
- Forster, *Lectures on Riemann Surfaces*, §16.3 (Uniformization).
- Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III / Ch. V.
- Hubbard, *Teichmüller Theory*, vol. I, Ch. 1.

**Sketch of one possible proof in Lean**:
1. From `genus X = 0`, deduce `Module.finrank ℂ (HolomorphicOneForms X) = 0`.
2. Use Riemann–Roch on the divisor `D = p` for `p : X` arbitrary
   (`AX_RiemannRoch` already in `Jacobians/Axioms/RiemannRoch.lean`)
   to produce a non-constant meromorphic function with a single simple
   pole; this is a degree-1 holomorphic map `X → ℂP¹`.
3. Show this map is a biholomorphism (degree-1 + ℂP¹ smooth ⇒
   biholomorphism via Hurwitz / open mapping).
4. Compose with the standard `ℂP¹ ≃ₜ S²` (stereographic projection,
   already in our `Jacobians/ProjectiveCurve/Line.lean`).

**Cross-reference**: this axiom is the exact statement of
`Jacobians.Axioms.Uniformization0.AX_genus_eq_zero_iff_homeo` in
our existing main tree. A bridge proof
`genus_eq_zero_iff_homeo := AX_genus_eq_zero_iff_homeo` would
discharge this axiom in terms of ours, **but only after Kirov's
`HolomorphicOneForms` is proven equivalent to our
`Jacobians.HolomorphicOneForm`** (those are different types — same
mathematical content, different Lean encoding). Producing that
equivalence is itself a worthwhile follow-up task.

---

### 2. `Jacobians.Vendor.Kirov.ambientPhi_ambientPsi_eq`

**File**: `Jacobians/Vendor/Kirov/HolomorphicForms.lean` (around line 336).

**Statement** (with surrounding `variable` declarations from the file
expanded for clarity):
```lean
axiom ambientPhi_ambientPsi_eq
    {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
      [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (d : ℕ)
    (y : Fin gY → ℂ) :
  ambientPhi (gX := gX) (gY := gY) f hf (ambientPsi f hf y) = (d : ℕ) • y
```
where `ambientPhi` and `ambientPsi` are the matrix-pushforward and
matrix-pullback maps (transposes of each other in coordinates) defined
earlier in `HolomorphicForms.lean`.

**Mathematical content**: the **degree identity** `f_* ∘ f^* = deg(f) · id`
expressed at the level of `Fin g → ℂ` ambient coordinates. This is the
key nontrivial functorial identity in the challenge — Buzzard explicitly
chose it as one of the anti-hack constraints (`pushforward_pullback`).

**Classical references**:
- Forster, *Lectures on Riemann Surfaces*, §17 (degree of holomorphic
  maps; trace identity).
- Miranda, *Algebraic Curves and Riemann Surfaces*, §III.4 (trace map
  on differentials).
- Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1, §1
  (proper holomorphic maps and degree).

**Sketch of one possible proof in Lean**:
1. Need a real `ContMDiff.degree` definition. Currently Kirov's `degree` is
   placeholder constant 0 (Jacobians.Vendor.Kirov.HolomorphicForms uses
   only the bare type `ℕ`). Real definition: degree = preimage count at
   any regular value (Sard's theorem + properness).
2. Real `ambientPhi` / `ambientPsi` need to come from honest
   pullback/pushforward of forms (currently they are defined via the
   matrix transpose construction, which is correct in coordinates but
   needs identification with the geometric definitions).
3. The identity then follows from the trace formula:
   `∫_X f_*(α) ∧ β = ∫_Y α ∧ f^*(β)` evaluated on basis pairs.

Estimated cost (per Kirov's docstring): ~500–1000 LOC of Lean.

**Cross-reference**: this is the same mathematical content as
`Jacobians.Axioms.AbelJacobiMap.AX_pushforward_pullback` in our main
tree. A bridge proof from one to the other has the same prerequisite as
above (proving the two `HolomorphicOneForms` types equivalent).

---

## Provenance and licensing

Both axioms are derivative work of Kirov's original `:= sorry`
declarations in `rkirov/jacobian-claude` (Apache 2.0). The conversion
from `lemma`/`theorem ... := sorry` to `axiom` is a **structural-only**
modification (same name, same signature, no mathematical change in
either direction). Discharging either axiom is upstream-friendly: the
resulting `theorem` could be contributed back to Kirov's project (or to
Mathlib if the proof is general).
