# `genus_eq_zero_iff_homeo` — discharge recipe

**Location:** `Jacobians/Vendor/Kirov/Genus.lean:94`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~1 hour, <30 LOC
**Blocked by:** `AX_genus_eq_zero_iff_homeo` (main tree, `Jacobians/Axioms/Uniformization0.lean:55`)

**Statement (verbatim):**
```lean
axiom genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
```

**Why it's an axiom right now:** This is the genus-0 case of the Uniformization
theorem (Forster §16.3; Miranda Ch. V): a compact connected Riemann surface
with `Module.finrank ℂ (HolomorphicOneForms X) = 0` admits a degree-1
meromorphic function and is hence biholomorphic to `ℂP¹ ≃ₜ S²`. Upstream
(`vendor/kirov-jacobian-claude`) had this as `:= sorry`; the port to this
repository converted it to `axiom` form so the vendored cone builds without
`sorry` warnings (see `vendor/kirov-jacobian-claude/HANDOFF.md` §1). It is
the "anti-hack" constraint on Kirov's side that prevents the trivial
`Jacobian X := 0` solution. The exact same statement — modulo (i) the HOF
encoding and (ii) a `Nonempty X` hypothesis — is axiomatized on the main
tree as `Jacobians.Axioms.AX_genus_eq_zero_iff_homeo`
(`Jacobians/Axioms/Uniformization0.lean:55`). Because the main-tree axiom
is already in scope and the two types of holomorphic 1-form are linked by
`bridgeFormEquiv`, the Kirov-side axiom should be discharged as a
*bridge theorem* rather than re-proved from RR + SD.

**Proof recipe**

The plan is: discharge Kirov's `genus_eq_zero_iff_homeo` by `exact`ing the
main tree's `AX_genus_eq_zero_iff_homeo` after transporting Kirov's
`genus X = 0` hypothesis through the bridge equivalence between the two
HOF encodings. (The genuine textbook proof plan for the underlying math is 
documented in `docs/planning/AX_genus_eq_zero_iff_homeo.md` for the main-tree axiom.)

1. **Verify the HOF equivalence already exists.** The bridge
   ```lean
   noncomputable def bridgeFormEquiv :
     HolomorphicOneForm X ≃ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X
   ```
   is constructed in `Jacobians/Bridge/KirovHolomorphicEquiv.lean:277-289`
   (from `bridgeForm` and `BridgeFormEquiv.inverseForm`, with both round-trip
   identities proven at `:240` and `:269`). No new infrastructure is needed
   on this side.

2. **State and prove a `genus`-agreement lemma.** Add to
   `Jacobians/Bridge/KirovHolomorphicEquiv.lean` (or a new file
   `Jacobians/Bridge/KirovGenus.lean`):
   ```lean
   theorem genus_eq_kirovGenus
       {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
       [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] :
       Jacobians.RiemannSurface.genus X = Jacobians.Vendor.Kirov.genus X := by
     unfold Jacobians.RiemannSurface.genus Jacobians.Vendor.Kirov.genus
     exact (LinearEquiv.finrank_eq (bridgeFormEquiv (X := X))).symm
   ```
   - `Jacobians.RiemannSurface.genus` is defined at
     `Jacobians/RiemannSurface/Genus.lean:39` as
     `Module.finrank ℂ (HolomorphicOneForm X)`.
   - `Jacobians.Vendor.Kirov.genus` is defined at
     `Jacobians/Vendor/Kirov/Genus.lean:78` as
     `Module.finrank ℂ (HolomorphicOneForms X)`.
   - `LinearEquiv.finrank_eq` is the Mathlib lemma transporting
     `Module.finrank` across a `≃ₗ`.

3. **Discharge the axiom via the main-tree axiom + step (2).** In a new
   file `Jacobians/Vendor/Kirov/AxiomDischarges.lean` (the location suggested
   by `vendor/kirov-jacobian-claude/HANDOFF.md` step 2), write:
   ```lean
   import Jacobians.Vendor.Kirov.Genus
   import Jacobians.Axioms.Uniformization0
   import Jacobians.Bridge.KirovHolomorphicEquiv   -- for genus_eq_kirovGenus

   namespace Jacobians.Vendor.Kirov

   open Jacobians.Axioms Jacobians.RiemannSurface

   theorem genus_eq_zero_iff_homeo
       {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
       [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
       [IsManifold 𝓘(ℂ, ℂ) ω X] :
       Jacobians.Vendor.Kirov.genus X = 0 ↔
         Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
     rw [← Jacobians.Bridge.genus_eq_kirovGenus (X := X)]
     exact AX_genus_eq_zero_iff_homeo

   end Jacobians.Vendor.Kirov
   ```
   The main-tree axiom `AX_genus_eq_zero_iff_homeo`
   (`Jacobians/Axioms/Uniformization0.lean:55`) takes the *same* instance
   bundle except that it omits `[Nonempty X]`; Kirov's stronger
   hypothesis set therefore satisfies it directly.

4. **Delete the original axiom.** Remove
   `axiom genus_eq_zero_iff_homeo` at `Jacobians/Vendor/Kirov/Genus.lean:94`
   and update the per-file Apache-2.0 modification header. The new
   `theorem` shadows the deleted axiom under the *same fully qualified
   name* `Jacobians.Vendor.Kirov.genus_eq_zero_iff_homeo`, so no downstream
   `LineIntegral.lean` / `HolomorphicForms.lean` consumer needs to change.

5. **Note on `Nonempty` propagation.** Kirov's `HolomorphicOneForms` type
   in `Jacobians/Vendor/Kirov/Genus.lean:48` carries `[Nonempty X]` in its
   instance set; the main-tree `HolomorphicOneForm` does not require
   `Nonempty X` (see `Jacobians/Axioms/Uniformization0.lean:55-58`). This route
   imports `Nonempty X` from the consumer side, so this asymmetry is
   harmless: every site that wants to invoke Kirov's theorem already
   carries `[Nonempty X]`, and the main-tree axiom is happy with a strict
   subset of the hypotheses. Kirov's `LineIntegral` consumer at
   `Jacobians/Vendor/Kirov/LineIntegral.lean:64-65` already uses the same
   `[Nonempty X]`-bearing instance bundle.

**Files touched**
- `Jacobians/Bridge/KirovHolomorphicEquiv.lean` — add the
  `genus_eq_kirovGenus` bridge lemma (one new theorem, ≤ 8 LOC).
- `Jacobians/Vendor/Kirov/AxiomDischarges.lean` — **new file**; contains the
  `theorem genus_eq_zero_iff_homeo` discharge, imports
  `Jacobians.Axioms.Uniformization0` and `Jacobians.Bridge.KirovHolomorphicEquiv`.
- `Jacobians/Vendor/Kirov/Genus.lean` — delete the `axiom` block at
  `:94-96`; update the modification header at `:9-13` to record the
  axiom-deletion (per `HANDOFF.md` step 3).
- `Jacobians.lean` (or the relevant root manifest) — add `import
  Jacobians.Vendor.Kirov.AxiomDischarges` so the theorem is in scope for
  downstream consumers (verify nothing else regresses).

**Acceptance**
- `lake build Jacobians.Vendor.Kirov.Genus` succeeds (the theorem is now
  in `Jacobians.Vendor.Kirov.AxiomDischarges`; `Genus.lean` no longer
  declares the axiom).
- `lake build Jacobians.Vendor.Kirov.LineIntegral` succeeds — this is
  the narrowest downstream consumer of `Genus.lean`
  (`Jacobians/Vendor/Kirov/LineIntegral.lean:15` imports `HolomorphicForms`
  which transitively imports `Genus`).
- `#print axioms Jacobians.Vendor.Kirov.genus_eq_zero_iff_homeo` no longer
  reports `Jacobians.Vendor.Kirov.genus_eq_zero_iff_homeo` itself; it now
  reports `Jacobians.Axioms.AX_genus_eq_zero_iff_homeo` (the discharged
  Kirov axiom traces back to the main-tree axiom — net axiom count drops
  by 1 globally because we removed Kirov's `axiom` declaration and
  reused an *existing* main-tree axiom).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns
  PASS; the fleet axiom scanner registers a count drop of 1 in
  `Jacobians/Vendor/Kirov/Genus.lean`.

**Risk / escalation triggers**
- If `bridgeFormEquiv` (`Jacobians/Bridge/KirovHolomorphicEquiv.lean:277`)
  turns out to depend on its own structural axioms whose composition
  introduces a *new* axiom downstream of `genus_eq_zero_iff_homeo`, the
  net axiom count may not drop. Verify with
  `#print axioms` before declaring the recipe discharged; if a new
  Kirov-bridge axiom appears, escalate to a human to decide whether to
  defer this discharge until the bridge is itself axiom-free (see
  `vendor/kirov-jacobian-claude/HANDOFF.md` §"two bridge axioms").
- If Lean rejects `LinearEquiv.finrank_eq` in step 2 due to a typeclass
  mismatch (the `HolomorphicOneForms` instance set carries `Nonempty X`
  while `HolomorphicOneForm` does not), escalate — do not silently weaken
  or strengthen the statement.
- If the project requires retiring the *underlying* uniformization assumption completely, escalate: this document is merely bridging the vendor axiom to the main tree. Proving the main-tree uniformization axiom directly via Riemann–Roch and Serre Duality is a separate multi-month sheaf-cohomology project documented in `docs/planning/AX_genus_eq_zero_iff_homeo.md`.

### Gemini critique addressed:
- Recalibrated the effort estimate from 7 (~1 focused week, ~150–250 LOC) down to 1 (~1 hour, <30 LOC) because this is a direct, trivial bridging task.
- Fixed Lean 4 implicit argument unification bugs in Steps 2 and 3 by explicitly supplying `(X := X)` to `bridgeFormEquiv` and `genus_eq_kirovGenus`.
- Removed the out-of-scope "Route (b)" direct proof plan entirely, as the genuine textbook proof strategy belongs to the main-tree `AX_genus_eq_zero_iff_homeo` axiom documentation, not this vendor duplicate's bridging plan.

---
**Vetting trail.** Critique: `_vetting/genus_eq_zero_iff_homeo.md`. Verdict: revise. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
