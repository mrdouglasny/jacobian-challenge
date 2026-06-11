# FLIP_CHECKLIST — the atomic Layer-3 flip commit (L-lane pre-write, 2026-06-11)

The final flip PR waits on ONE input: the T-lane's `FrameResidueTrace` construction,
i.e. a theorem giving (any of these shapes; all are interchangeable via
`Jacobians/Layer3/FlipPrep.lean` + `ResidueAtom.lean`):

* `data.FrameTraceHypothesis` for the canonical `ω₀ = df` datum
  (`nonempty_canonicalForm17Data`, `CanonicalFormDifferential.lean:552`), or
* `kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.FrameTraceHypothesis`
  (the weakest needed form — the residual is honestly `g = 0`-only, PR #194), or
* `∃ data, data.ResidueAtom` at `kirovGenus X = 0` directly.

Everything below is compiled and kernel-verified on branch `feat/layer3-flip-prep`
(`Jacobians/Layer3/FlipPrep.lean`, all declarations standard-3). Call the T-lane
theorem `T` below; write `hsplit : kirovGenus X = 0 → ∃ data, data.FrameTraceHypothesis`
for its genus-split packaging (one `fun _ => ⟨_, T⟩`).

---

## 0. Two findings that shape the flip (read first)

### 0a. Divisor-pin: `serreDuality_equiv` is NOT flippable while `canonicalDivisor` is opaque

`serreDuality_equiv` (`Jacobians/Layer3/Cohomology.lean:59`) is stated with
`Jacobians.Axioms.canonicalDivisor X` — an opaque `axiom` constant
(`Jacobians/RiemannSurface/Cohomology/LineBundleBasic.lean:43`) constrained by **no other
axiom** (verified by census 2026-06-11: only theorems mention it). No theorem can pin the
dimension of `L(canonicalDivisor X − D)`, so the axiom's verbatim statement is underivable
from ANY analytic input. The flip therefore **de-opaques `canonicalDivisor`**
(axiom → `noncomputable def … := Classical.choose serreDuality_equiv_exists`), after which
the verbatim `serreDuality_equiv` is `Classical.choose_spec` — the compiled shape is
`FlipPrep.serreDuality_equiv_for_chosen_K`. **Kernel count: 21 → 18** (both Layer-3 axioms
AND `canonicalDivisor`), not the previously quoted 21 → 19.

Fallback if the community wants the `canonicalDivisor` conversion discussed separately
(it touches the `Jacobians.Axioms` trust surface): flip `h1coh_zero_finrank` + the
keystone only (21 → 20) and land `serreDuality_equiv` + `canonicalDivisor` in an
immediate follow-up. Do NOT attempt to flip `serreDuality_equiv` alone — it is impossible
as stated.

### 0b. Port import cycle: `RiemannRoch.lean` cannot import `KeystonePackaging` directly

The re-pin needs `RiemannRoch.lean` → `KeystonePackaging`, but
`KeystonePackaging → TailGenusTarget → SerreDualityGenus0 → KirovDolbeault.RiemannRoch`
is an existing import chain (also `TailSerre`, `SerreSurjectivitySkeleton` import
`RiemannRoch`). **Base-file split required** (the proven Phase-C pattern): those three
files consume ONLY `MeromorphicFunction.deg_div` (SerreDualityGenus0) and
`lDim_eq_zero_of_deg_neg` (TailSerre, SerreSurjectivitySkeleton) from `RiemannRoch.lean`.

---

## 1. Port side (`vendor/kirov-dolbeault-port/KirovDolbeault/`)

### 1.1 Base-file split (cycle break; no statement changes)

* NEW FILE `KirovDolbeault/RiemannRochDegree.lean`: move verbatim from
  `RiemannRoch.lean` →
  - `MeromorphicFunction.deg_div` (`RiemannRoch.lean:76-79`)
  - `lDim_eq_zero_of_deg_neg` (`RiemannRoch.lean:90-…`)
  (imports: `KirovDolbeault.Abel`, `KirovDolbeault.LinearSystem`,
  `KirovDolbeault.MeromorphicLiouville`, `KirovDolbeault.ProperMapDegreeSheets`,
  `KirovDolbeault.DegDivResidue` — the subset of `RiemannRoch.lean:21-25` they need.)
* `RiemannRoch.lean`: import `KirovDolbeault.RiemannRochDegree` (delete the two moved
  decls; everything else keeps compiling — `deg_canonical`, `lDim_canonical_eq_genus`,
  `exists_singleSimplePole_of_genus_zero_of_rr` stay).
* Redirect imports in `Dolbeault/SerreDualityGenus0.lean`, `Dolbeault/TailSerre.lean`,
  `Dolbeault/SerreSurjectivitySkeleton.lean`, and (check) `GenusSphereHeadline.lean`:
  `import KirovDolbeault.RiemannRoch` → `import KirovDolbeault.RiemannRochDegree`
  (GenusSphereHeadline genuinely uses `exists_riemannRoch_divisor`; it keeps the
  `RiemannRoch` import — it is downstream, no cycle).

### 1.2 The keystone replacement (`Dolbeault/SerreDualityPairing.lean`)

* DELETE `exists_serreDualityData` (**the keystone sorry**, docstring+theorem
  :120-134; theorem head :131, `sorry` at :134) and its two ∀-cover dependents in the
  same file:
  - `arithmeticGenus_eq_genus_serre` (:136-141)
  - `serre_h1_eq_serre` (:143-149)
  (Sole consumers of these two: `Dolbeault/DolbeaultLadder.lean` wrappers, §1.3.)

### 1.3 The ladder re-shape (`Dolbeault/DolbeaultLadder.lean`)

* DELETE the ∀-cover wrappers `arithmeticGenus_eq_genus` (:53-60), `serre_h1_eq`
  (:62-67), `riemannRoch_equality_of_ladder` (:72-87).
* ADD the data-parametrized form (same proof body, `data.serreH1` / `data.arithmeticGenus`
  replacing the `_serre` calls):

  ```lean
  theorem riemannRoch_equality_of_data (𝔘 : FiniteCover X)
      (hR : 𝔘.LocallyRealizable) (data : SerreDualityData 𝔘) :
      ∃ K : Divisor X, ∀ D : Divisor X,
        (lDim D : ℤ) - lDim (K - D) = Divisor.deg X D + 1 - kirovGenus X := by
    refine ⟨data.K, fun D => ?_⟩
    have h := cohomological_riemannRoch 𝔘 hR D
    rw [𝔘.h0Dim_eq_lDim D, data.serre_eq D, data.arithmeticGenus] at h
    exact h
  ```

### 1.4 The unconditional ∃-cover keystone (`Dolbeault/KeystonePackaging.lean`, append)

```lean
/-- THE KEYSTONE, unconditional: T-lane trace assembly + #194 genus split + #193 capstone. -/
theorem exists_serreDualityData_cover :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_cover_of_genus_split_residueAtom
    (fun hg0 => exists_residueAtom_of_exists_frameTrace ⟨_, T⟩)  -- T = T-lane theorem
```

(If `T` lives in a file not already imported by `KeystonePackaging.lean`, add the import
or put this theorem in the T-lane's file instead.)

### 1.5 The consumer re-pin (`RiemannRoch.lean:60-68`)

* Add `import KirovDolbeault.Dolbeault.KeystonePackaging` (legal after §1.1).
* Replace the proof of `exists_riemannRoch_divisor` (statement UNCHANGED — its second
  consumer `exists_singleSimplePole_of_genus_zero_of_rr` :155 and
  `GenusSphereHeadline.lean` keep compiling):

  ```lean
  theorem exists_riemannRoch_divisor : ... := by
    obtain ⟨𝔘, hL, hR, ⟨data⟩⟩ := Dolbeault.exists_serreDualityData_cover (X := X)
    exact Dolbeault.riemannRoch_equality_of_data 𝔘 hR data
  ```

  (The old :66-68 chose the cover via `exists_realizableLerayCover`; the new proof takes
  the cover EXHIBITED by the keystone — the agreed ∃-cover weakening + re-pin,
  `docs/planning/COVER_WIRING.md`. The `LerayCoverExists` import can stay.)

## 2. Our side (`Jacobians/`)

### 2.1 `Jacobians/RiemannSurface/Cohomology/LineBundleBasic.lean` (de-opaque, §0a)

* Add imports: `Jacobians.Layer3.FlipPrep` (+ the T-lane module if needed). No cycle:
  only `Layer3/Cohomology.lean` and `Cohomology/LineBundle.lean` import LineBundleBasic,
  both outside FlipPrep's closure (census 2026-06-11).
* Replace `axiom canonicalDivisor` (:40-45) by:

  ```lean
  /-- The unconditional ∃-K Serre package at the chartDiskCover pin (T-lane + FlipPrep). -/
  theorem serreDuality_equiv_exists (X : Type*) [...same instances...] :
      ∃ K : Jacobians.Axioms.Divisor X,
        Module.finrank ℂ (riemannRochSpace K) = Jacobians.RiemannSurface.genus X ∧
        ∀ D, Nonempty (Jacobians.Layer3.H1coh D ≃ₗ[ℂ]
          Module.Dual ℂ (riemannRochSpace (K - D))) :=
    Jacobians.Layer3.serreDuality_equiv_exists_of_frameTrace (fun _ => ⟨_, T⟩)

  /-- The canonical divisor: the chosen Serre-duality divisor (formerly an opaque axiom). -/
  noncomputable def canonicalDivisor (X : Type*) [...] : Divisor X :=
    Classical.choose (serreDuality_equiv_exists X)

  theorem canonicalDivisor_spec (X : Type*) [...] :
      Module.finrank ℂ (riemannRochSpace (canonicalDivisor X)) = genus X ∧
      ∀ D, Nonempty (Jacobians.Layer3.H1coh D ≃ₗ[ℂ]
        Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D))) :=
    Classical.choose_spec (serreDuality_equiv_exists X)
  ```

  (Namespace/instance details: keep `Jacobians.Axioms.canonicalDivisor` exactly —
  all downstream references are by that name; `H1coh` mention pulls `Layer3.CechH1Bridge`
  transitively via FlipPrep.)

### 2.2 `Jacobians/Layer3/Cohomology.lean` (the two axiom→theorem conversions)

* Add `import Jacobians.Layer3.FlipPrep` (and keep LineBundleBasic import).
* :48-53 `axiom h1coh_zero_finrank` → theorem, statement VERBATIM:

  ```lean
  theorem h1coh_zero_finrank :
      Module.finrank ℂ (H1coh (0 : Divisor X)) = genus X :=
    h1coh_zero_finrank_of_frameTrace (fun _ => ⟨_, T⟩)
  ```

* :55-62 `axiom serreDuality_equiv` → theorem, statement VERBATIM:

  ```lean
  theorem serreDuality_equiv (D : Divisor X) :
      Nonempty (H1coh D ≃ₗ[ℂ]
        Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D))) :=
    (canonicalDivisor_spec (X := X)).2 D
  ```

* Everything below (`riemannRochL3`, `serreDualityL3`, `h0_canonical_L3`,
  `canonicalDivisor_deg_L3`) compiles unchanged. So do the wrappers
  `Jacobians/Axioms/SerreDuality.lean` (`AX_SerreDuality`), `RiemannRochAPI`,
  `SerreDualityAPI`, `SheafCohomologySpec` (same names, same types).

## 3. Verification gates (per CLAUDE.md)

1. `lake env lean` each touched file; `lake build` full tree (port + Jacobians).
2. `#print axioms` on: `h1coh_zero_finrank`, `serreDuality_equiv`,
   `Jacobians.Axioms.canonicalDivisor`-consumers (`AX_SerreDuality`, `AX_RiemannRoch`),
   `exists_riemannRoch_divisor`, `exists_serreDualityData_cover`, and the repo headliners.
   Expect standard-3 (+ unrelated surviving axioms for headliners). NO
   `h1coh_zero_finrank` / `serreDuality_equiv` / `canonicalDivisor` / `sorryAx` anywhere.
3. Regenerate `docs/axiom-report.txt` (`scripts/axiom_report.lean`) and run
   `scripts/check_axiom_consistency.sh` locally before push.

## 4. Ledger / docs touch list (same commit, per AXIOM_AUDIT_FORMAT)

* `AXIOM_AUDIT.md`:
  - Class-3 row (two Layer-3 axioms): → **DISCHARGED <date>** with the route
    (T-lane trace → #194 genus-split atom → #193 capstone → FlipPrep composition);
    update the class-count table (Class 3: 2 → 0).
  - 2a/stub row `LineBundle, canonicalDivisor, LineBundle.ofDivisor (3)` → `(2)`:
    `canonicalDivisor` **DISCHARGED → def** (Classical.choose of the proven ∃-K package).
  - Header counts: kernel axioms 21 → 18.
* `README.md` "Current Status": same counts, same commit.
* `docs/axiom-report.txt`: regenerated (gate 3).
* Close the tracker issue(s) for `h1coh_zero_finrank` / `serreDuality_equiv` (#126
  lineage) and link pinned #82 if the post-mortem log wants the de-opaque note.
* `docs/planning/L_LANE_PROGRESS.log` / `P_LANE_PROGRESS.log`: flip-landed entries.

## 5. Expected diff budget

~6 port files (1 new), 2 Jacobians files, 3 docs. No statement of any surviving axiom
changes; no new axioms; the only deleted SORRY is the keystone
(`SerreDualityPairing.lean:134`).
