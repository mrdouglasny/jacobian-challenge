# `AX_Hyperelliptic_evenEquiv` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:99`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 2 &nbsp;&nbsp; **Est:** ~1 hour, ~10 LOC — definitional once `Hyperelliptic` lands as a parity-dispatched real `def`; mirror of `AX_Hyperelliptic_oddEquiv`.
**Blocked by:** `Hyperelliptic`

**Statement (verbatim):**
```lean
axiom AX_Hyperelliptic_evenEquiv (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Hyperelliptic H ≃ₜ HyperellipticEven H h
```

**Why it's an axiom right now:** Identical reasoning to `AX_Hyperelliptic_oddEquiv`: the unified type `Hyperelliptic H` is itself an `axiom` (`Hyperelliptic.lean:59`) because the natural `dite`-based real `def` trips Lean's typeclass resolution. The two parity homeomorphisms are axiomatized as the *pin* that fixes the intended content of the unified type (`Hyperelliptic.lean:50-58`). The even branch target is real today: `HyperellipticEven H h := HyperellipticEvenProj H` (`Hyperelliptic.lean:24-25`) with all topological instances already discharged (`Hyperelliptic.lean:27-48`).

**Proof recipe**

Mirror of `AX_Hyperelliptic_oddEquiv.md`, with the parity hypothesis flipped.

1. Discharge `Hyperelliptic` first (`Hyperelliptic.md`, effort 5). Under the recommended parity-dispatched encoding
   ```lean
   def Hyperelliptic (H : HyperellipticData) : Type :=
     if h : Odd H.f.natDegree then HyperellipticOdd H h
     else HyperellipticEven H h
   ```
   the even branch satisfies `Hyperelliptic H = HyperellipticEven H h` definitionally (after `dif_neg h`).
2. Discharge as `Homeomorph.refl`:
   ```lean
   theorem AX_Hyperelliptic_evenEquiv
       (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
       Hyperelliptic H ≃ₜ HyperellipticEven H h := by
     unfold Hyperelliptic
     rw [dif_neg h]
     exact Homeomorph.refl _
   ```
   The required `TopologicalSpace (HyperellipticEven H h)` is the existing instance at `Hyperelliptic.lean:27-29` (which itself unfolds to `HyperellipticEvenProj H`'s instance).
3. If `unfold; rw` fails for elaboration reasons, fall back to `Equiv.cast` through a manual proof of the definitional equality, as in step 3 of the odd recipe.
4. Replace `axiom AX_Hyperelliptic_evenEquiv` (lines 96–100) with `theorem AX_Hyperelliptic_evenEquiv` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean`. Downstream consumers (the five `instX` recipes, `instChartedSpace`/`instIsManifold` recipes via parity dispatch, and the `genus_Hyperelliptic_eq` chain) are unaffected.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — replace `axiom AX_Hyperelliptic_evenEquiv` at lines 96–100 with a `theorem` whose body is `Homeomorph.refl _` (after unfolding `Hyperelliptic` and reducing `dif_neg h`).

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` (`Hyperelliptic.lean:109`) no longer lists `AX_Hyperelliptic_evenEquiv`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `Hyperelliptic` cannot land as the parity-dispatched `def` (typeclass-on-`dite` issue re-triggers), this recipe is blocked at step 1; escalate to the `Hyperelliptic.md` recipe's `Sum`-encoded fallback and rewrite this discharge as the canonical injection-into-`inr` homeomorphism.
- If a future refactor changes `HyperellipticEven H h := HyperellipticEvenProj H` to a fresh quotient (e.g. dropping the abbreviation in favor of a direct wrapper), revisit step 2 — the `Homeomorph.refl` becomes a non-trivial homeomorphism through that wrapper.
- If `Hyperelliptic` adds an explicit parity argument, this homeomorphism becomes `rfl` directly; trivial but downstream signatures may need updating.
