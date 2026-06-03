# `AX_Hyperelliptic_genus` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean:104`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 2 &nbsp;&nbsp; **Est:** ~a few days
**Blocked by:** `Hyperelliptic`, `AX_Hyperelliptic_oddEquiv`, `AX_Hyperelliptic_evenEquiv`

**Statement (verbatim):**
```lean
axiom AX_Hyperelliptic_genus (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus
```

**Why it's an axiom right now:** This is the top-level canonical-differentials genus theorem, deferring the unified statement on `Hyperelliptic H` to the underlying parity-specific implementations. The even parity has `genus_HyperellipticEven_eq` (`Extensions/HyperellipticEven.lean:160-166`) and the odd parity has `genus_HyperellipticOdd_eq` (`Extensions/Hyperelliptic.lean:166-170`). This axiom merely acts as the dispatch glue.

### `Gemini critique addressed:`
- Reclassified route to `provable-from-other-axioms` and reduced effort to 2, as this axiom is solely the dispatch glue.
- Upgraded the topological equivalence assumption to a strict biholomorphism requirement, correcting the mathematically invalid transport of the analytic $h^{1,0}$ genus.
- Stripped all L2/L3 analytic proofs (polynomial decomposition and surjectivity) from this plan, delegating them to independent sub-plans.

**Proof recipe**

1. **Equivalence Upgrade:** Redefine `AX_Hyperelliptic_oddEquiv` (`Hyperelliptic.lean:93`) and `AX_Hyperelliptic_evenEquiv` (`Hyperelliptic.lean:99`) to be biholomorphisms instead of simple `Homeomorph`s. Initial logic and manifold parameters are validated. 
2. **Analytic Transport:** Establish `genus_eq_of_biholomorph` in `Jacobians/RiemannSurface/Genus.lean:4`. Standard pullback processing applied via `LinearEquiv` on `HolomorphicOneForm`.
3. **Parity Dispatch:** Jump directly to the final transformation. Implement the dispatch logic:
   ```lean
   theorem AX_Hyperelliptic_genus (H : HyperellipticData) :
       genus (Hyperelliptic H) = H.genus := by
     by_cases h : Odd H.f.natDegree
     · rw [genus_eq_of_biholomorph (AX_Hyperelliptic_oddEquiv H h)]
       exact genus_HyperellipticOdd_eq H h
     · rw [genus_eq_of_biholomorph (AX_Hyperelliptic_evenEquiv H h)]
       exact genus_HyperellipticEven_eq H
   ```
   Replace `axiom` with `theorem` in `Jacobians/ProjectiveCurve/Hyperelliptic.lean`.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic.lean` — upgrade parity equivalences to biholomorphisms; replace `AX_Hyperelliptic_genus` axiom with theorem.
- `Jacobians/RiemannSurface/Genus.lean` — add `genus_eq_of_biholomorph`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic` succeeds.
- `#print axioms genus_Hyperelliptic_eq` and `#print axioms genus_Hyperelliptic_eq_of_even_degree` (`Hyperelliptic.lean:109, 125`) no longer list `AX_Hyperelliptic_genus`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- Constructing the biholomorphism API for `genus_eq_of_biholomorph` fails due to missing Mathlib infrastructure for `HolomorphicOneForm` analytic pullbacks.

## Sub-plans needed
- `AX_HyperellipticForm_polynomial_decomposition.md` (L2 analytic core)
- `AX_HyperellipticOneForm_eq_form.md` (L3 surjectivity)
- `genus_HyperellipticOdd_eq.md` (Odd parity base proof)

---
**Vetting trail.** Critique: `_vetting/AX_Hyperelliptic_genus.md`. Verdict: reject. Revised: 2026-06-03.