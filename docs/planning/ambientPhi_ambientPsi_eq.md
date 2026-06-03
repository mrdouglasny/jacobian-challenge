# `ambientPhi_ambientPsi_eq` — discharge recipe

**Location:** `Jacobians/Vendor/Kirov/HolomorphicForms.lean:340`
**Route:** mathlib-now (discharge by deletion + downstream cleanup; the axiom is a vendored Kirov duplicate of `AX_pushforward_pullback` which lives in the main tree) &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** < 1 hour, ~10 LOC (just delete it)
**Blocked by:** none

**Statement (verbatim):**
```lean
/-- **Ambient degree identity** (Forster §17 / Miranda §III.4).
The composition `ambientPhi f hf ∘ ambientPsi f hf` equals
multiplication by the degree `d`. In terms of forms: `f_* ∘ f^* = deg(f) • id`.

Mathlib has no manifold-level degree theory for proper holomorphic maps.
Real content requires a real `ContMDiff.degree` (via preimage counting
at regular values) together with a real trace/pushforward construction
for `ambientPhi`. ~500-1000 lines to formalize.

**Stated as `axiom` for handoff** (was `:= sorry` in upstream). To
discharge: prove the same statement and replace this `axiom` with a
`theorem`. See `vendor/kirov-jacobian-claude/HANDOFF.md`. -/
axiom ambientPhi_ambientPsi_eq {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (d : ℕ)
    (y : Fin gY → ℂ) :
    ambientPhi (gX := gX) (gY := gY) f hf (ambientPsi f hf y) = (d : ℕ) • y
```

**Why it's an axiom right now:** The axiom was introduced as a placeholder for the trace formula on holomorphic 1-forms. However, as currently stated, it is a mathematical falsehood and logically self-contradictory. Lean treats the free parameters `(d : ℕ)` and `(y : Fin gY → ℂ)` as universally quantified. Asserting `ambientPhi (...) = d • y` for *all* `d` forces `y = 0` (e.g., set `d = 0` and `d = 1`), making it trivially false unless `gY = 0`. Moreover, the matrix transpose of the pullback in an unpolarized, arbitrary coordinate basis does not equate to the geometric trace. Given that the codebase contains exactly zero calls to this axiom, it is dead code that should be excised entirely.

**Proof recipe**

1. **Delete the axiom.** Remove the entirety of `axiom ambientPhi_ambientPsi_eq` and its docstring from `Jacobians/Vendor/Kirov/HolomorphicForms.lean:340`.
2. **Verify isolated state.** Confirm via `grep -rn "ambientPhi_ambientPsi_eq" Jacobians/` that no downstream theorems implicitly relied on this axiom (the previous analysis confirmed zero usage, so this should pass silently).
3. **Clean up vendor docs.** Remove references to this required discharge from `vendor/kirov-jacobian-claude/HANDOFF.md` to prevent future confusion.

**Files touched**
- `Jacobians/Vendor/Kirov/HolomorphicForms.lean` — delete the `axiom ambientPhi_ambientPsi_eq` block (lines 333-344).
- `vendor/kirov-jacobian-claude/HANDOFF.md` — strike the entry for axiom #2 (lines 71–124).

**Acceptance**
- `lake build Jacobians.Vendor.Kirov.HolomorphicForms` succeeds.
- `#print axioms ambientPhi_id` (`Jacobians/Vendor/Kirov/HolomorphicForms.lean:347`) and `#print axioms ambientPhi_comp` (`HolomorphicForms.lean:359`) remain stable.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `lake build` reveals an unexpected downstream dependency that was somehow obfuscated from the textual `grep`, stop and escalate. Any proof relying on a logically false axiom (one that can prove `y = 0` for any `y`) is fundamentally mathematically corrupt and must be completely rewritten; it cannot be salvaged by simple refactoring.

## Gemini critique addressed:
- **Route and Effort changed:** Reclassified from `genuine-textbook` (effort 8) to `needs-deletion` (effort 1) since the axiom is mathematically irredeemable, logically false, and completely unused.
- **Removed the massive implementation plan:** The 6-week plan involving degree theory and geometric trace maps was completely removed. Fixing an unused, broken axiom in a vendor namespace is a misallocation of effort.
- **Corrected logical misunderstanding:** Acknowledged that an axiom with a universally quantified free variable `d : ℕ` that fails for some `d` is unconditionally false, not "vacuous."
- **Corrected geometric misunderstanding:** Noted that the matrix transpose of the pullback in an arbitrary basis does not equal the geometric trace, avoiding the trap of trying to equate them.
- **Removed hallucinated mathlib references:** Removed dependencies on non-existent theorems like `Complex.analyticAt_of_differentiable_on_punctured`.

---
**Vetting trail.** Critique: `_vetting/ambientPhi_ambientPsi_eq.md`. Verdict: reject. Revised: 2026-06-03.

**Cross-plan patch (2026-06-03):** Standardised manifold-model-space notation to `𝓘(ℂ, ℂ)` (Mathlib's `modelWithCornersSelf ℂ ℂ`); the single-arg alias `𝓘(ℂ)` caused typeclass-unification failures between generic and concrete plans.
