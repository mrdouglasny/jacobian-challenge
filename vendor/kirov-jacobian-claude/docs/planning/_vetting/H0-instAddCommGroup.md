# Gemini 3.1 Pro critique — `H0-instAddCommGroup`

**Model:** gemini-3.1-pro-preview
**Duration:** 35.3s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **revise**

---

Here is a critical review of the proposed discharge plan for `H0.instAddCommGroup`.

1. **Route classification**: **Incorrect**. It should be `needs-infra`. The `mathlib-now` route implies the pieces exist in Mathlib right now to close the sorry. However, Lean's typeclass synthesis cannot invent an `AddCommGroup` structure for an undefined, opaque `axiom` type like `H0`. This task is entirely bottlenecked on building the project-specific sheaf/sections infrastructure for `H0` and `LineBundle`. 
2. **Effort 1..10**: 1 is well-calibrated, but this is only true *conditionally*—the `H0` infrastructure PR must do 100% of the actual mathematical heavy lifting.
3. **Proof recipe**: The recipe literally kicks the can to `H0.md`, which is the only logically sound approach here. The sections of a sheaf of modules naturally form a module. It also correctly recognizes that this should be batched with the `Module` and `H1` instances. However, because it delegates the entire problem, it proves that this is an infra task, not a standalone Mathlib search. 
4. **Textbook citations**: N/A, which is perfectly appropriate for standard structural boilerplate.
5. **What's missing or wrong**:
   - **False risk assessment**: Under "Risk / escalation triggers", the concern about `ModuleCat ℂ` is misguided. If the eventual API exposes `H0 L` as a `ModuleCat ℂ`, Mathlib's standard setup provides a coercion to `Type` (via `Bundled`) which automatically synthesizes the `AddCommGroup` and `Module` instances on the carrier type. `inferInstance` will still work flawlessly. It does not become a "refl-coercion" (which isn't a real Lean concept anyway).
   - **Architectural separation**: This task should not exist as a standalone ticket or PR. A PR that introduces `def H0` without establishing its fundamental algebraic instances is bad practice and mathematically incomplete. This entire plan should be folded directly into the `H0.md` recipe as an acceptance criterion.
6. **Recommendation**: Revise. Update the route to `needs-infra`, delete the incorrect `ModuleCat` risk warning, and explicitly mandate that this instance must be provided in the exact same PR that defines `H0`.

VERDICT: revise — Change the route to needs-infra and remove the incorrect ModuleCat coercion risk, as typeclass inference handles bundled category coercions automatically.
