# Gemini 3.1 Pro critique — `H0-instModule`

**Model:** gemini-3.1-pro-preview
**Duration:** 39.9s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **revise**

---

Here is a rigorous review of the proposed discharge plan for `H0.instModule`.

1. **Route classification**: `mathlib-now` is technically accurate for this specific axiom *only* because it defers all actual work to the `H0` and `LineBundle` definitions, which themselves are deeply `needs-infra`. Assuming the prerequisites are done correctly, this instance is trivial. 
2. **Effort 1..10**: 1 is accurate for typing `inferInstance`, though effectively the effort should be 0 since this axiom must be deleted and replaced with an inline instance in the exact same PR that defines `H0`.
3. **Proof recipe**: The plan correctly identifies that this is just a dependent instance propagation, but it has a massive conceptual overkill. It kicks the can to `H0` and `LineBundle` (which is unavoidable for instance axioms), but proposes deriving the module structure of `H0` via `Sheaf.H F 0` and the `Ext`-group construction from `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. This is mathematically backwards and a Lean footgun. The 0-th cohomology of a sheaf $F$ should simply be evaluated as `F.val.obj (op ⊤)`. If the sheaf is valued in `ModuleCat ℂ`, the `Module ℂ` instance on the global sections is definitionally free and requires zero derived functor or `Ext` machinery.
4. **Textbook citations**: Forster Ch. II is a fine reference for the math, but irrelevant for Lean's typeclass synthesis of global sections. 
5. **What's missing or wrong**: 
   - **Overcomplicating `H0`**: Do not use `Ext` or `Sheaf.H` to define `H0`. It should be `(L.sheaf).val.obj (op ⊤)`. Leave `Sheaf.H` and the `Ext` machinery strictly for `H1`. 
   - **Missing constraint on `LineBundle`**: The "Risk / escalation triggers" section correctly identifies that `LineBundle` might only expose an `AddCommGroup`. This shouldn't be a mere risk; it must be a strict, non-negotiable requirement passed to the `LineBundle` plan: `LineBundle` *must* be constructed as a `Sheaf (ModuleCat ℂ) X` (or an `O_X`-module if the structure sheaf is developed), not just a sheaf of abelian groups. If it isn't, this plan doesn't just fail; the entire complex geometry setup is wrong.
   - **PR Isolation**: These instance axioms (`H0.instAddCommGroup`, `H0.instModule`) should not be discharged in separate files or separate PRs. They must be bundled into the exact same PR that turns `H0` into a `def`. 

6. **Recommendation**: Revise. Remove the `Ext`/`Sheaf.H` nonsense for `H0`, mandate that `LineBundle` is defined as a sheaf valued in `ModuleCat ℂ`, and explicitly state that this instance will be provided by `F.val.obj (op ⊤)`.

VERDICT: revise — The plan correctly relies on typeclass inference but overcomplicates the Mathlib realization by invoking `Ext`-groups for `H0` instead of simple evaluation `F.val.obj (op ⊤)` in `ModuleCat ℂ`.
