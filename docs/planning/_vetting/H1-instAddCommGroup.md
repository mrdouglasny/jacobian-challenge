# Gemini 3.1 Pro critique — `H1-instAddCommGroup`

**Model:** gemini-3.1-pro-preview
**Duration:** 28.5s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed discharge plan for `H1.instAddCommGroup`.

1. **Route classification**: **Incorrect.** You classified this as `mathlib-now`, but explicitly state it is blocked by `H1` (an effort 9 `needs-infra` task). You cannot discharge an instance axiom "now" when the base type it applies to remains an opaque axiom. The correct classification is `needs-infra` (or `provable-from-other-axioms`), as this is purely a companion administrative task that must be bundled directly into the PR that defines `H1`.

2. **Effort**: The estimate of 1 is calibrated for the administrative boilerplate, but heavily masks the reality: the actual work is entirely deferred to the `H1` infra task. As long as it is understood that this effort 1 is just the typing of `:= inferInstance` *after* the effort 9 task is done, it is acceptable. 

3. **Proof recipe**: The logical structure of the recipe (wait for `H1` to become a `def` built as a quotient of modules, then apply `inferInstance`) is standard and correct. However, it completely fabricates its Mathlib claims. It states: *"In the Mathlib abstract analog, `Sheaf.H F 1` lives in `AddCommGrpCat` by construction as `Ext¹` (`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic:17–24`)."*
**This is a hallucination.** Mathlib v4.30 does *not* have a file `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. General sheaf cohomology as the derived functors of the global sections functor (`Sheaf.H`) is not yet in Mathlib. Because Mathlib lacks this, the `H1` definition will likely have to be a bespoke Čech cohomology construction natively returning an `AddCommGroup` via `QuotientAddGroup`.

4. **Textbook citations**: The reference to Forster Ch. II §13 for the Čech complex vector space structure is accurate and appropriate. 

5. **What's missing or wrong**:
   - **Hallucinated Mathlib API**: As noted above, `Mathlib.CategoryTheory.Sites.SheafCohomology` does not exist. You cannot rely on `Sheaf.H F 1` or Category Theory derived functors for this instance because they aren't there. 
   - **Route contradiction**: Claiming `mathlib-now` for something blocked by a major infrastructure overhaul is poor project management. Instances on opaque types cannot be filled with `inferInstance` until the type is un-opaqued.

6. **Recommendation**: Revise. Change the route to `needs-infra` (to be bundled with the `H1` PR), strip out the hallucinated references to Mathlib's non-existent `Sheaf.H`, and explicitly state that the instance will come from `QuotientAddGroup` applied to the bespoke Čech cocycle/coboundary construction.

VERDICT: revise — Change the route to `needs-infra` (this must be bundled with the definition of `H1`), and remove the hallucinated Mathlib reference `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (which does not exist in Mathlib v4.30).
