# Gemini 3.1 Pro critique — `PrincipalDivisors`

**Model:** gemini-3.1-pro-preview
**Duration:** 80.5s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **reject**

---

Here is the referee critique of the proposed axiom-discharge plan for `PrincipalDivisors`:

### 1. Route classification
The plan proposes **`needs-infra`**, which is half-correct. Defining the subgroup and meromorphic function bundle is indeed infrastructure. However, proving that meromorphic functions on a compact Riemann surface have finitely many zeros/poles (Stage B) is a **`genuine-textbook`** endeavor (the Identity Theorem). The route for discharging *this specific axiom* should strictly be `needs-infra`, and it should avoid the textbook proof entirely.

### 2. Effort 1..10
The estimate (8, ~3–4 weeks) is **wildly miscalibrated**.
- If executed exactly as written (which requires proving the Identity Theorem on manifolds for Stage B), it is an **Effort 9+** (months of work, 1500+ LOC), because patching local analytic constancy to global constancy on manifolds is completely missing from Mathlib.
- If revised to bypass Stage B using classical logic (see below), the effort drops to an **Effort 2** (~2 days, <150 LOC). 

### 3. Proof recipe
- **FATAL GAP in Stage B:** The plan claims Mathlib's `eventually_eq_zero_or_eventually_ne_zero` provides discreteness. This is **false**. It only states that around each point, the function is *either* zero on an entire neighborhood *or* has isolated zeros. To conclude global discreteness, you mathematically must use `ConnectedSpace X` and the Identity Theorem to prove the "zero on an entire neighborhood" case is impossible for `f ≠ 0`. The plan entirely misses this load-bearing step.
- **Can-kicking opportunity missed:** You do not need to prove Stage B to discharge this axiom! Because Lean functions are total and we have classical logic, you can define `div` using `dite` (dependent if-then-else):
  ```lean
  noncomputable def MeromorphicFunction.div (f : MeromorphicFunction X) : Divisor X :=
    if h : (Function.support (fun p => (orderAt p f.toFun).toInt)).Finite
    then ∑ p ∈ h.toFinset, (orderAt p f.toFun).toInt • FreeAbelianGroup.of p
    else 0
  ```
  This immediately satisfies the typechecker for the definition and pushes the brutal finiteness proof to the theorems that actually need to evaluate `div` (e.g., Abel's Theorem).
- **Stage D Closure Hack:** Using `AddSubgroup.closure (Set.range ...)` is a smart, correct Lean trick to bypass proving that `div` is a group homomorphism right now.

### 4. Textbook citations
Forster is correct, but the plan cites Forster Thm 8.7 (discrete zeros) while completely ignoring the prerequisite **Forster Thm 8.5 (Identity Theorem)**, which is where the actual mathematical difficulty lies.

### 5. What's missing or wrong
- **The Identity Theorem is ignored:** Stage B assumes topological discreteness is immediate from local behavior. It is not. You cannot pass from local isolated zeros to a global discrete finite set without analytic continuation.
- **Over-engineering a definition:** Axiom discharge for a definition should focus solely on constructing the term. Bundling a massive finiteness proof into it violates separation of concerns and will completely stall the PR.
- **Typechecker trap in Stage C:** `FreeAbelianGroup.of p` will not typecheck if `Divisor X` is still an opaque axiom. As noted in your "Blocked by" section, `Divisor X` must be fully defined/unsealed in the codebase before `PrincipalDivisors` can be formalized.

### 6. Recommendation
**Reject.** The current plan attempts a massive, mathematically flawed proof of finiteness inside a definitional PR. Revise the plan to completely drop Stage B, use `dite` on the `Finite` predicate to define `MeromorphicFunction.div` in Stage C, and keep the `AddSubgroup.closure` trick in Stage D. This will drop the effort to 2 and securely discharge the axiom.

VERDICT: reject — The plan severely underestimates the mathematical difficulty of Stage B (missing the Identity Theorem on manifolds) and should be revised to use classical logic (`dite`) to bypass the finiteness proof entirely for the definition.
