# Gemini 3.1 Pro critique — `LineBundle-ofDivisor`

**Model:** gemini-3.1-pro-preview
**Duration:** 47.3s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **revise**

---

Here is a rigorous review of your axiom-discharge plan.

1. **Route classification**: `mathlib-now` is correct, but *only* if you follow Track L1. Track L2 is a mathematical dead-end.
2. **Effort**: 1 is perfectly calibrated for Track L1. 
3. **Proof recipe**: Your Track L2 contains a **catastrophic mathematical error**. You are conflating a line bundle $\mathcal{O}(D)$ with its space of global sections $H^0(X, \mathcal{O}(D))$. The project's axioms already define `H0 L` as a separate object; defining `LineBundle D` as its sections makes no sense. 
   Even worse, you claim in Track L2 that Riemann-Roch guarantees a meromorphic function $f_D$ with $\mathrm{div}(f_D) = -D$ for an arbitrary divisor $D$. This means $D = \mathrm{div}(1/f_D)$, which asserts that *every divisor is principal*. If every divisor is principal, the divisor class group is zero, the Picard group is trivial, and the Jacobian of any Riemann surface is a single point! You are proposing a proof recipe that annihilates the very object this project is built to study.
4. **Textbook citations**: Forster is the correct reference for the relationship between divisors and line bundles, but he certainly does not claim every divisor is principal. Your commentary under the citation completely misses the mark.
5. **What's missing or wrong**:
   - The fundamental difference between a line bundle and its module of global sections.
   - The false assumption that general divisors admit a function with exact poles/zeros to cancel them out.
   - You must completely discard Track L2. The architecture of this project explicitly uses `LineBundle D` as a phantom type / tag to pass the divisor $D$ into the `H0` and `H1` axioms. Track L1 (`LineBundle D := PUnit` and `LineBundle.ofDivisor D := PUnit.unit`) is the only architecturally correct and mathematically safe way to discharge this axiom without building the full machinery of locally free sheaves or invertible sheaves (which would be effort-10, not effort-1). 
6. **Recommendation**: Revise. Strip out every mention of Track L2 and unconditionally commit to the `PUnit` phantom-type implementation.

VERDICT: revise — Delete the mathematically disastrous Track L2 (which implies all divisors are principal and the Jacobian is trivial) and commit exclusively to the PUnit phantom-type track.
