# S5 statement layer — Forster §17.7, the `unwind` field (Lane L, step S5)

*2026-06-10, branch `feat/keystone-l-unwind`. For the orchestrator's DT vet BEFORE downstream
reliance. Target: the `unwind` field of `SurjectivityInputs`
(`KirovDolbeault/Dolbeault/SerreSurjectivitySkeleton.lean:95-99`), the LAST unproven field.
Implementation: `KirovDolbeault/Dolbeault/SerreUnwind.lean`.*

---

## 1. Interface audit result (the prompt's "compatibility law" check)

`SerreResidueRealization 𝔘 K` has exactly TWO fields (`pairing`, `witness`) and **no
cross-divisor law whatsoever** — at the abstract-interface level the divisors' pairings
`pairing D` and `pairing (D−nP)` are completely independent data, so the §17.7 unwind is
**not provable against the abstract interface** (a counter-model assigns unrelated
nondegenerate pairings at each divisor).

However, the realization the R-lane actually supplies is the **assembled** one:
`GlobalResidue.toSerreResidueRealization` with `pairing D = res ∘ cup D K`
(`SerreResidueRealizationAssembly.lean:93-114`), and at THAT level the two *formal* halves of
17.7 become **theorems** (cup is literally germ multiplication, so all multiplicativity is
cochain-level `mul_assoc` + the landed `globalGerm_mul_inv`):

* **restriction compatibility** — `pairing E (incl u) = pairing D u ∘ H¹-inclusion` for
  `E ≤ D` (cochain-identical: the inclusion is the identity on cochains);
* **cancellation** — `λ ∘ (ψ·) = ι(φ) ∘ (ψ·) ⟹ λ = ι(φ)` from surjectivity of mult-by-ψ
  (the landed `psiMul_surjective` / `h1InclMono_surjective`).

What is **NOT** derivable from `GlobalResidue` (= `res : cechH1 K →ₗ ℂ` + the residue-1
`nondegenerate` witness) is the *geometric* heart of 17.7, the **pole-bound regularity**
step. Per the no-unilateral-interface-extension rule, that is landed as a NAMED hypothesis
(`Prop`-valued def, no axiom, no interface change) — see `docs/planning/S5_BLOCKER.md` for
the extension decision it queues.

## 2. Why the naive order arithmetic fails (the honest derivation)

With `D' := D − nP`: `ψ ∈ L(nP)` gives only `ord ψ ≥ −nP`; ψ may carry **extra zeros** away
from `P`. So for `w ∈ L(K−D')`:

```
ord(w/ψ) = ord w − ord ψ ≥ (D' − K) − div ψ      (exact: ord ψ = div ψ, ψ germ-nonzero)
```

i.e. `w/ψ ∈ L(K − E)` for `E := D' − div ψ` — and `E ≤ D` (since `div ψ ≥ −nP`), but
`L(K−E) ⊋ L(K−D)` whenever ψ has zeros outside the allowance. The membership
`w/ψ ∈ L(K−D)` is **false as pure order arithmetic**; it is exactly Forster's Lemma 17.7:

> if `λ ∘ i_{E→D} = ι_E(v)` on `H¹(𝒪_E)` for `E ≤ D`, `v ∈ L(K−E)`, then `v ∈ L(K−D)`
> (and hence `λ = ι_D(v)`).

Forster proves this by an explicit one-point cocycle: if `v ∉ L(K−D)`, pick `x₀` where the
bound fails, build the two-set-cover class `η` of a local `z^{−1−ord_{x₀}v}` — it dies in
`H¹(𝒪_D)` (its pole is within the `D`-allowance) yet `Res(v·η) = 1 ≠ 0`, contradicting
`ι_E(v)(η) = λ(i(η)) = 0`. This consumes the **value of `res` on an explicit local Laurent
cocycle** (note `v·η` has a *simple* pole — exactly the R-lane's R6 simple-pole ML-tie), a
locality datum the `GlobalResidue` fields do not carry.

## 3. The landed statements (verbatim from `SerreUnwind.lean`)

### 3a. The isolated missing law (Prop def, hypothesis-parametric — NOT an axiom)

```lean
/-- **[ISOLATED INPUT — Forster §17.7 pole-bound regularity].** ... -/
def GlobalResidue.UnwindRegularity (G : GlobalResidue 𝔘 K) (D : Divisor X) : Prop :=
  ∀ (E : Divisor X) (hED : ∀ x, E x ≤ D x) (v : lSysModule (X := X) (K - E))
    (lam : Module.Dual ℂ (𝔘.cechH1 D)),
    G.pairing E v = lam ∘ₗ 𝔘.h1InclMono hED →
    ∃ u : lSysModule (X := X) (K - D),
      lSysInclMono (divisor_sub_le_sub_left K hED) u = v
```

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), Lemma 17.7. Discharge path:
two-set one-point cocycle + the R-lane's concrete `res` (R6 simple-pole tie + R8-style
witness machinery); see S5_BLOCKER.md.

### 3b. The unwind theorem (Forster §17.7 reduced to the law — sorry-free)

```lean
theorem GlobalResidue.unwind (G : GlobalResidue 𝔘 K) (hR : 𝔘.LocallyRealizable)
    {D : Divisor X} (P : X) (hreg : G.UnwindRegularity D)
    (lam : Module.Dual ℂ (𝔘.cechH1 D)) (n : ℕ)
    (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ)))
    (w : lSysModule (X := X) (K - (D - Finsupp.single P (n : ℤ))))
    (hψ : ψ ≠ 0)
    (hmatch : 𝔘.psiAct D P lam n ψ = G.pairing (D - Finsupp.single P (n : ℤ)) w) :
    lam ∈ Set.range (G.pairing D)
```

Proof architecture (all PROVEN, no new assumptions beyond `hreg`):

1. **Division (honest version):** representative `ψ₀` of ψ is germ-nonzero everywhere
   (identity theorem, `orderW_ne_top_of_exists`); set `E := (D−nP) − div ψ₀ ≤ D` and
   `φ := w·ψ₀⁻¹ ∈ L(K−E)` (`orderW_mul` + `orderW_inv` + `coe_div_eq_orderW`; new
   `Mul (MeromorphicFunction X)` instance + `mul_mem_linearSystem`).
2. **Shift iso:** `ψ· : H¹(𝒪_{D−nP}) → H¹(𝒪_E)` is onto (germ inverse `ψ₀⁻¹`,
   `globalGerm_mul_inv` — no `hR` needed for this step), and
   `i_{E→D} ∘ (ψ·)_{D'→E} = psiMul ψ` (cochain-identical).
3. **Functional identity:** for every `η ∈ H¹(𝒪_E)`, writing `η = ψ·ξ`:
   `pairing E φ (η) = res(φ·ψ·ξ) = res(w·ξ) = (ψλ)(ξ) = λ(i_{E→D} η)`, i.e.
   `G.pairing E φ = lam ∘ₗ h1InclMono` (cup multiplicativity `cupH1_cupH1` +
   germ-level `cupH1_congr_germ` since `φψ = w` only *as germs*).
4. **Regularity (the law):** `hreg` upgrades `φ` to `u ∈ L(K−D)` with `incl u = φ`.
5. **Cancellation:** `pairing D u ∘ incl = pairing E φ = lam ∘ incl` and `incl = h1InclMono`
   is surjective on `H¹` (iterated skyscraper `h1InclMono_surjective`, uses `hR`), so
   `pairing D u = lam`. ∎

### 3c. The assembly gate — full `SurjectivityInputs` now inhabits

```lean
example {𝔘 : FiniteCover X} {K : Divisor X} (G : GlobalResidue 𝔘 K)
    (D : Divisor X) (P : X) (hR : 𝔘.LocallyRealizable) (hreg : G.UnwindRegularity D) :
    SurjectivityInputs G.toSerreResidueRealization D where
  P := P
  psiAct := fun lam n => 𝔘.psiAct D P lam n
  psiAct_injective := fun lam hlam n => 𝔘.psiAct_injective hR D P lam hlam n
  unwind := fun lam _hlam n ψ w hψ0 hmatch => G.unwind hR P hreg lam n ψ w hψ0 hmatch
```

ALL three geometric fields of `SurjectivityInputs` are now supplied; combined with the landed
S7 skeleton this yields `Function.Surjective (G.pairing D)` (§17.9, the HARD half) **modulo
exactly two named inputs**: `G : GlobalResidue 𝔘 K` (Lane R) and
`hreg : G.UnwindRegularity D` (this file's isolated law; discharge alongside R6/R8).

## 4. Vet questions for DT (per axiom-vetting protocol, applied to the Prop law)

`UnwindRegularity` is a hypothesis, not an axiom — but it will eventually be discharged or
field-ified, so vet now: (a) typing as above; (b) **strength**: is the `∃ u, incl u = v`
conclusion (junk-free germ-class level) the right transcription of Forster's "`ω ∈ L(K−D)`"?
(c) **non-vacuity/satisfiability**: it HOLDS for the true residue realization (Forster 17.7's
proof) and FAILS for adversarial abstract `res` — i.e. it is a genuine restriction, neither
trivially true nor inconsistent with the intended model; (d) the `lam`-quantified
factorization hypothesis form vs the equivalent annihilator form
(`ι_E(v) ⊥ ker(incl)`) — equivalent given `h1InclMono_surjective` (hR), factorization form
chosen to match Forster's `i^*λ = ι_E(v)` verbatim.
