# TAIL_BLOCKER — residual inputs of the Laurent-tail duality tower

Status ledger for the tail lane (branch `feat/tail-duality-tower`; rungs per
`docs/planning/KIROV_ROUTE_IDEAS.md` items 3–4 — ideas credited to Kirov's tree,
implementations ours).  Updated 2026-06-11.

## What is PROVEN (standard-3, no hypotheses beyond the port's own theorems)

| Rung | File | Content |
|------|------|---------|
| 1 | `TailFrame.lean` | Laurent-tail pairing frame: `tailCoeff`, kernel law, single-monomial witness, residue reading, window tail space, `tailPairing`. |
| 2 | `TailRegularity.lean` | **Miranda VI.3.6 unconditional**: gap-induction engine; coefficient + pair-frame pole-bound regularity; both in the exact `lSysInclMono` shape of the §17.7/§17.9 chain (`tailRegularity_lSysInclMono`, `tailRegularitySlot_lSysInclMono`). No cover isolation, no integral. |
| 4 | `TailUnwind.lean` | The §17.9 chain **re-pointed**: `unwindRegularity_of_cechTailComparison` and `pairing_surjective_of_cechTailComparison` — `UnwindRegularity` is no longer a chain input; its geometric heart is rung 2. |
| 3 (step 1) | `CechH1CupKill.lean` | **Cup-kill proven**: `exists_effective_h1Dim_eq_zero_forall_ge` — an effective `A₀` with `h¹(𝒪_A) = 0` for every `A ≥ A₀` (pigeonhole on `cup` + germ-inverse factorization + `h1InclMono_surjective`). |
| 3 (steps 2–3) | `TailGenusTarget.lean` | The two-RR subtraction executed: `h1Dim_zero_eq_kirovGenus_of_tailRR` (uniform `h¹(𝒪) = g`), the `hga` shape at `g = 0`, and the canonical-cover Layer-3 flip target — all conditional on `TailRiemannRoch X` ONLY. |

## Residual input 1 — `TailRiemannRoch X` (rung 3's single remaining hypothesis)

```
∀ A ≥ 0, deg A > 2·kirovGenus X − 2 → (lDim A : ℤ) = deg A + 1 − kirovGenus X
```

Large-degree Riemann–Roch in the junk-free linear-system dimension.  This is the OUTPUT of
the item-3 tail tower (Miranda Ch. VI; Kirov actuals ≈ 4.4k LoC):

1. **Global truncated-tail spaces** `𝒯[D](X)` (multi-point generalization of rung 1's
   one-point `tailWindow`; finite-dimensional, `dim = deg` bookkeeping).
2. **Tail `H¹`**: `H¹_tail(D) := coker(α_D : ℳ(X) → 𝒯[D](X))`, tail RR-I
   `l(D) − h¹_tail(D) = deg D + 1 − g_tail` by Finsupp dimension counting.
3. **Tail Serre duality** `h¹_tail(D) = l(K − D)` (rung 2 = the VI.3.6 half; the
   surjectivity half = recovery + growth pigeonhole over RR-I, the shapes of our proven
   abstract `serre_surjectivity_dim_core`).
4. **`g_tail = kirovGenus X`**: pair frame `K = div ω₀` via `CanonicalFormIso`
   (`Ω(X) ≅ L(K)`, in the port) + the unconditional pair-frame residue theorem
   (`∑Res = 0`, the Stokes-atom tower — the one genuinely analytic ingredient,
   Kirov: `ResidueTheoremStokes`, seeded from Wallace's planar Green's theorem).

Estimated 2–4 weeks (KIROV_ROUTE_IDEAS item 3 verdict).  NOT faked here: rung 3's
deliverables are honestly conditional on this one named hypothesis.

## Residual input 2 — `CechTailComparison` (rung 4's restated chain input)

```
G.pairing E (mk fE) = lam ∘ₗ h1InclMono hED → slot tail pairings of fE vanish on [E b, D b)
```

The Čech↔tail evaluation dictionary for the concrete fine-sheaf `GlobalResidue`: each gap
monomial tail is realized by a one-point Čech test cocycle that is a coboundary at level `D`
(cochain side: skyscraper `coneB0`, available), so the factored functional kills it; what
remains is evaluating `res(cup fE · testCocycle) = tailPairingSlot …` — proven at ISOLATED
marked points (`resCocycle_cup_testCocycle_ne_zero`, `SerreUnwindDetect.lean`), open in the
multi-chart smeared-pole case (`docs/planning/UNWIND_BLOCKER.md` walls live entirely inside
this dictionary now; the chain around it is theorem).

**Honest strength note**: `CechTailComparison` is not literally weaker than
`UnwindRegularity` — it is a different factorization in which the geometric regularity
content (Miranda VI.3.6) has been proven and subtracted out.  On the Miranda route the chain
is instead re-pointed at the tail pairing itself, where the comparison is definitional; the
Čech-side comparison only matters if one insists on the concrete Čech `GlobalResidue`.

## Keystone assembly-readiness (as of this commit)

The keystone `exists_serreDualityData` analytic inputs are NOT yet all theorems.  Status:
- §17.7 regularity (was `UnwindRegularity`): **theorem** in the tail frame (rung 2);
  Čech-side concrete discharge still gated by `CechTailComparison` (residual input 2).
- `hga` / `h¹(𝒪) = g`: conditional on `TailRiemannRoch X` (residual input 1).
- The R-lane interface (`hsep`/`SlotExactK`/`CupMLWitnessR`/`ExactOrderWitness`): proven
  (R-lane capstone `exists_separating_cousinResidueData`).

## Update 2026-06-11 (branch `feat/tail-riemann-roch`)

Residual input 1 (`TailRiemannRoch X`) has been **decomposed and mostly discharged** by the
item-3 tower build (T1–T6, `TailCoeffFull` / `TailSpaceGlobal` / `TailRR1` / `TailSerre`):
global tail spaces, tail `H¹` finiteness, and **tail RR-I are now unconditional theorems**;
tail Serre duality's injectivity half is proven; `TailRiemannRoch X` itself is a theorem
conditional on exactly (i) `Nonempty (TailPairFrame X)` — slots + the pair-frame residue
theorem `∑Res(F·ω₀) = 0`, the one analytic atom — and (ii) `PairingSurjective` (Miranda
VI.3.10 recovery + pigeonhole).  See `docs/planning/TAILRR_BLOCKER.md`.
