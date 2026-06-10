# S5 BLOCKER — the residue interface lacks the Forster §17.7 pole-bound regularity law

*2026-06-10, Lane L step S5 (`feat/keystone-l-unwind`). Per the lane instruction ("if the
interface LACKS a pairing×cup compatibility law, write the precise missing statement here —
that's an interface extension decision, do not bolt it on unilaterally").*

## Audit outcome

Checked `SerreResidueRealization` (`SerreResiduePairing.lean:192-201`) and `GlobalResidue`
(`SerreResidueRealizationAssembly.lean:75-83`) plus every `pairing`-related lemma in the port:

1. **The anticipated pairing×cup *compatibility* law is NOT missing** at the level that
   matters: for the assembled realization (`pairing D = res ∘ cup D K`) restriction
   compatibility and ψ-multiplicativity are **derivable theorems** (cup = germ
   multiplication; landed in `SerreUnwind.lean` as `cupH1_cupH1`, `cupH1_h1InclMono`,
   `h1InclMono_cupH1`, `pairing_comp_h1InclMono`). The abstract `SerreResidueRealization`
   does lack any cross-divisor law, but the skeleton is parametric in `R`, so instantiating
   at `G.toSerreResidueRealization` is legitimate and requires no interface change.

2. **What IS missing — and not derivable from `GlobalResidue` — is the geometric heart of
   Forster 17.7, the pole-bound regularity:**

```lean
-- The precise missing statement (landed as a Prop def + hypothesis, NOT bolted onto the
-- interface; KirovDolbeault/Dolbeault/SerreUnwind.lean):
def GlobalResidue.UnwindRegularity (G : GlobalResidue 𝔘 K) (D : Divisor X) : Prop :=
  ∀ (E : Divisor X) (hED : ∀ x, E x ≤ D x) (v : lSysModule (X := X) (K - E))
    (lam : Module.Dual ℂ (𝔘.cechH1 D)),
    G.pairing E v = lam ∘ₗ 𝔘.h1InclMono hED →
    ∃ u : lSysModule (X := X) (K - D),
      lSysInclMono (divisor_sub_le_sub_left K hED) u = v
```

   Informally: if the level-`E` residue functional of `v ∈ L(K−E)` factors through the
   (surjective) inclusion `H¹(𝒪_E) → H¹(𝒪_D)` for `E ≤ D`, then `v` already lies in the
   smaller system `L(K−D)`. Forster 17.7, p. 137.

## Why it cannot be proven from the current fields

`GlobalResidue` carries only `res : cechH1 K →ₗ ℂ` and the residue-1 `nondegenerate`
witness. Forster's proof of 17.7 evaluates `Res` on an **explicit one-point two-set-cover
cocycle** (local `z^{−1−ord v}`; the product `v·η` has a *simple* pole) — a locality datum
absent from the fields. An adversarial `res` satisfying `nondegenerate` can violate the
regularity (the witness controls existence of SOME class with pairing 1, not the value of
`res` on prescribed local classes); a dimension-count derivation would need
`l(K−E) − l(K−D) = h¹(E) − h¹(D)`, which IS Serre duality — circular.

## Decision queued for owner / upstream (rkirov)

Options, in our recommended order:

1. **Discharge it for the concrete fine-sheaf `res` (no interface change at all).** The
   R-lane's R6 (simple-pole ML-tie `Res([δμ]) = Res_a(μ)` via `DbarDisk.cauchyPompeiu`) plus
   an S4-style two-set one-point cocycle construction is exactly the needed input; then
   `UnwindRegularity` becomes a theorem about the R-lane's `GlobalResidue` instance and the
   hypothesis is supplied at assembly time (Lane A). **No decision needed beyond scheduling**
   — this keeps `GlobalResidue` frozen.
2. **Field-ify:** add `regularity : ∀ D, UnwindRegularity (D := D) …` (or its annihilator
   form) as a third `GlobalResidue` field. Touches the shared interface ⇒ needs the
   discussion step + DT satisfiability vet (it holds for the intended `res` by Forster 17.7).
3. Strengthen with a general locality field (`res` on explicit Laurent cocycles = local
   residue), subsuming both this and S4's `nondeg` transport. Largest change; only worth it
   if S4 hits the same wall.

## What landed regardless (sorry-free, axiom-free)

`SerreUnwind.lean`: the full 17.7 reduction `GlobalResidue.unwind` (division with the honest
`E = D − nP − div ψ` order arithmetic, shift-iso, functional identity, cancellation via
`h1InclMono_surjective`), parametric in `hreg : UnwindRegularity`; plus the
`SurjectivityInputs` assembly gate. The §17.9 surjectivity of the Serre pairing is now
conditional on exactly **{`G : GlobalResidue 𝔘 K`} ∪ {`UnwindRegularity G D`}** — both on
the R-lane critical path, nothing else.
