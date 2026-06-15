# VALIDATION — convincing a mathematician the construction is correct

**Purpose.** Buzzard's challenge asks us to *formalize the Jacobian and prove it
has 24 properties*. This document is about a sharper, downstream goal: **what is
the most efficient artifact that convinces a working mathematician we have
correctly formalized a construction of the Jacobian** — and it states that
artifact as a concrete *goal to prove*, with current status.

This is not a restatement of the challenge. It is the validation target the
challenge is *evidence for*.

---

## 0. The right framing: the burden is on *statements*, not proofs

Lean's kernel already certifies the proofs. `lake build` + `#print axioms`
(sorry-aware) machine-check that every headline is sorry-free and rests only on
its declared axioms. So a mathematician who trusts the kernel has **nothing to
check about the proofs**. The entire remaining burden is the **specification
gap** — auditing *statements* to rule out the only two failure modes a green,
axiom-clean build does **not** catch:

1. **Wrong object.** `Jacobian X` compiles and carries theorems, but it is
   secretly `ℂ^g`, or a torus of the wrong dimension, or a degenerate look-alike.
   Every theorem is true *of that object*; the object just isn't the Jacobian.
2. **Vacuous statements.** A theorem is true but does not *say* what its English
   name claims — a mis-stated `genus`, a vacuous hypothesis on injectivity, the
   wrong smoothness class on the Abel–Jacobi map.

**"Most efficient validation" therefore means: the smallest set of *statements* a
mathematician must read-and-trust so that, granting the kernel checked the
proofs, both failure modes are closed.**

A corollary worth internalizing: **a long checklist is not the efficient thing to
*convince with*.** A checklist convinces by *accumulation* (rule out degeneracies
one at a time) and leaves the reader to decide whether the list is *complete
enough* — and, as established separately, the 24 do **not** categorically pin the
Jacobian, so that residual doubt never fully closes. Efficiency comes from
*categoricity*, not length.

**But the convincing-set and the *delivery-set* are not the same thing, and they
pull in opposite directions on length.** You convince with the *fewest*
statements that close the spec gap; you deliver the *most* statements that are
independently useful or independently validating. A finished formalization should
exceed the convincing-minimal — not because any *particular* list is canonical
(it isn't; *24*, and *those* 24, is Buzzard's authorship, and some members like
`genus_eq_zero_iff_homeo` are curve facts, not Jacobian API) — but for three
reasons that generalize past this challenge:

1. **Validation ≠ library.** The minimal categorical artifact *certifies*
   correctness; it does not make the object *usable*. The universal property is
   hard to apply directly — a downstream user would re-derive functoriality, the
   AJ map's properties, the genus relations each time. The "redundant" theorems
   are the worked-out **API surface** people actually cite. Redundancy that is
   wasteful for convincing is what is valuable for using.
2. **Concrete breadth cross-validates the *primitives*.** The universal property
   is faithful only *relative to its own statement being right* — it presupposes
   `genus`, the differentials, `ContMDiff`, the group law are formalized
   correctly. A single abstract statement can be perfectly correct while sitting
   atop a mis-formalized primitive that happens not to bite for *that* statement.
   Abstraction *hides* primitive-level errors; a spread of concrete consequences,
   each touching the primitives from a different angle, is what *exposes* them.
   This is redundancy-as-error-detection: the more independent concrete theorems,
   the more the definitions are pinned by triangulation.
3. **It is nearly free.** Proving the universal property *requires* Abel's
   theorem, the lattice rank, period functoriality — the content of most of the
   list is the scaffolding of the capstone proof anyway. Not exposing those
   proven lemmas as named API discards work already done.

So the general principle is **characterization (certificate) + a usable API +
enough concrete cross-checks to triangulate the primitives** — the first minimal
and categorical, the second and third deliberately broad and redundant. The 24
are one reasonable, non-canonical instantiation of "API + cross-checks." This
document is about the *convincing* set; the delivery set is properly larger.

---

## 1. The validation artifact — three parts, in order of convincing power

### Part A — the definition, read directly (does the bulk of the work)

`Jacobians/Jacobian/Construction.lean:146`

```
noncomputable abbrev Jacobian (X) [...] := H⁰(X, Ω¹)* / (period lattice)
```

A mathematician who reads this **recognizes the standard construction on sight**
— `ℂ^g / Λ` with Abel–Jacobi = integration of holomorphic 1-forms. This is the
single most efficient convincing act in the whole development, because *the
definition is the textbook object*. The reader's residual task shrinks to "are
`HolomorphicOneForm X`, the period pairing, and the lattice formalized
faithfully?" — and `genus X := finrank ℂ (HolomorphicOneForm X)`
(`RiemannSurface/Genus`) and the chart dimension `Fin (genus X) → ℂ` are right
there in the definition, so `dim = g` is **structural, not a separate theorem**.

### Part B — a curated anti-vacuity subset (3 lemmas, NOT 24)

Chosen for *degeneracy coverage* of exactly the primitives in Part A — each kills
one way the formalization could be faithful-looking but vacuous:

| Anti-degeneracy lemma | Decl | Kills the failure mode |
|---|---|---|
| `dim Jacobian = genus` (full-rank `2g` lattice) | structural (chart dim) + `finrank_loopPeriodLattice_unconditional` (`PeriodDiscretenessKirovRoute.lean:1329`) | "object collapsed / lattice degenerate" |
| Abel–Jacobi holomorphic, basepoint ↦ 0 | `Jacobian.ofCurve_contMDiff`, `Jacobian.ofCurve_self` (`Challenge.lean:133,136`) | "map mis-wired / non-holomorphic" |
| Abel–Jacobi injective for `g ≥ 1` | `Jacobian.ofCurve_inj` (`Challenge.lean:140`) | "map trivial / target is the wrong object" |

Note `genus_eq_zero_iff_homeo` is deliberately **excluded** — it is a curve-side
fact and says nothing about `J`. The subset is about `J`, not about `X`.

These make the formalized pieces *non-vacuous*. They are **necessary but not
sufficient**: dimension + injectivity + holomorphy still permit, in principle, an
isogenous abelian variety, or the right torus with a wrong complex structure.
Closing that last gap is Part C.

### Part C — the universal property (the categorical certificate)

`Jacobians/UniversalProperty.lean:93` (`structure IsJacobian`),
`:457` (`theorem ofCurve_isJacobian`)

```
IsJacobian x₀ J aj  :=  aj_holo ∧ aj_base (aj x₀ = 0) ∧ universal
  -- where `universal`: every pointed holomorphic f : X → A (A a complex torus
  -- of ANY dimension) factors uniquely through aj by a holomorphic hom J →+ A.
  -- "ComplexTorus J" is encoded by the typeclass bundle:
  --   [CompactSpace][ConnectedSpace][ChartedSpace (Fin g → ℂ)][LieAddGroup …] J
```

This is the **one statement that converts Part B's *evidence* into a *proof of
identity***. By Yoneda, an initial object of the category 𝒞_X of pointed
holomorphic maps `X → (complex torus)` is unique up to unique isomorphism — so
once `ofCurve_isJacobian` is established, anything satisfying `IsJacobian` **is**
the Jacobian, with **zero "is this enough?" residual**. It is the strongest
assurance per statement read in the entire development.

This "unique up to unique isomorphism" is now a **machine-checked theorem**, not
just Yoneda folklore: `Jacobians.isJacobian_unique` (`UniversalProperty.lean`)
proves any two objects satisfying `IsJacobian x₀` are biholomorphically,
group-isomorphically the same via mutually inverse holomorphic homs intertwining
their Abel–Jacobi maps — and it is **axiom-free** (`#print axioms` →
`propext, Classical.choice, Quot.sound`), using *none* of the 24. The corollary
`isJacobian_iso_jacobian` specializes it to the concrete `Jacobian X` (via
`ofCurve_isJacobian`, inheriting its four torus axioms).

It is not sufficient *alone* — its proof is unreadable (so it does nothing for
the *vacuity* worry; that is Part B's job), and the predicate itself needs a
small audit (is 𝒞_X the right category? — yes: compact connected complex Lie
group ⇒ complex torus, and a curve's Albanese torus is automatically an abelian
variety). But as the capstone over A + B it is what makes the validation
*categorical* rather than *accumulative*.

---

## 2. The goal to prove

**The validation artifact is complete and load-bearing exactly when
`ofCurve_isJacobian` is sorry-free AND axiom-clean (standard-3 only).**

> **G1 DONE (PR #251).** `AX_PeriodCycleBasis` is discharged from every headline
> closure — **all 24 Buzzard headlines are now standard-3**, and Parts A+B of the
> artifact are fully axiom-clean. The capstone `ofCurve_isJacobian` no longer
> carries `AX_PeriodCycleBasis` either; it is down to the **three torus axioms**.

Current status (`#print axioms Jacobians.ofCurve_isJacobian`, 2026-06-14):

```
[propext, Classical.choice, Quot.sound,
 AX_curve_generates_jacobian,
 AX_period_functoriality,
 AX_torus_self_albanese]
```

So the capstone now rests on **three project axioms**, all torus-side (Parts A+B
and every Buzzard headline are axiom-clean). The remaining bounded goal:

| Goal | Axiom to discharge | Reduces to | Status |
|---|---|---|---|
| ~~**G1**~~ | ~~`AX_PeriodCycleBasis`~~ | **T-GEN** (`AnalyticLoopsGenerateH1`) | ✅ **done** — T-GEN proved unconditionally (#248), headlines rewired (#250/#251) |
| **G2** | `AX_curve_generates_jacobian` | the Abel–Jacobi image generates the torus (Part C "generates" clause) | open |
| **G3** | `AX_period_functoriality` | naturality of the period map under holomorphic `X → Y` | open |
| **G4** | `AX_torus_self_albanese` | a complex torus is its own Albanese (the base case of universality) | open |

**When G2–G4 are discharged, the three-part artifact (definition + anti-vacuity
subset + axiom-free universal property) is the complete, minimal, categorical
proof that we have correctly formalized a construction of the Jacobian** — and it
is far shorter to audit than the 24.

### Why this is the priority, not a detour

The universal property is not merely elegant. It is **the single most
convincing statement in the development** — the one that closes the wrong-object
failure mode outright. Making it axiom-free is therefore the highest-leverage
validation work: it upgrades the artifact from "necessary-condition evidence"
(Parts A+B alone) to "categorical certificate."

With G1 done, the **Buzzard challenge itself is axiom-free**; the remaining
G2–G4 are the torus-side axioms specific to this Albanese capstone (the
"validation endgame", beyond the 24). See `AXIOM_AUDIT.md` for their statements
and vetting status (the axiom certificate / verification side), and
[`FAITHFULNESS.md`](FAITHFULNESS.md) for the informal↔formal correspondence.

---

## 3. One-paragraph version (for a referee)

*The Jacobian is defined as `H⁰(X,Ω¹)*` modulo its period lattice (recognizably
the standard construction). Three machine-checked, **axiom-free** lemmas certify
the construction is non-degenerate: the lattice has full rank `2g` (so the
quotient is a `g`-dimensional torus), and the Abel–Jacobi map is holomorphic,
basepoint-preserving, and injective for positive genus. The single theorem
`ofCurve_isJacobian` then proves the construction satisfies the Albanese
universal property — it is the initial object among pointed holomorphic maps from
`X` to complex tori — which, by Yoneda, characterizes it up to unique isomorphism.
That theorem is the whole validation: granting Lean's kernel, a mathematician
need read only the definition, the three non-vacuity lemmas, and the statement of
the universal property to be convinced the right object was built. As of PR #251
the definition and all three non-vacuity lemmas — and indeed every Buzzard
headline — are axiom-free; the remaining formal work is to discharge the three
torus-side axioms `ofCurve_isJacobian` still rests on, after which the categorical
certificate itself is unconditional.*
