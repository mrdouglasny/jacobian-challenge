# Unified discharge plan — the three Albanese torus axioms (G2, G3, G4)

The Albanese categoricity capstone `ofCurve_isJacobian` rests on exactly three
torus axioms (after the #1 `dualCover` flip):

| | Axiom | What it says |
|---|---|---|
| **G2** | `AX_torus_self_albanese` | an abstract compact connected complex Lie group `A ≅ ℂ^m/Λ` is its own Albanese |
| **G3** | `AX_period_functoriality` | a holomorphic `f : X → A` sends `Λ_X` into the target lattice under the dual pullback |
| **G4** | `AX_curve_generates_jacobian` | the Abel–Jacobi image group-generates `J = ℂ^g/Λ` |

This file states the **minimal new axiom set** to turn all three into theorems,
the per-axiom reductions, and where **vendoring more of Kirov** removes work.

> **Headline result of this analysis.** The three reduce to **a single
> irreducible new axiom** — `AX_torus_uniformization` (G2) — *plus* a moderate
> Kirov-vendored build for G4. The "complex subtorus structure" axiom I earlier
> thought G4 needed is **avoidable** (Kirov's local Jacobi map + an open-subgroup
> argument). G3 needs no new axiom (it follows from G2 + already-proven
> naturality), modulo a small statement reframe.

```
                    ┌─ G4  ── (no new axiom) ── Kirov JacobiLocalMap + open-subgroup
ofCurve_isJacobian ─┤
                    ├─ G2  ── AX_torus_uniformization   ← the one irreducible new axiom
                    └─ G3  ── (no new axiom) ── proven naturality + G2,  + statement reframe
```

---

## G4 — `AX_curve_generates_jacobian`: dischargeable, **no new axiom** (vendor Kirov)

**Route B (Jacobi inversion), now cheap.** Kirov's
`Jacobians/PeriodLattice/JacobiLocalMap.lean` (../jacobian-claude, **sorry-free**)
already proves the analytic heart:
- `exists_jacobiBasePoints_det_ne_zero` — Forster 21.3: a rank-`g` base-point
  family with non-vanishing period-Jacobian determinant.
- `jacobiMap a : (Fin g → ℂ) → J`, `jacobiMap_hasStrictFDerivAt`,
  `jacobiDerivEquiv` — at such a family the derivative is a linear iso ⇒ (IFT)
  `jacobiMap` is a **local diffeomorphism** ⇒ open map near the center.

**Remaining build (moderate, ours):**
1. **Bridge** `jacobiMap a z  =  Σᵢ ofCurve x₀ (chart⁻¹ zᵢ)  (+ const)` — identify
   Kirov's local Jacobi map with the `g`-fold Abel–Jacobi sum of our `ofCurve`.
   (Both are "integrate the `ωᵢ` from `x₀`"; this is plumbing between his coords
   and ours, via the `bridgeFormEquiv` already used in `torusPullbackOneForm`.)
2. **Open image:** local diffeo ⇒ `Set.range (g-fold ofCurve sum)` contains an
   open set `U`.
3. **Open subgroup:** `H := AddSubgroup.closure (range (ofCurve x₀))` contains `U`
   (g-fold sums are sums of `ofCurve` points ∈ `H`, up to the `g·ofCurve x₀`
   shift) ⇒ `H ⊇ U − u₀ ∋ 0` open ⇒ `H` is an **open** subgroup.
4. **Open ⇒ ⊤:** an open subgroup is closed (`AddSubgroup.isClosed_of_isOpen` /
   complement is a union of open cosets) ⇒ clopen; `J` connected ⇒ `H = ⊤`.

Steps 2–4 are standard Mathlib. Step 1 is the real work (chart bookkeeping).
**No subtorus classification, no `Symᵍ` manifold theory, no axiom.** Effort:
days, not weeks, *given* the Kirov vendor.

**Vendor needed:** `JacobiLocalMap.lean` + its dependency cone (the Forster-21.3
determinant lemma, the local lift-charts, `genus`/forms infra it uses). Most of
its analytic base overlaps the already-vendored dolbeault port; scope the cone
before committing.

---

## G2 — `AX_torus_self_albanese`: the **one irreducible new axiom**

This is uniformization of an **abstract** compact connected complex Lie group
modelled on `ℂ^m`. Neither Mathlib (no compact-complex-Lie-group theory, no
Cartan) nor Kirov (he only ever builds the **concrete** `ℂ^g/Λ`, never uniformizes
an abstract `A`) has it. So G2 is genuinely the irreducible analytic input.

**Cleanest axiom to state** (replace the bespoke `TorusSelfAlbanesePresentation`
with the standard classical theorem it packages):

```lean
/-- **Uniformization of a complex torus** (Birkhoff/Cartan; Birkenhake–Lange Ch.1).
A compact connected complex Lie group modelled on `ℂ^m` is biholomorphically
group-isomorphic to `ℂ^m/Λ` for a full `ZLattice Λ`, with the iso's inverse
coordinate given by integrating the invariant 1-forms from `0`. -/
axiom AX_torus_uniformization {m} {A} [compact connected complex LieAddGroup on ℂ^m] :
    ∃ (Λ : Submodule ℤ (Fin m → ℂ)) (_ : IsZLattice ℝ Λ),
      Nonempty (TorusUniformization m A Λ)   -- biholo group iso + invariant-form-integral coordinate
```
`TorusSelfAlbanesePresentation` is then a **definition** built from it. Vetting:
already Gemini+Codex-vetted in spirit (2026-06-02); re-vet the repackaged form for
type/strength/satisfiability (the witness is `ℂ^m/Λ` itself — non-vacuous).

**Build alternative (multi-week):** complex `exp`/developing map of `A` as a flat
compact complex Lie group, surjectivity (compact+connected), `ker exp` a
`ZLattice`. Genuinely Mathlib-grade; would also be reusable. Recommend
**axiomatize now, build later** — it is one clean, standard, classically-true
statement off the Buzzard critical path.

**Statement-level escape hatch (worth weighing):** if `IsJacobian` is restricted
to **concretely-presented** tori `ℂ^m/Λ` (carrying the presentation as data)
rather than abstract `A`, then G2 is *trivial* (the presentation is given) and the
axiom vanishes — at the cost of a slightly weaker (but arguably more honest)
categoricity statement. This is the cheapest path to "Albanese axiom-free" and
should be a conscious choice, not a default.

---

## G3 — `AX_period_functoriality`: no new axiom, but reframe the statement

`Λ_X ↦ P.lattice` under the dual pullback `torusAmbientLinear f`. Two facts:
- **Naturality is already proven:** `torusPullback_pathIntegral_naturality`
  (`UniversalProperty.lean:280`): `∮_{f∘γ} ω = ∮_γ f^*ω`. With
  `span_periodLatticeInBasis_eq_top` (Λ_X is ℝ-spanned by loop periods) it
  suffices to send each loop period into the target lattice.
- **Loop ⇒ lattice** uses G2's self-Albanese integration identity (a loop's
  developing ambiguity lands in `P.lattice`).

**Statement bug to fix (soundness-relevant).** As written G3 quantifies over an
**arbitrary** `P : TorusPresentation m A`; for a `P` whose `lattice` is unrelated
to `A`, the containment is **false**, so the axiom-as-written is *too strong /
not satisfiable for all `P`*. Fix before relying on it:
- **(A)** change the hypothesis to take the **self-Albanese** presentation from
  `AX_torus_uniformization` (or a `TorusUniformization m A Λ`), then steps above
  give a theorem; or
- **(B)** fold the lattice-containment field into `AX_torus_uniformization`'s
  output, so G3 disappears as a separate obligation.

Either way **G3 introduces no new axiom** and lands once G2 exists. Recommend (B)
(one axiom emits everything torus-side). *Flag:* the current `∀ P` form should be
re-vetted / corrected regardless, since an over-general axiom is a latent
soundness risk (CLAUDE.md "vet STRENGTHENING for satisfiability").

---

## Minimal new-axiom set & recommended order

**Irreducible new axioms: ONE** — `AX_torus_uniformization` (G2), or **zero** if
the concrete-tori escape hatch is chosen, or **zero** if G2 is built (multi-week).

Recommended landing order (each independently verifiable):
1. **G4** — vendor Kirov `JacobiLocalMap` + build steps 1–4. *No axiom; days.*
   Replaces `AX_curve_generates_jacobian` with a theorem. **Start here.**
2. **G2** — restate as `AX_torus_uniformization` (1 clean axiom) + tracking issue
   + owner sign-off; derive `TorusSelfAlbanesePresentation` from it. *Net: cleaner
   axiom, same count.* (Or take the concrete-tori escape hatch → 0 axioms.)
3. **G3** — option (B): emit lattice-containment from #2; G3 becomes a theorem.
   *Also fix the `∀ P` over-generality now (soundness).*

End state: `ofCurve_isJacobian` rests on **`AX_torus_uniformization` alone**
(down from 3), or **axiom-free** if G2 is built / the escape hatch is taken — i.e.
the Albanese categoricity certificate becomes a one-axiom (or zero-axiom) result.

## Vendoring assessment (Kirov)

| Need | Kirov has it? | Action |
|---|---|---|
| G4 local Jacobi inversion (Forster 21.3 + IFT) | **Yes** — `JacobiLocalMap.lean`, sorry-free | **vendor** (port its cone) |
| G4 torus covering/quotient structure | Yes — `JacobianConstruction/ZLatticeQuotient.lean` | reuse if our `ComplexTorus` lacks a piece |
| G2 abstract torus uniformization | **No** (concrete tori only) | axiomatize or build |
| G3 naturality | n/a — **we already have it** (`torusPullback_pathIntegral_naturality`) | reuse ours |

**Independence caveat** ([[no-more-vendoring]]): vendoring more Kirov trades
independence for speed. For G4 the payoff is large (sorry-free analytic engine
that would otherwise be weeks). Per owner's note in this session, vendoring is on
the table for the Albanese endgame; record provenance + per-file attribution as
with the dolbeault port, or reimplement-with-citation if independence is
preferred for the final artifact.
