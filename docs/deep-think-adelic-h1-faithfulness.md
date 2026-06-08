# Deep-think query — is the adelic H¹ anchor (Weil repartitions on a curve) faithful?

## Role & ask

You are a research collaborator vetting the **mathematical faithfulness** of a Lean
4 / Mathlib formalization. We are building an *intermediate, faithfully-defined*
layer for sheaf cohomology on a compact Riemann surface (a curve), to replace
opaque axioms for `H¹` / Riemann–Roch / Serre duality. The design: define `H¹`
**algebraically** via Weil **repartitions** (a simplified adele), and state RR +
Serre as `sorry`-ed pinning theorems (the "challenge"). CI is green and two code
reviews pass; we now want an independent check that the **definitions and theorem
statements are the right mathematics** — faithful and provable, not degenerate.

**Deliverable:** for each numbered question below, a clear verdict (faithful /
problem, with specifics) and any convention error or hidden obstruction. Be
concrete; cite the classical source (Weil repartitions; Serre, *Groupes
algébriques et corps de classes* ch. II; Forster *Lectures on Riemann Surfaces*;
Stichtenoth) where relevant.

## Setting

- `X` is a **compact connected Riemann surface** (a 1-dim complex manifold), NOT
  an abstract algebraic curve. Places = points `p : X`.
- `orderAt p (f) : WithTop ℤ` is the chart-local Laurent **order** (valuation) of
  a meromorphic function at `p`; `⊤` means "germ is zero at p". So a pole of
  order `n` has `orderAt = -n`, a zero of order `n` has `+n`, `⊤` = identically
  zero near `p`.

## The Lean definitions (verbatim, cleaned)

```lean
-- The function field K_X, as an ADDITIVE ℂ-vector space (germ quotient):
-- meromorphic-at-every-point functions, modulo functions that are germ-zero
-- (order ⊤) everywhere.
def MeroFunctions (X) : Submodule ℂ (X → ℂ) := { f | ∀ p, MeromorphicAtX f p }
def GermZero (X)    : Submodule ℂ (MeroFunctions X) := { f | ∀ p, orderAt p f = ⊤ }
abbrev MeroField (X) : Type := MeroFunctions X ⧸ GermZero X     -- = K_X
-- order descends to the quotient:
def orderAtField (p) : MeroField X → WithTop ℤ        -- = v_p

-- H⁰(O(D)) = L(D), already a real def (a ℂ-subspace of K_X):
def riemannRochSpace (D : Divisor X) : Submodule ℂ (MeroField X) :=
  { F | ∀ p, (-(coeff p D) : WithTop ℤ) ≤ orderAtField p F }   -- ord_p(F) ≥ -D(p)

-- A Weil repartition: a K_X-valued family, integral at all but finitely many places.
def IsRepartition (r : X → MeroField X) : Prop :=
  { p | ¬ (0 : WithTop ℤ) ≤ orderAtField p (r p) }.Finite       -- cofinitely ord ≥ 0
def repartitions (X) : Submodule ℂ (X → MeroField X) := { r | IsRepartition r }   -- 𝔸_X

-- 𝔸_X(D): bounded by the divisor.
def repartitionsBounded (D) : Submodule ℂ (X → MeroField X) :=
  { r | IsRepartition r ∧ ∀ p, (-(coeff p D) : WithTop ℤ) ≤ orderAtField p (r p) }

-- Diagonal (principal) repartitions K_X ↪ 𝔸_X, f ↦ (p ↦ f).  Lands in 𝔸_X because
-- a meromorphic function on a compact RS has finitely many poles (proved).
def diagonalRepartition : MeroField X →ₗ[ℂ] (X → MeroField X) := fun f => (fun _ => f)
def diagonalRepartitionRes : MeroField X →ₗ[ℂ] repartitions X      -- corestricted into 𝔸_X
def repartitionsBoundedRes (D) : Submodule ℂ (repartitions X)     -- 𝔸_X(D) ∩ 𝔸_X via comap

-- THE DEFINITION UNDER REVIEW:  H¹(X, O(D)) := 𝔸_X / (𝔸_X(D) + K_X)
def adeleH1Relations (D) : Submodule ℂ (repartitions X) :=
  repartitionsBoundedRes D ⊔ LinearMap.range diagonalRepartitionRes
def adeleH1 (D : Divisor X) : Type := (repartitions X) ⧸ adeleH1Relations D
-- adeleH1 is a ℂ-vector space (quotient of 𝔸_X by 𝔸_X(D)+K_X).
```

## The pinning theorems (stated as `sorry`; the "challenge")

```lean
-- genus X = finrank ℂ (HolomorphicOneForm X)  (already defined, validated on ℙ¹/elliptic)

theorem riemannRoch_anchor (D) :
    (finrank ℂ (riemannRochSpace D) : ℤ) - (finrank ℂ (adeleH1 D) : ℤ)
      = Divisor.deg X D + 1 - (genus X : ℤ)

theorem adeleH1_finiteDim (D) : FiniteDimensional ℂ (adeleH1 D)

theorem serre_anchor :
    ∃ K : Divisor X, ∀ D : Divisor X,
      Nonempty (adeleH1 D ≃ₗ[ℂ] Module.Dual ℂ (riemannRochSpace (K - D)))
```

## Questions

1. **Is `adeleH1 D := 𝔸_X/(𝔸_X(D)+K_X)` the faithful Weil `H¹(X, O(D))`?** With our
   conventions (repartition = `K_X`-valued family integral a.e.; `𝔸_X(D)` = `ord_p ≥
   −D(p)`; diagonal = principal). Any sign/convention error?

2. **The key subtlety — repartitions valued in the GLOBAL field `K_X`, not the local
   completions `K_p`.** Our `r : X → MeroField X` assigns at each place an element of
   the *same global* field `K_X` (with an order condition), NOT an element of the
   local completion `K_p`. Weil's original "répartitions" (Serre, ch. II) are
   *also* `K`-valued, so we believe this is exactly Weil's object (hence "repartitions"
   not "adeles"). **Confirm**: is the `K`-valued repartition the correct object, and
   does `H¹ = 𝔸/(𝔸(D)+K)` compute the right cohomology with it — or does faithful
   `H¹` require the `K_p`-completions (in which case ours is wrong/degenerate)?

3. **Serre duality provability.** `serre_anchor` is `∃ K, ∀ D, H¹(O(D)) ≅ H⁰(O(K−D))^*`.
   (a) Is `∃ K, ∀ D` the right strength (existence of a dualizing divisor)?
   (b) The intended proof is the **residue pairing** `𝔸/(𝔸(D)+K) × H⁰(Ω(−D)) → ℂ`,
   `(a, ω) ↦ ∑_p res_p(a_p ω)`. But note `K_X = MeroField` is currently only an
   **additive ℂ-vector space** — to form `a_p · ω` (function × 1-form) the proof needs
   `K_X`'s multiplication / its action on 1-forms. **Confirm** the statement is provable
   *in principle* but flag that the proof requires completing `K_X` to a field / a
   module action, and whether `∑res = 0` (residue theorem) is the crux.

4. **Riemann–Roch statement.** `h⁰(D) − h¹(D) = deg D + 1 − g` with `h⁰ =
   finrank(riemannRochSpace D)`, `h¹ = finrank(adeleH1 D)`, `g = finrank(HolomorphicOneForm)`.
   Is the adelic proof (`𝔸(D)/𝔸(D′)` comparison + the strong-approximation /
   `K_X`-codimension count) going to go through with these definitions? Any
   convention mismatch in the index arithmetic?

5. **Complex-analytic vs algebraic.** `X` is an analytic compact Riemann surface, not a
   scheme; `K_X` = meromorphic functions. The classical adelic RR/Serre is for an
   algebraic function field over a base field. Does the machinery transfer directly
   (meromorphic functions on a compact RS form a transcendence-degree-1 function field
   over `ℂ`, places = points, residue fields = `ℂ`)? In particular: does the proof
   secretly need **existence of a non-constant meromorphic function** (so `K_X` is a
   genuine function field separating points) — and is that safe to assume / where
   should it enter?

6. **Finite-dimensionality.** Is `adeleH1_finiteDim` provable from these definitions
   directly (adelic finiteness of `𝔸/(𝔸(D)+K)`), or does it require RR / an extra input?
   Should it be proven before RR, or does RR give it?

7. **Degeneracy/vacuity check.** Is there any way these definitions are *degenerate*
   (e.g. `adeleH1` accidentally `0`, or always infinite-dim, or `serre_anchor`'s `∃ K`
   satisfiable by a junk `K`) that would let a wrong definition pass the pins? The genus
   is already validated (ℙ¹ → 0, elliptic → 1) via a *separate* `HolomorphicOneForm`
   def; does that constrain `adeleH1` correctly through RR?

8. **Anything missing.** Any standard hypothesis, convention, or companion lemma the
   anchor should add now (while the statements are being "locked down") to avoid a
   later faithfulness gap.
```
