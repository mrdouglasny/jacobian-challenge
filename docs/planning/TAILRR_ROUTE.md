# TAILRR_ROUTE — the cheapest honest path to `TailRiemannRoch X`

Branch `feat/tail-riemann-roch` (on top of the #184 tower). Target = the named input of
`TailGenusTarget.lean`:

```
def TailRiemannRoch (X) ... : Prop :=
  ∀ A : Divisor X, (∀ x, (0:Divisor X) x ≤ A x) →
    2 * (kirovGenus X : ℤ) - 2 < Divisor.deg X A →
    (lDim (X := X) A : ℤ) = Divisor.deg X A + 1 - kirovGenus X
```

## Inventory verdict (the "cheap bridge" candidates, all REJECTED)

* **Cup-kill + RR + h¹-monotonicity alone**: cup-kill gives `h¹(A) = 0` only for `A ≥ A₀`;
  `cohomological_riemannRoch` then gives `l(A) = deg A + 1 − h¹(𝒪)`.  TWO gaps, not one:
  (i) the constant is `h¹(𝒪)`, not `kirovGenus`; (ii) the sharp range `deg A > 2g−2` for
  `A ⊉ A₀`.  Monotonicity (`h1Dim_add_single_le`) runs the WRONG way (vanishing at a larger
  divisor never descends).  Both gaps are exactly Serre-duality content:
  `h¹(𝒪) = g` IS duality at `D = 0`, and sharp-range vanishing IS `h¹(A) = l(K−A) = 0`,
  `deg K = 2g−2`.  No duality-free derivation exists (this is where the genuinely analytic
  global input enters the subject).  REJECTED as a complete route; the cup-kill stays as
  rung-3 substrate.
* **Čech-side duality via the §17.9 chain** (`TailUnwind.pairing_surjective_of_cechTailComparison`):
  gated on `CechTailComparison` = the multi-chart smeared-pole evaluation wall
  (`UNWIND_BLOCKER.md`).  Strictly harder analysis than the Miranda tail model.  REJECTED.
* **Hodge/Dolbeault `h¹(𝒪) = g`**: conjugate-form positivity (Kirov's `AbelPairingPositivity`)
  is post-base, not in our port; would need fresh surface integration.  REJECTED.

## The route: the Miranda Ch. VI tail tower, natively (KIROV_ROUTE_IDEAS items 3–4)

Tail H¹ := coker(α_D : ℳ(X) → 𝒯[D]); ALL of RR-I + duality happens in the tail model; the
statement `TailRiemannRoch` mentions only `lDim`/`deg`/`kirovGenus`, so **no tail↔Čech bridge
is needed anywhere**.  Čech facts used: `riemannRoch_inequality` (the M-bound, proven),
`lDim_zero_eq_one`, `lDim_eq_zero_of_deg_neg`, `finiteDimensional_globalSections` (+
`globalSectionsEquivQuot` for `FiniteDimensional ℂ (lSysModule D)`), and
`CanonicalForm17Data.hKgenus` (`l(K) = kirovGenus`, proven via `omega17`).

Final assembly (all inside the tail model, pair frame `(ω₀, K)` from
`nonempty_canonicalForm17Data`):

1. tail RR-I: `l(D) − h¹_t(D) = deg D + 1 − g_t`, `g_t := h¹_t(0)` (pure Finsupp/dimension
   bookkeeping, no analysis);
2. tail Serre duality: `h¹_t(D) = lDim (K − D)`;
3. `g_t = h¹_t(0) = l(K) = kirovGenus X` (duality at `0` + `hKgenus`);
4. `deg K = 2g − 2` (RR-I at `D = K` + duality `h¹_t(K) = l(0) = 1`);
5. `TailRiemannRoch`: for effective `A`, `deg A > 2g−2 = deg K`: `h¹_t(A) = l(K−A) = 0`
   (`lDim_eq_zero_of_deg_neg`), so RR-I collapses to the sharp formula.

### Rungs (planned files, all under `vendor/kirov-dolbeault-port/KirovDolbeault/Dolbeault/`)

| Rung | File | Content | Status target |
|------|------|---------|--------|
| T1 | `TailCoeffFull.lean` | FULL Laurent coefficients (`stripFun` leading-term peeling over the proven `laurentCoeff`; honest at every order, junk-free): linearity (no order hypotheses), order law `(∀ k < m, c_k = 0) ↔ m ≤ ord`, germ-congruence, level-shift | **LANDED, unconditional** |
| T2 | `TailSpaceGlobal.lean` | global truncated-tail space `𝒯[D] ⊆ (X×ℤ) →₀ ℂ` (uncurried), upper space, truncation maps, window subspace with `dim = deg D' − deg D` (+ Pi model) | **LANDED, unconditional** |
| T3 | same file | `α_D : ℳ(X) →ₗ`, kernel `= L(D)` (order law), junk-invariance, level compatibility | **LANDED, unconditional** |
| T4 | `TailRR1.lean` | finiteness `h¹_t(D) < ∞` (deep-truncation kill + M-bound, NO Čech vanishing) + window exactness + tail RR-I via comparable-pair χ-constancy (`posPart` common refinement) | **LANDED, unconditional** |
| T5 | `TailSerre.lean` | `planarCoeff` + window product law; `TailPairFrame` (slots + residue atom); pairing well-defined + linear + junk-free; **injectivity half landed**; surjectivity = named input `PairingSurjective` | **LANDED, conditional pieces as planned** |
| T6 | `TailSerre.lean` Part E | assembly: `tailRiemannRoch_of_pairingSurjective : TailPairFrame → PairingSurjective → TailRiemannRoch X` | **LANDED** |

**Status 2026-06-11 (am): T1–T6 all landed (standard-3, no custom axioms, no sorries).**

**Status 2026-06-11 (pm, S-lane): T7 LANDED — `TailSurjectivity.lean` proves
`TailPairFrame.pairingSurjective : P.PairingSurjective` (Miranda VI.3.10, standard-3,
no custom axioms, no sorries).  `TailRiemannRoch X` is now a theorem conditional on
ONE named hypothesis — frame existence (`TailPairFrame.tailRiemannRoch`).
Residual-input ledger: `docs/planning/TAILRR_BLOCKER.md`.**

| T7 | `TailSurjectivity.lean` | general window product law; `mulTail` multiplication–truncation operator (+ transport identity, upper kill); local inverse tails (division); `mulH1`/`tailPsiAct` (+ injectivity); the unwind (VI.3.7/3.9); the VI.3.10 pigeonhole over `serre_surjectivity_dim_core` + `tail_riemannRoch_I` | **LANDED, unconditional** |

### The ONE isolated analytic atom: the pair-frame residue theorem

```
PairResidueTheorem (data : CanonicalForm17Data X) : Prop :=
  ∀ F : MeromorphicFunction X, (total residue of F·ω₀) = 0
```

Needed EXACTLY ONCE: well-definedness of the pairing on the quotient `H¹_t(D)`
(`⟨h, α_D f⟩ = ∑_p Res_p(f·h·ω₀) = 0`).  Every other step is finite coefficient algebra.
Port status: `FormResidueTheorem.lean` has the trace-route skeleton with the trace
CONSTRUCTION open (Gate A; the 50 `FormTrace*` files are conditional);
`GeneralMLDistribution.res_eq_zero_of_globalMeromorphic` is likewise gated on
`FormResidueTrace`.  Kirov's own tree discharges it by the Stokes-atom tower
(`ResidueTheoremStokes`, ~3.7k LoC, post-base — route ideas only).  So the atom is named,
honest, and isolated — the tower converts the blocker surface from "all of large-degree RR"
to "this single classical theorem", which is shared infrastructure with Abel-⊆ (item 1's
E3b) anyway.

If the atom is NOT discharged this session, the deliverable is
`TailRiemannRoch_of_pairResidue : PairResidueTheorem data → TailRiemannRoch X`
plus `TAILRR_BLOCKER.md` recording it as the single residual input.
