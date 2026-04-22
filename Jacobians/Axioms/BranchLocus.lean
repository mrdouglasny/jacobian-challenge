/-
`AX_BranchLocus`: properness, discrete fibers, and degree invariance
for non-constant holomorphic maps between compact Riemann surfaces.

**Statement.** For `f : X → Y` a non-constant holomorphic map between
compact Riemann surfaces:

(a) `f` is proper (preimage of compact is compact — automatic since
    `X` is compact).
(b) Every fiber `f⁻¹(q)` is discrete and (hence, by compactness) finite.
(c) The fiber sum `∑_{p ∈ f⁻¹(q)} localOrder(f, p, q)` is independent
    of `q`. This common value is `ContMDiff.degree f`.
(d) The set of `q` at which some point has `localOrder(f, p, q) > 1`
    (the critical values) is finite.

**Consequences.**
* `ContMDiff.degree f` is a well-defined `ℕ`, computable at any point
  via local orders — no Sard's theorem needed (Sard is `TODO` at this
  pin, see `Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`).
* `pushforward_pullback = deg • id` reduces to "f_* f^* ω = deg(f) · ω
  on 1-forms", which reduces to fiber-counting using (c).

**Why axiomatized.** The proof uses: non-constant holomorphic maps are
open (Open Mapping Theorem for 1-dim), combined with compactness of
`X` and connectedness of `Y`. All standard, but Mathlib's local-
holomorphic-map-is-open infrastructure is specific to `ℂ`-valued maps,
not maps between manifolds — this needs adaptation we haven't done.

See `docs/formalization-plan.md` §7; discharge priority #2.
Reference: Forster Ch. I §4; Mumford Vol I §II.2.
-/
import Jacobians.RiemannSurface.OneForm

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff

-- TODO (AX_BranchLocus): precise Lean statement requires
-- `localOrder (f, p, q)` defined in a consumer module (probably
-- `Jacobian/Functoriality.lean`). Declare axiom here once consumed.
--
-- Convention: `localOrder f p q = 0` when `f p ≠ q`. This lets the fiber
-- sum `∑' p : X, localOrder f p q` range over all of `X` (finitely many
-- nonzero terms since each fiber is finite), avoiding the `toFinset`
-- dependent-type mess of the earlier draft.
--
-- Target signature (revised 2026-04-22 post-Gemini review):
--
--   axiom AX_BranchLocus {X Y : Type*} [...]
--       (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
--       (hnc : ¬ ∃ c : Y, ∀ x : X, f x = c) :  -- non-constant
--       -- (c): common degree d — independence of q via tsum.
--       ∃ d : ℕ, 0 < d ∧
--         (∀ q : Y, (∑' p : X, localOrder f p q) = d) ∧
--       -- (d): finite critical values.
--         { q : Y | ∃ p : X, f p = q ∧ localOrder f p q > 1 }.Finite
--
-- Commentary.
-- * `¬ ∃ c, ∀ x, f x = c` is the standard "non-constant" predicate
--   (previous draft used `¬ ∀ x y, f x = f y`, which is the double-∀
--   formulation — confusing even if equivalent).
-- * `∑'` (`tsum`) on a function with finite support returns the sum over
--   the support when the rest is `0`. No `Fintype`/`Decidable`
--   instance needed on preimages.
-- * The degree `d` is extracted as part of the conclusion; consumers
--   that want `ContMDiff.degree f` unpack it via `Classical.choose`.

end Jacobians.Axioms
