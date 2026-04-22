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
-- `localOrder (f, p, q)` defined in a consumer module
-- (probably `Jacobian/Functoriality.lean`). Declare axiom here once
-- consumed.
--
-- Target signature (sketch):
--
--   axiom AX_BranchLocus {X Y : Type*} [...]
--       (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
--       (hnc : ¬ ∀ x y, f x = f y) :
--       -- (c): independence of q
--       ∀ q₁ q₂ : Y,
--         (∑ p ∈ (f ⁻¹' {q₁}).toFinset, localOrder f p q₁) =
--         (∑ p ∈ (f ⁻¹' {q₂}).toFinset, localOrder f p q₂)
--       -- (d): finite critical values
--       ∧ { q : Y | ∃ p ∈ f ⁻¹' {q}, localOrder f p q > 1 }.Finite

end Jacobians.Axioms
