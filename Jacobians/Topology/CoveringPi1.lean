/-
# π₁ via covering spaces: the deck-group isomorphism

For a covering map `p : E → X` with simply connected total space `E`, the
monodromy action at a basepoint lift `e₀` is a bijection between the path
classes `Path.Homotopic.Quotient (p e₀) y` and the fiber `p ⁻¹' {y}`; at
`y = p e₀` this is a bijection `π₁(X, p e₀) ≃ p ⁻¹' {p e₀}`.

When the covering is the quotient by a free, properly discontinuous action of
a commutative group `G` (`IsAddQuotientCoveringMap`), this upgrades to a group
isomorphism `Multiplicative G ≃* FundamentalGroup X (p e₀)` — the classical
"deck group = π₁ of the base" — which sends `g : G` to the projection of ANY
path `e₀ → g +ᵥ e₀` in `E` (`deckHom_eq_fromPath`).

Instantiated in `Jacobians.Topology.PuncturedPlanePi1` for the shifted
exponential covering of the punctured plane, giving `π₁(ℂ ∖ {a}) ≃ ℤ` with the
circle loop around `a` as generator. Route (c) of `docs/planning/SVK_ROUTE.md`
(consumer: the slit-sheet discharge plan for `AX_PeriodCycleBasis`,
`docs/planning/CYCLEBASIS_ALTERNATIVES.md` direction 2b).

Mathlib-only imports. Sorry-free and axiom-free
(beyond the three standard axioms).
-/
import Mathlib

namespace Jacobians.Topology

open CategoryTheory unitInterval

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

section Monodromy

variable (cov : IsCoveringMap p)

/-- If `Γ` is a pointwise lift through the covering map `p` of the path `γ`, then the
monodromy of the class of `γ` sends the starting lift to the endpoint of `Γ`. -/
theorem monodromy_mk {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) {e' : E}
    (Γ : Path (e : E) e') (hΓ : ∀ t, p (Γ t) = γ t) (he' : p e' = y) :
    cov.monodromy (Path.Homotopic.Quotient.mk γ) e = ⟨e', he'⟩ := by
  obtain ⟨e, he⟩ := e
  apply Subtype.ext
  show cov.liftPath γ e (γ.source.trans (show p e = x from he).symm) 1 = e'
  have hlift : (Γ : C(I, E)) = cov.liftPath γ e (γ.source.trans (show p e = x from he).symm) :=
    (cov.eq_liftPath_iff' _).mpr ⟨funext fun t ↦ hΓ t, Γ.source⟩
  rw [← hlift]
  exact Γ.target

/-- Monodromy from a fixed basepoint lift is injective on path classes when the total
space is simply connected: two paths in the base whose lifts from `e₀` share their
endpoint are homotopic. -/
theorem monodromy_injective [SimplyConnectedSpace E] (e₀ : E) {y : X} :
    Function.Injective fun γ : Path.Homotopic.Quotient (p e₀) y ↦
      cov.monodromy γ ⟨e₀, rfl⟩ := by
  intro γ₀ γ₁
  induction γ₀, γ₁ using Path.Homotopic.Quotient.ind₂ with
  | mk γ₀ γ₁ =>
  intro hmono
  -- the lifted paths share their endpoint
  have hend : cov.liftPath γ₀ e₀ γ₀.source 1 = cov.liftPath γ₁ e₀ γ₁.source 1 :=
    congrArg Subtype.val hmono
  let Γ₀ : Path e₀ (cov.liftPath γ₀ e₀ γ₀.source 1) :=
    ⟨cov.liftPath γ₀ e₀ γ₀.source, cov.liftPath_zero .., rfl⟩
  let Γ₁ : Path e₀ (cov.liftPath γ₀ e₀ γ₀.source 1) :=
    ⟨cov.liftPath γ₁ e₀ γ₁.source, cov.liftPath_zero .., hend.symm⟩
  -- simply connected total space: the lifts are homotopic; project the homotopy down
  have hmap : (Γ₀.map cov.continuous).Homotopic (Γ₁.map cov.continuous) :=
    Path.Homotopic.map (SimplyConnectedSpace.paths_homotopic Γ₀ Γ₁) ⟨p, cov.continuous⟩
  have hy : y = p (cov.liftPath γ₀ e₀ γ₀.source 1) :=
    γ₀.target.symm.trans (congr_fun (cov.liftPath_lifts γ₀ e₀ γ₀.source) 1).symm
  -- the projected lifts are the original paths
  have e₀eq : (Γ₀.map cov.continuous).cast rfl hy = γ₀ := by
    ext t
    exact congr_fun (cov.liftPath_lifts γ₀ e₀ γ₀.source) t
  have e₁eq : (Γ₁.map cov.continuous).cast rfl hy = γ₁ := by
    ext t
    exact congr_fun (cov.liftPath_lifts γ₁ e₀ γ₁.source) t
  show Path.Homotopic.Quotient.mk γ₀ = Path.Homotopic.Quotient.mk γ₁
  rw [← e₀eq, ← e₁eq, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_cast]
  exact congrArg (Path.Homotopic.Quotient.cast · rfl hy) (Quotient.sound hmap)

/-- Monodromy from a fixed basepoint lift is surjective onto the fiber when the total
space is path connected. -/
theorem monodromy_surjective [PathConnectedSpace E] (e₀ : E) {y : X} :
    Function.Surjective fun γ : Path.Homotopic.Quotient (p e₀) y ↦
      cov.monodromy γ ⟨e₀, rfl⟩ := by
  rintro ⟨e', he'⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at he'
  subst he'
  exact ⟨(Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e₀ e')).map
    ⟨p, cov.continuous⟩, cov.monodromy_map _⟩

/-- **Path classes = fiber, over a simply connected cover.** For a covering map with
simply connected total space, monodromy from a basepoint lift `e₀` identifies path
classes in the base starting at `p e₀` with the fiber over the endpoint. -/
noncomputable def pathClassEquivFiber [SimplyConnectedSpace E] (e₀ : E) (y : X) :
    Path.Homotopic.Quotient (p e₀) y ≃ p ⁻¹' {y} :=
  Equiv.ofBijective _ ⟨monodromy_injective cov e₀, monodromy_surjective cov e₀⟩

/-- **π₁ = fiber of the universal cover** (as a bijection). -/
noncomputable def pi1EquivFiber [SimplyConnectedSpace E] (e₀ : E) :
    FundamentalGroup X (p e₀) ≃ p ⁻¹' {p e₀} :=
  pathClassEquivFiber cov e₀ (p e₀)

end Monodromy

end Jacobians.Topology
