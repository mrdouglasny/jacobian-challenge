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
  change cov.liftPath γ e (γ.source.trans (show p e = x from he).symm) 1 = e'
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
  change Path.Homotopic.Quotient.mk γ₀ = Path.Homotopic.Quotient.mk γ₁
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

section Deck

variable {G : Type*} [AddGroup G] [AddAction G E] (h : IsAddQuotientCoveringMap p G)
include h

/-- A quotient covering map is invariant under the deck action. -/
theorem proj_vadd (g : G) (e : E) : p (g +ᵥ e) = p e :=
  h.apply_eq_iff_mem_orbit.mpr (AddAction.mem_orbit e g)

variable [SimplyConnectedSpace E]

/-- The deck loop of `g : G`: the class in `π₁(X, p e₀)` of the projection of a path
from `e₀` to `g +ᵥ e₀` in the (simply connected) total space. -/
noncomputable def deckLoop (e₀ : E) (g : G) : FundamentalGroup X (p e₀) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
    (((PathConnectedSpace.somePath e₀ (g +ᵥ e₀)).map h.isCoveringMap.continuous).cast
      rfl (proj_vadd h g e₀).symm))

/-- Monodromy along the deck loop of `g` sends the fiber point `g' +ᵥ e₀` to
`(g' + g) +ᵥ e₀`: the lift of the deck loop starting at `g' +ᵥ e₀` is the
`g'`-translate of the chosen path, by uniqueness of lifts. -/
theorem monodromy_deckLoop (e₀ : E) (g g' : G) :
    h.isCoveringMap.monodromy (FundamentalGroup.toPath (deckLoop h e₀ g))
        ⟨g' +ᵥ e₀, proj_vadd h g' e₀⟩
      = ⟨(g' + g) +ᵥ e₀, proj_vadd h (g' + g) e₀⟩ := by
  haveI : ContinuousConstVAdd G E := h.toContinuousConstVAdd
  refine monodromy_mk h.isCoveringMap _ _
    (((PathConnectedSpace.somePath e₀ (g +ᵥ e₀)).map
      (continuous_const_vadd g')).cast rfl (vadd_vadd g' g e₀).symm)
    (fun t ↦ ?_) (proj_vadd h (g' + g) e₀)
  change p (g' +ᵥ (PathConnectedSpace.somePath e₀ (g +ᵥ e₀)) t)
    = p ((PathConnectedSpace.somePath e₀ (g +ᵥ e₀)) t)
  exact proj_vadd h g' _

/-- The base case of `monodromy_deckLoop`: the deck loop of `g` moves the canonical
basepoint lift to `g +ᵥ e₀`. -/
theorem monodromy_deckLoop_base (e₀ : E) (g : G) :
    h.isCoveringMap.monodromy (FundamentalGroup.toPath (deckLoop h e₀ g)) ⟨e₀, rfl⟩
      = ⟨g +ᵥ e₀, proj_vadd h g e₀⟩ :=
  monodromy_mk h.isCoveringMap _ _ (PathConnectedSpace.somePath e₀ (g +ᵥ e₀))
    (fun _ ↦ rfl) (proj_vadd h g e₀)

/-- Deck loops compose contravariantly with `End`-multiplication (`End` multiplication
is reverse path composition, while lift translation adds on the left). -/
theorem deckLoop_add (e₀ : E) (g g' : G) :
    deckLoop h e₀ (g' + g) = deckLoop h e₀ g * deckLoop h e₀ g' := by
  apply monodromy_injective h.isCoveringMap e₀ (y := p e₀)
  change h.isCoveringMap.monodromy (FundamentalGroup.toPath (deckLoop h e₀ (g' + g))) ⟨e₀, rfl⟩
    = h.isCoveringMap.monodromy
        (FundamentalGroup.toPath (deckLoop h e₀ g * deckLoop h e₀ g')) ⟨e₀, rfl⟩
  have hmul : FundamentalGroup.toPath (deckLoop h e₀ g * deckLoop h e₀ g')
      = (FundamentalGroup.toPath (deckLoop h e₀ g')).trans
          (FundamentalGroup.toPath (deckLoop h e₀ g)) := rfl
  rw [monodromy_deckLoop_base h e₀ (g' + g), hmul, h.isCoveringMap.monodromy_trans_apply,
    monodromy_deckLoop_base h e₀ g', monodromy_deckLoop h e₀ g g']

end Deck

section DeckComm

variable {G : Type*} [AddCommGroup G] [AddAction G E] (h : IsAddQuotientCoveringMap p G)
variable [SimplyConnectedSpace E]
include h

/-- The deck homomorphism `Multiplicative G →* π₁(X, p e₀)` of a quotient covering by
a commutative group, sending `g` to the projection of a path `e₀ → g +ᵥ e₀`. -/
noncomputable def deckHom (e₀ : E) : Multiplicative G →* FundamentalGroup X (p e₀) :=
  MonoidHom.mk' (fun a ↦ deckLoop h e₀ a.toAdd) fun a b ↦ by
    change deckLoop h e₀ (a.toAdd + b.toAdd) = deckLoop h e₀ a.toAdd * deckLoop h e₀ b.toAdd
    rw [add_comm]
    exact deckLoop_add h e₀ a.toAdd b.toAdd

theorem deckHom_apply (e₀ : E) (g : G) :
    deckHom h e₀ (Multiplicative.ofAdd g) = deckLoop h e₀ g := rfl

theorem deckHom_bijective (e₀ : E) : Function.Bijective (deckHom h e₀) := by
  haveI : IsCancelVAdd G E := h.isCancelVAdd
  constructor
  · intro a b hab
    have hmono : h.isCoveringMap.monodromy
          (FundamentalGroup.toPath (deckLoop h e₀ a.toAdd)) ⟨e₀, rfl⟩
        = h.isCoveringMap.monodromy
          (FundamentalGroup.toPath (deckLoop h e₀ b.toAdd)) ⟨e₀, rfl⟩ := by
      exact congrArg (fun γ ↦ h.isCoveringMap.monodromy (FundamentalGroup.toPath γ)
        ⟨e₀, rfl⟩) hab
    rw [monodromy_deckLoop_base h e₀, monodromy_deckLoop_base h e₀] at hmono
    exact Multiplicative.toAdd.injective
      (IsCancelVAdd.right_cancel _ _ e₀ (congrArg Subtype.val hmono))
  · intro γ
    obtain ⟨g, hg⟩ := AddAction.mem_orbit_iff.mp (h.apply_eq_iff_mem_orbit.mp
      (h.isCoveringMap.monodromy (FundamentalGroup.toPath γ) ⟨e₀, rfl⟩).2)
    refine ⟨Multiplicative.ofAdd g, monodromy_injective h.isCoveringMap e₀ (y := p e₀) ?_⟩
    change h.isCoveringMap.monodromy
        (FundamentalGroup.toPath (deckHom h e₀ (Multiplicative.ofAdd g))) ⟨e₀, rfl⟩
      = h.isCoveringMap.monodromy (FundamentalGroup.toPath γ) ⟨e₀, rfl⟩
    rw [deckHom_apply, monodromy_deckLoop_base h e₀ g]
    exact Subtype.ext hg

/-- **The deck group is the fundamental group.** For a quotient covering by a free,
properly discontinuous action of a commutative group `G` on a simply connected space,
`π₁` of the base at `p e₀` is `Multiplicative G`; the iso sends `g` to the projected
deck loop `e₀ → g +ᵥ e₀`. -/
noncomputable def deckMulEquivPi1 (e₀ : E) :
    Multiplicative G ≃* FundamentalGroup X (p e₀) :=
  MulEquiv.ofBijective (deckHom h e₀) (deckHom_bijective h e₀)

theorem deckMulEquivPi1_apply (e₀ : E) (g : G) :
    deckMulEquivPi1 h e₀ (Multiplicative.ofAdd g) = deckLoop h e₀ g := rfl

/-- **Generator identification.** Any loop `γ` at `p e₀` in the base that lifts
pointwise to a path `e₀ → g +ᵥ e₀` upstairs represents the image of `g` under the
deck isomorphism. This is the form consumers use: it identifies explicit loops
(e.g. circle loops around a puncture) as the generators. -/
theorem deckMulEquivPi1_eq_fromPath (e₀ : E) (g : G) {e' : E}
    (Γ : Path e₀ e') (γ : Path (p e₀) (p e₀)) (hΓ : ∀ t, p (Γ t) = γ t)
    (he' : e' = g +ᵥ e₀) :
    deckMulEquivPi1 h e₀ (Multiplicative.ofAdd g)
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
  apply monodromy_injective h.isCoveringMap e₀ (y := p e₀)
  change h.isCoveringMap.monodromy
      (FundamentalGroup.toPath (deckMulEquivPi1 h e₀ (Multiplicative.ofAdd g))) ⟨e₀, rfl⟩
    = h.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e₀, rfl⟩
  rw [deckMulEquivPi1_apply, monodromy_deckLoop_base h e₀ g,
    monodromy_mk h.isCoveringMap γ ⟨e₀, rfl⟩ Γ hΓ (by rw [he']; exact proj_vadd h g e₀)]
  exact Subtype.ext he'.symm

end DeckComm

end Jacobians.Topology
