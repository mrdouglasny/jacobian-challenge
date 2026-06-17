/-
# G3/G4 — the binary-split generation engine for the punctured plane

Issue #171 / `docs/planning/B1_GENERATION_ROUTE.md` rungs **G3/G4**
(binary-split design, third/fourth-pass notes), continuing the SVKGEN
lane's ladder with the strengthening its G4 notes call for: the induction
is run *for all basepoints and spokes simultaneously*, in the
abstract-subgroup membership form of the house G1 pattern.

**Main result** (`fromPath_mem_of_cellSpokes_subset`): every subgroup of
`π₁(ℂ ∖ T, x₀)` containing all **cell-spoke classes** — classes of loops
that live inside an open cell `W` with `W ∩ T = {s}` whose punctured part
is homeomorphic to a once-punctured plane, conjugated to the basepoint
along an arbitrary spoke — contains every loop class.

**Method.** Strong induction on `T.card` over a vertical-line split.
Both transports (the half-plane sides through
`halfPlaneHomeo`/`halfPlaneHomeoGT`, and the 90° rotation that makes the
real projections non-constant) are instances of ONE lemma
(`side_transfer`): membership statements pull back along `Subgroup.comap`
of the π₁ homomorphism induced by the side presentation, and the
generating set is closed under these pullbacks because spokes absorb all
basepoint corrections (`SpokeAlgebra`).  No normal-closure bookkeeping and
no meridian-conjugacy input is needed at this layer.

Mathlib-only mathematical content.
-/
import Jacobians.Topology.CoverGeneration
import Jacobians.Topology.SpokeAlgebra
import Jacobians.Topology.HalfPlaneHomeo
import Jacobians.Topology.PuncturedPlaneGeneration

namespace Jacobians.Topology

open Set

local notation "Qmk" => Path.Homotopic.Quotient.mk

/-! ## The generating set and the statement -/

/-- **The cell-spoke generating set**: classes of loops that stay inside an
open cell `W ⊆ ℂ` meeting `T` exactly at its puncture `s`, whose punctured
part is homeomorphic to a once-punctured plane, conjugated to the basepoint
along an arbitrary spoke. -/
def CellSpokes (T : Finset ℂ) (x₀ : {z : ℂ // z ∉ (T : Set ℂ)}) :
    Set (FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀) :=
  {g | ∃ s : ℂ, s ∈ T ∧ ∃ W : Set ℂ, IsOpen W ∧ W ∩ (T : Set ℂ) = {s} ∧
    (∃ a : ℂ, Nonempty ({z : ℂ // z ∈ W ∧ z ≠ s} ≃ₜ {w : ℂ // w ≠ a})) ∧
    ∃ (y : {z : ℂ // z ∉ (T : Set ℂ)}) (δ : Path y y),
      (∀ t, (δ t : ℂ) ∈ W) ∧ ∃ p : Path x₀ y, g = spokedClass p δ}

/-- The generation statement at a fixed basepoint: any subgroup containing
the cell-spoke classes contains every loop class. -/
def CellGenAt (T : Finset ℂ) (x₀ : {z : ℂ // z ∉ (T : Set ℂ)}) : Prop :=
  ∀ H : Subgroup (FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀),
    CellSpokes T x₀ ⊆ (H : Set _) →
    ∀ γ : Path x₀ x₀, FundamentalGroup.fromPath (Qmk γ) ∈ H

/-- The generation statement at every basepoint. -/
def CellGen (T : Finset ℂ) : Prop := ∀ x₀, CellGenAt T x₀

/-! ## Base cases -/

/-- Base case `T = ∅`: the fundamental group is trivial. -/
theorem cellGen_empty : CellGen (∅ : Finset ℂ) := by
  intro x₀ H _ γ
  haveI := subsingleton_fundamentalGroup_compl_empty x₀
  have h1 : FundamentalGroup.fromPath (Qmk γ) = 1 := Subsingleton.elim _ _
  rw [h1]
  exact H.one_mem

/-- Base case `T = {a}`: the whole space is itself an admissible cell, so
every loop class is a cell-spoke class with the trivial spoke. -/
theorem cellGen_singleton (a : ℂ) : CellGen ({a} : Finset ℂ) := by
  intro x₀ H hsub γ
  rw [← spokedClass_refl γ]
  apply hsub
  refine ⟨a, Finset.mem_singleton_self a, univ, isOpen_univ, by simp,
    ⟨a, ⟨{ toFun := fun z => ⟨z.1, z.2.2⟩
           invFun := fun w => ⟨w.1, mem_univ _, w.2⟩
           left_inv := fun z => rfl
           right_inv := fun w => rfl
           continuous_toFun := continuous_subtype_val.subtype_mk _
           continuous_invFun := continuous_subtype_val.subtype_mk _ }⟩⟩,
    x₀, γ, fun t => mem_univ _, Path.refl x₀, rfl⟩

/-! ## Generic transport toolkit -/

/-- Path-connectedness transfers along a homeomorphism. -/
theorem pathConnectedSpace_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (φ : A ≃ₜ B) [h : PathConnectedSpace A] :
    PathConnectedSpace B := by
  constructor
  · exact h.nonempty.map φ
  · intro x y
    obtain ⟨γ⟩ := h.joined (φ.symm x) (φ.symm y)
    exact ⟨(γ.map φ.continuous).cast (φ.apply_symm_apply x).symm
      (φ.apply_symm_apply y).symm⟩

/-- Flattening of the nested subtype `{z : ℂ ∖ T // P z}`. -/
def flattenSide (P : ℂ → Prop) (T : Finset ℂ) :
    {z : {z : ℂ // z ∉ (T : Set ℂ)} // P (z : ℂ)}
      ≃ₜ {z : ℂ // P z ∧ z ∉ (T : Set ℂ)} where
  toFun z := ⟨(z.1 : ℂ), z.2, z.1.2⟩
  invFun w := ⟨⟨w.1, w.2.2⟩, w.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-! ## The transported side -/

section Side

variable {P : ℂ → Prop}

/-- The punctures on the `P`-side, transported to the plane by the side
presentation `Φ`. -/
noncomputable def sideFinset (Φ : {z : ℂ // P z} ≃ₜ ℂ) (T : Finset ℂ) :
    Finset ℂ :=
  Set.Finite.toFinset
    (s := ⇑Φ '' (Subtype.val ⁻¹' (T : Set ℂ)))
    ((T.finite_toSet.preimage Subtype.val_injective.injOn).image _)

theorem mem_sideFinset {Φ : {z : ℂ // P z} ≃ₜ ℂ} {T : Finset ℂ} {w : ℂ} :
    w ∈ sideFinset Φ T
      ↔ ∃ z : {z : ℂ // P z}, (z : ℂ) ∈ (T : Set ℂ) ∧ Φ z = w := by
  simp only [sideFinset, Set.Finite.mem_toFinset, Set.mem_image,
    Set.mem_preimage]

theorem sideFinset_card_helper (Φ : {z : ℂ // P z} ≃ₜ ℂ) (T : Finset ℂ) :
    (sideFinset Φ T).card = ((T : Set ℂ) ∩ {z | P z}).ncard := by
  have h0 : (sideFinset Φ T).card
      = (⇑Φ '' (Subtype.val ⁻¹' (T : Set ℂ))).ncard :=
    (Set.ncard_eq_toFinset_card _ _).symm
  have himg : (Subtype.val : {z : ℂ // P z} → ℂ) ''
        ((Subtype.val : {z : ℂ // P z} → ℂ) ⁻¹' (T : Set ℂ))
      = (T : Set ℂ) ∩ {z : ℂ | P z} := by
    ext z
    constructor
    · rintro ⟨u, huT, rfl⟩
      exact ⟨huT, u.2⟩
    · rintro ⟨hzT, hz⟩
      exact ⟨⟨z, hz⟩, hzT, rfl⟩
  rw [h0, Set.ncard_image_of_injective _ Φ.injective,
    ← Set.ncard_image_of_injective _ Subtype.val_injective, himg]

/-- Dropping the punctures beyond the side strictly decreases the count. -/
theorem sideFinset_card_lt (Φ : {z : ℂ // P z} ≃ₜ ℂ) {T : Finset ℂ} {t : ℂ}
    (ht : t ∈ T) (hPt : ¬ P t) : (sideFinset Φ T).card < T.card := by
  rw [sideFinset_card_helper]
  have hsub : (T : Set ℂ) ∩ {z | P z} ⊂ (T : Set ℂ) := by
    refine ⟨inter_subset_left, fun hsup => ?_⟩
    exact hPt (hsup (Finset.mem_coe.mpr ht)).2
  have := Set.ncard_lt_ncard hsub T.finite_toSet
  rwa [Set.ncard_coe_finset] at this

/-- A full side preserves the count. -/
theorem sideFinset_card_eq (Φ : {z : ℂ // P z} ≃ₜ ℂ) {T : Finset ℂ}
    (hall : ∀ t ∈ T, P t) : (sideFinset Φ T).card = T.card := by
  rw [sideFinset_card_helper]
  have : (T : Set ℂ) ∩ {z | P z} = (T : Set ℂ) :=
    inter_eq_left.mpr fun z hz => hall z (Finset.mem_coe.mp hz)
  rw [this, Set.ncard_coe_finset]

theorem sideHomeo_aux₁ (Φ : {z : ℂ // P z} ≃ₜ ℂ) (T : Finset ℂ)
    (z : {z : ℂ // P z ∧ z ∉ (T : Set ℂ)}) :
    Φ ⟨z.1, z.2.1⟩ ∉ ((sideFinset Φ T) : Set ℂ) := by
  intro hmem
  obtain ⟨u, huT, hu⟩ := mem_sideFinset.mp (Finset.mem_coe.mp hmem)
  have huz : (u : ℂ) = z.1 :=
    congrArg Subtype.val (Φ.injective hu)
  exact z.2.2 (huz ▸ huT)

theorem sideHomeo_aux₂ (Φ : {z : ℂ // P z} ≃ₜ ℂ) (T : Finset ℂ)
    (w : {w : ℂ // w ∉ ((sideFinset Φ T) : Set ℂ)}) :
    (Φ.symm (w : ℂ) : ℂ) ∉ (T : Set ℂ) := by
  intro hT
  exact w.2 (Finset.mem_coe.mpr
    (mem_sideFinset.mpr ⟨Φ.symm (w : ℂ), hT, Φ.apply_symm_apply _⟩))

/-- The flat side minus its punctures is homeomorphic to the plane minus
the transported punctures. -/
noncomputable def sideHomeo (Φ : {z : ℂ // P z} ≃ₜ ℂ) (T : Finset ℂ) :
    {z : ℂ // P z ∧ z ∉ (T : Set ℂ)}
      ≃ₜ {w : ℂ // w ∉ ((sideFinset Φ T) : Set ℂ)} where
  toFun z := ⟨Φ ⟨z.1, z.2.1⟩, sideHomeo_aux₁ Φ T z⟩
  invFun w := ⟨(Φ.symm (w : ℂ) : ℂ), (Φ.symm (w : ℂ)).2, sideHomeo_aux₂ Φ T w⟩
  left_inv z := by
    apply Subtype.ext
    change (Φ.symm (Φ ⟨z.1, z.2.1⟩) : ℂ) = z.1
    rw [Φ.symm_apply_apply]
  right_inv w := by
    apply Subtype.ext
    change Φ (Φ.symm w.1) = (w.1 : ℂ)
    rw [Φ.apply_symm_apply]
  continuous_toFun :=
    (Φ.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp
      (Φ.symm.continuous.comp continuous_subtype_val))).subtype_mk _

/-- The inclusion of the flat side into the punctured plane. -/
def sideIncl (P : ℂ → Prop) (T : Finset ℂ) :
    C({z : ℂ // P z ∧ z ∉ (T : Set ℂ)}, {z : ℂ // z ∉ (T : Set ℂ)}) :=
  ⟨fun z => ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-! ## Pulling cells back through the side presentation -/

/-- The pullback of a cell along the side presentation. -/
def sideCell (Φ : {z : ℂ // P z} ≃ₜ ℂ) (Ŵ : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ h : P z, Φ ⟨z, h⟩ ∈ Ŵ}

theorem sideCell_eq_image (Φ : {z : ℂ // P z} ≃ₜ ℂ) (Ŵ : Set ℂ) :
    sideCell Φ Ŵ = Subtype.val '' (⇑Φ ⁻¹' Ŵ) := by
  ext z
  constructor
  · rintro ⟨h, hmem⟩
    exact ⟨⟨z, h⟩, hmem, rfl⟩
  · rintro ⟨u, hmem, rfl⟩
    exact ⟨u.2, hmem⟩

theorem isOpen_sideCell (hPopen : IsOpen {z : ℂ | P z})
    (Φ : {z : ℂ // P z} ≃ₜ ℂ) {Ŵ : Set ℂ} (hŴ : IsOpen Ŵ) :
    IsOpen (sideCell Φ Ŵ) := by
  rw [sideCell_eq_image]
  exact hPopen.isOpenMap_subtype_val _ (hŴ.preimage Φ.continuous)

/-- The pullback cell meets `T` exactly at the pulled-back puncture. -/
theorem sideCell_inter_coe (Φ : {z : ℂ // P z} ≃ₜ ℂ) {T : Finset ℂ}
    {Ŵ : Set ℂ} {ŝ : ℂ}
    (h : Ŵ ∩ ((sideFinset Φ T) : Set ℂ) = {ŝ}) :
    sideCell Φ Ŵ ∩ (T : Set ℂ) = {(Φ.symm ŝ : ℂ)} := by
  have hŝ : ŝ ∈ Ŵ ∩ ((sideFinset Φ T) : Set ℂ) := by
    rw [h]
    exact mem_singleton _
  ext z
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hz, hΦz⟩, hzT⟩
    have hTside : Φ ⟨z, hz⟩ ∈ ((sideFinset Φ T) : Set ℂ) := by
      rw [Finset.mem_coe, mem_sideFinset]
      exact ⟨⟨z, hz⟩, hzT, rfl⟩
    have hmem : Φ ⟨z, hz⟩ ∈ Ŵ ∩ ((sideFinset Φ T) : Set ℂ) := ⟨hΦz, hTside⟩
    rw [h, mem_singleton_iff] at hmem
    have hz' : (⟨z, hz⟩ : {z : ℂ // P z}) = Φ.symm ŝ :=
      Φ.injective (by rw [Φ.apply_symm_apply]; exact hmem)
    exact congrArg Subtype.val hz'
  · rintro rfl
    obtain ⟨u, huT, hu⟩ := mem_sideFinset.mp (Finset.mem_coe.mp hŝ.2)
    have huŝ : u = Φ.symm ŝ :=
      Φ.injective (by rw [Φ.apply_symm_apply]; exact hu)
    refine ⟨⟨(Φ.symm ŝ).2, ?_⟩, ?_⟩
    · change Φ (Φ.symm ŝ) ∈ Ŵ
      rw [Φ.apply_symm_apply]
      exact hŝ.1
    · rw [← huŝ]
      exact huT

/-- The pullback cell's punctured part is homeomorphic to the original
cell's punctured part. -/
noncomputable def sideCellHomeo (Φ : {z : ℂ // P z} ≃ₜ ℂ) (Ŵ : Set ℂ)
    (ŝ : ℂ) :
    {z : ℂ // z ∈ sideCell Φ Ŵ ∧ z ≠ (Φ.symm ŝ : ℂ)}
      ≃ₜ {w : ℂ // w ∈ Ŵ ∧ w ≠ ŝ} where
  toFun z := ⟨Φ ⟨z.1, z.2.1.choose⟩, z.2.1.choose_spec, by
    intro heq
    apply z.2.2
    have hzeq : (⟨z.1, z.2.1.choose⟩ : {z : ℂ // P z}) = Φ.symm ŝ :=
      Φ.injective (by rw [Φ.apply_symm_apply]; exact heq)
    exact congrArg Subtype.val hzeq⟩
  invFun w := ⟨(Φ.symm w.1 : ℂ),
    ⟨⟨(Φ.symm w.1).2, by
        change Φ (Φ.symm w.1) ∈ Ŵ
        rw [Φ.apply_symm_apply]
        exact w.2.1⟩, by
      intro heq
      apply w.2.2
      have h1 : Φ.symm w.1 = Φ.symm ŝ := Subtype.ext heq
      have h2 := congrArg Φ h1
      rwa [Φ.apply_symm_apply, Φ.apply_symm_apply] at h2⟩⟩
  left_inv z := by
    apply Subtype.ext
    change (Φ.symm (Φ ⟨z.1, z.2.1.choose⟩) : ℂ) = z.1
    rw [Φ.symm_apply_apply]
  right_inv w := by
    apply Subtype.ext
    change Φ (Φ.symm w.1) = (w.1 : ℂ)
    rw [Φ.apply_symm_apply]
  continuous_toFun :=
    (Φ.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp
      (Φ.symm.continuous.comp continuous_subtype_val)).subtype_mk _

theorem coe_sideHomeo_symm_mem_sideCell (Φ : {z : ℂ // P z} ≃ₜ ℂ)
    (T : Finset ℂ) {Ŵ : Set ℂ}
    {w : {w : ℂ // w ∉ ((sideFinset Φ T) : Set ℂ)}} (hw : (w : ℂ) ∈ Ŵ) :
    (((sideHomeo Φ T).symm w : {z : ℂ // P z ∧ z ∉ (T : Set ℂ)}) : ℂ)
      ∈ sideCell Φ Ŵ := by
  refine ⟨(Φ.symm (w : ℂ)).2, ?_⟩
  change Φ (Φ.symm (w : ℂ)) ∈ Ŵ
  rw [Φ.apply_symm_apply]
  exact hw

/-! ## The side-transfer engine -/

/-- **Side transfer.**  If the generation statement holds for the
transported side punctures, then any loop staying on the side already lies
in every subgroup containing the cell-spoke classes.  Both the half-plane
sides of the separating split and the global rotation are instances. -/
theorem side_transfer (hPopen : IsOpen {z : ℂ | P z})
    (Φ : {z : ℂ // P z} ≃ₜ ℂ) {T : Finset ℂ}
    (hside : CellGen (sideFinset Φ T))
    {x₀ : {z : ℂ // z ∉ (T : Set ℂ)}} (hx₀P : P (x₀ : ℂ))
    {H : Subgroup (FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀)}
    (hsub : CellSpokes T x₀ ⊆ (H : Set _))
    (δ : Path x₀ x₀) (hδ : ∀ t, P ((δ t : ℂ))) :
    FundamentalGroup.fromPath (Qmk δ) ∈ H := by
  classical
  set Ψ := sideHomeo Φ T with hΨdef
  set ι := sideIncl P T with hιdef
  -- the flat-side basepoint and the corestricted loop
  set x₀' : {z : ℂ // P z ∧ z ∉ (T : Set ℂ)} := ⟨(x₀ : ℂ), hx₀P, x₀.2⟩
    with hx₀'def
  set δ' : Path x₀' x₀' :=
    { toFun := fun t => ⟨(δ t : ℂ), hδ t, (δ t).2⟩
      continuous_toFun := by fun_prop
      source' := by
        apply Subtype.ext
        change (δ 0 : ℂ) = ((x₀ : {z : ℂ // z ∉ (T : Set ℂ)}) : ℂ)
        rw [δ.source]
      target' := by
        apply Subtype.ext
        change (δ 1 : ℂ) = ((x₀ : {z : ℂ // z ∉ (T : Set ℂ)}) : ℂ)
        rw [δ.target] } with hδ'def
  -- the connecting homomorphism and the pulled-back subgroup
  set e := pi1MulEquivOfHomeomorph Ψ x₀' with hedef
  set f : FundamentalGroup {w : ℂ // w ∉ ((sideFinset Φ T) : Set ℂ)} (Ψ x₀')
      →* FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀ :=
    (FundamentalGroup.mapOfEq ι rfl).comp e.symm.toMonoidHom with hfdef
  have hsubhat : CellSpokes (sideFinset Φ T) (Ψ x₀') ⊆ ((H.comap f) : Set _) := by
    rintro g ⟨ŝ, hs1T, Ŵ, hŴo, hWT1, ⟨â, ⟨φ₁⟩⟩, ŷ, δ₁, hd1W, p₁, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    -- the pulled-back puncture
    have hŝmem : ŝ ∈ Ŵ ∩ ((sideFinset Φ T) : Set ℂ) := by
      rw [hWT1]
      exact mem_singleton _
    obtain ⟨u, huT, hu⟩ := mem_sideFinset.mp (Finset.mem_coe.mp hŝmem.2)
    have huŝ : u = Φ.symm ŝ :=
      Φ.injective (by rw [Φ.apply_symm_apply]; exact hu)
    have hsT : (Φ.symm ŝ : ℂ) ∈ T := by
      rw [← huŝ]
      exact Finset.mem_coe.mp huT
    -- the pulled-back loop and spoke in the flat side
    set y' := Ψ.symm ŷ with hy'def
    set δd : Path y' y' := δ₁.map Ψ.symm.continuous with hδddef
    set pd : Path x₀' y' :=
      { toFun := fun t => Ψ.symm (p₁ t)
        continuous_toFun := Ψ.symm.continuous.comp p₁.continuous
        source' := by
          show Ψ.symm (p₁ 0) = x₀'
          rw [p₁.source]
          exact Ψ.symm_apply_apply x₀'
        target' := by
          show Ψ.symm (p₁ 1) = y'
          rw [p₁.target] } with hpddef
    -- membership of the pushed-forward generator
    have hgen : spokedClass (pd.map ι.continuous) (δd.map ι.continuous) ∈ H := by
      apply hsub
      refine ⟨(Φ.symm ŝ : ℂ), hsT, sideCell Φ Ŵ, isOpen_sideCell hPopen Φ hŴo,
        sideCell_inter_coe Φ hWT1, ⟨â, ⟨(sideCellHomeo Φ Ŵ ŝ).trans φ₁⟩⟩,
        ι y', δd.map ι.continuous, ?_, pd.map ι.continuous, rfl⟩
      intro t
      exact coe_sideHomeo_symm_mem_sideCell Φ T (hd1W t)
    -- the key computation: `f` sends the side generator to the pushed one
    have hA : e (spokedClass pd δd) = spokedClass p₁ δ₁ := by
      have h1 : e (spokedClass pd δd)
          = spokedClass (pd.map Ψ.continuous) (δd.map Ψ.continuous) := by
        change FundamentalGroup.mapOfEq (⟨⇑Ψ, Ψ.continuous⟩ :
            C({z : ℂ // P z ∧ z ∉ (T : Set ℂ)},
              {w : ℂ // w ∉ ((sideFinset Φ T) : Set ℂ)})) rfl
            (spokedClass pd δd) = _
        exact mapOfEq_spokedClass _ pd δd
      rw [h1]
      refine spokedClass_of_eq (Ψ.apply_symm_apply ŷ) _ _ _ _
        (fun t => ?_) (fun t => ?_)
      · change Ψ (Ψ.symm (p₁ t)) = p₁ t
        exact Ψ.apply_symm_apply _
      · change Ψ (Ψ.symm (δ₁ t)) = δ₁ t
        exact Ψ.apply_symm_apply _
    have hB : e.symm (spokedClass p₁ δ₁) = spokedClass pd δd := by
      rw [← hA, MulEquiv.symm_apply_apply]
    change (FundamentalGroup.mapOfEq ι rfl) (e.symm (spokedClass p₁ δ₁)) ∈ H
    rw [hB, mapOfEq_spokedClass ι pd δd]
    exact hgen
  -- run the side statement on the transported loop
  have hmain := hside (Ψ x₀') (H.comap f) hsubhat (δ'.map Ψ.continuous)
  rw [Subgroup.mem_comap] at hmain
  -- identify `f` of the transported class with the original class
  have h1 : e (FundamentalGroup.fromPath (Qmk δ'))
      = FundamentalGroup.fromPath (Qmk (δ'.map Ψ.continuous)) := by
    change FundamentalGroup.mapOfEq (⟨⇑Ψ, Ψ.continuous⟩ :
        C({z : ℂ // P z ∧ z ∉ (T : Set ℂ)},
          {w : ℂ // w ∉ ((sideFinset Φ T) : Set ℂ)})) rfl
        (FundamentalGroup.fromPath (Qmk δ')) = _
    rw [FundamentalGroup.mapOfEq_apply, Path.cast_rfl_rfl]
  have h2 : f (FundamentalGroup.fromPath (Qmk (δ'.map Ψ.continuous)))
      = FundamentalGroup.fromPath (Qmk δ) := by
    change (FundamentalGroup.mapOfEq ι rfl)
        (e.symm (FundamentalGroup.fromPath (Qmk (δ'.map Ψ.continuous))))
      = FundamentalGroup.fromPath (Qmk δ)
    rw [← h1, MulEquiv.symm_apply_apply, FundamentalGroup.mapOfEq_apply,
      Path.cast_rfl_rfl]
    refine congrArg (fun r : Path x₀ x₀ =>
      FundamentalGroup.fromPath (Qmk r)) ?_
    ext t
    rfl
  rwa [h2] at hmain

end Side

/-! ## Rebasing -/

/-- The generation statement transfers along a path between basepoints:
spokes absorb the conjugating path. -/
theorem cellGenAt_rebase {T : Finset ℂ} {x₀ y₀ : {z : ℂ // z ∉ (T : Set ℂ)}}
    (τ : Path x₀ y₀) (h : CellGenAt T y₀) : CellGenAt T x₀ := by
  intro H hsub γ
  set e := FundamentalGroup.fundamentalGroupMulEquivOfPath τ with hedef
  have hsub' : CellSpokes T y₀ ⊆ ((H.comap e.symm.toMonoidHom) : Set _) := by
    rintro g ⟨s, hsT, W, hWo, hWT, hpres, y, δ, hδW, q, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change e.symm (spokedClass q δ) ∈ H
    have hkey : e.symm (spokedClass q δ) = spokedClass (τ.trans q) δ := by
      rw [spokedClass_eq_transport, spokedClass_eq_transport,
        Path.trans_symm, fundamentalGroupMulEquivOfPath_trans,
        fundamentalGroupMulEquivOfPath_symm_eq]
    rw [hkey]
    exact hsub ⟨s, hsT, W, hWo, hWT, hpres, y, δ, hδW, τ.trans q, rfl⟩
  have hmain := h (H.comap e.symm.toMonoidHom) hsub'
    (τ.symm.trans (γ.trans τ))
  rw [Subgroup.mem_comap] at hmain
  have hmain' : e.symm (FundamentalGroup.fromPath
      (Qmk (τ.symm.trans (γ.trans τ)))) ∈ H := hmain
  have hid : e.symm (FundamentalGroup.fromPath (Qmk (τ.symm.trans (γ.trans τ))))
      = FundamentalGroup.fromPath (Qmk γ) := by
    rw [← fundamentalGroupMulEquivOfPath_fromPath τ γ,
      MulEquiv.symm_apply_apply]
  rwa [hid] at hmain'

/-! ## The separating-line step -/

/-- The core induction step under the assumption that not all punctures
share the same real part. -/
private theorem step_core {T : Finset ℂ}
    (hre : ∃ s₁ ∈ T, ∃ s₂ ∈ T, s₁.re ≠ s₂.re)
    (IH : ∀ T' : Finset ℂ, T'.card < T.card → CellGen T') :
    CellGen T := by
  classical
  -- the projection levels and the split
  set A : Finset ℝ := T.image Complex.re with hAdef
  have hA2 : 2 ≤ A.card := by
    obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := hre
    exact Finset.one_lt_card.mpr
      ⟨s₁.re, Finset.mem_image_of_mem _ hs₁,
        s₂.re, Finset.mem_image_of_mem _ hs₂, hne⟩
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  set a := A.min' hAne with hadef
  have hAerase : (A.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (A.min'_mem hAne)]
    omega
  set b := (A.erase a).min' hAerase with hbdef
  have hbA : b ∈ A := Finset.mem_of_mem_erase ((A.erase a).min'_mem hAerase)
  have hab : a < b :=
    lt_of_le_of_ne (A.min'_le _ hbA)
      (Ne.symm (Finset.ne_of_mem_erase ((A.erase a).min'_mem hAerase)))
  have hsplit : ∀ r ∈ A, r = a ∨ b ≤ r := by
    intro r hr
    by_cases hra : r = a
    · exact Or.inl hra
    · exact Or.inr ((A.erase a).min'_le _ (Finset.mem_erase.mpr ⟨hra, hr⟩))
  set c₁ := a + (b - a) / 3 with hc₁def
  set c₂ := a + 2 * (b - a) / 3 with hc₂def
  have hac₁ : a < c₁ := by
    rw [hc₁def]
    linarith
  have hc₁c₂ : c₁ < c₂ := by
    rw [hc₁def, hc₂def]
    linarith
  have hc₂b : c₂ < b := by
    rw [hc₂def]
    linarith
  -- the strip is puncture free
  have hfree : ∀ s : ℂ, s ∈ T → ¬(c₁ < s.re ∧ s.re < c₂) := by
    rintro s hs ⟨h1, h2⟩
    rcases hsplit s.re (Finset.mem_image_of_mem _ hs) with h | h
    · rw [h] at h1
      linarith
    · linarith
  -- witnesses on both sides of the strip
  obtain ⟨sa, hsa, hsare⟩ : ∃ s ∈ T, s.re = a := by
    obtain ⟨s, hs, hsre⟩ := Finset.mem_image.mp (A.min'_mem hAne)
    exact ⟨s, hs, hsre⟩
  obtain ⟨sb, hsb, hsbre⟩ : ∃ s ∈ T, s.re = b := by
    obtain ⟨s, hs, hsre⟩ := Finset.mem_image.mp hbA
    exact ⟨s, hs, hsre⟩
  -- the side statements from the induction hypothesis
  have hUside : CellGen (sideFinset (halfPlaneHomeo c₂) T) := by
    refine IH _ (sideFinset_card_lt _ hsb ?_)
    rw [hsbre]
    exact not_lt.mpr (le_of_lt hc₂b)
  have hVside : CellGen (sideFinset (halfPlaneHomeoGT c₁) T) := by
    refine IH _ (sideFinset_card_lt _ hsa ?_)
    rw [hsare]
    exact not_lt.mpr (le_of_lt hac₁)
  -- path-connectivity facts
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact_mod_cast Nat.one_lt_two
  -- the strip basepoint
  set m : ℝ := (c₁ + c₂) / 2 with hmdef
  have hm₁ : c₁ < m := by
    rw [hmdef]
    linarith
  have hm₂ : m < c₂ := by
    rw [hmdef]
    linarith
  have hmT : ((m : ℂ) : ℂ) ∉ (T : Set ℂ) := by
    intro hmem
    refine hfree _ (Finset.mem_coe.mp hmem) ?_
    rw [Complex.ofReal_re]
    exact ⟨hm₁, hm₂⟩
  set y₀ : {z : ℂ // z ∉ (T : Set ℂ)} := ⟨(m : ℂ), hmT⟩ with hy₀def
  -- the strip-basepoint statement via the two-open split
  have hstrip : CellGenAt T y₀ := by
    intro H hsub γ
    set U : Set {z : ℂ // z ∉ (T : Set ℂ)} := {z | (z : ℂ).re < c₂} with hUdef
    set V : Set {z : ℂ // z ∉ (T : Set ℂ)} := {z | c₁ < (z : ℂ).re} with hVdef
    have hUo : IsOpen U :=
      isOpen_lt (Complex.continuous_re.comp continuous_subtype_val)
        continuous_const
    have hVo : IsOpen V :=
      isOpen_lt continuous_const
        (Complex.continuous_re.comp continuous_subtype_val)
    have hcov : ∀ z : {z : ℂ // z ∉ (T : Set ℂ)}, z ∈ U ∪ V := by
      intro z
      by_cases h : (z : ℂ).re < c₂
      · exact Or.inl h
      · refine Or.inr ?_
        push Not at h
        change c₁ < (z : ℂ).re
        linarith
    -- path-connectivity of the sides
    have hUpc : IsPathConnected U := by
      rw [isPathConnected_iff_pathConnectedSpace]
      haveI hpcU : PathConnectedSpace
          {w : ℂ // w ∉ ((sideFinset (halfPlaneHomeo c₂) T) : Set ℂ)} := by
        have hc := ((sideFinset (halfPlaneHomeo c₂) T).finite_toSet.countable)
        have hc := hc.isPathConnected_compl_of_one_lt_rank hrank
        rw [isPathConnected_iff_pathConnectedSpace] at hc
        exact hc
      haveI hflat : PathConnectedSpace
          {z : ℂ // z.re < c₂ ∧ z ∉ (T : Set ℂ)} :=
        pathConnectedSpace_of_homeomorph (sideHomeo (halfPlaneHomeo c₂) T).symm
      exact pathConnectedSpace_of_homeomorph
        (flattenSide (fun z : ℂ => z.re < c₂) T).symm
    have hVpc : IsPathConnected V := by
      rw [isPathConnected_iff_pathConnectedSpace]
      haveI hpcV : PathConnectedSpace
          {w : ℂ // w ∉ ((sideFinset (halfPlaneHomeoGT c₁) T) : Set ℂ)} := by
        have hc := ((sideFinset (halfPlaneHomeoGT c₁) T).finite_toSet.countable)
        have hc := hc.isPathConnected_compl_of_one_lt_rank hrank
        rw [isPathConnected_iff_pathConnectedSpace] at hc
        exact hc
      haveI hflat : PathConnectedSpace
          {z : ℂ // c₁ < z.re ∧ z ∉ (T : Set ℂ)} :=
        pathConnectedSpace_of_homeomorph
          (sideHomeo (halfPlaneHomeoGT c₁) T).symm
      exact pathConnectedSpace_of_homeomorph
        (flattenSide (fun z : ℂ => c₁ < z.re) T).symm
    have hy₀U : y₀ ∈ U := by
      change ((m : ℂ) : ℂ).re < c₂
      rw [Complex.ofReal_re]
      exact hm₂
    have hy₀V : y₀ ∈ V := by
      change c₁ < ((m : ℂ) : ℂ).re
      rw [Complex.ofReal_re]
      exact hm₁
    -- the strip is path connected: straight segments
    have hUVpc : IsPathConnected (U ∩ V) := by
      have hcombo : ∀ (u v r : ℝ), c₁ < u → u < c₂ → c₁ < v → v < c₂ →
          0 ≤ r → r ≤ 1 → c₁ < (1 - r) * u + r * v ∧ (1 - r) * u + r * v < c₂ := by
        intro u v r hu1 hu2 hv1 hv2 hr0 hr1
        constructor
        · rcases eq_or_lt_of_le hr1 with h | h
          · rw [h]
            simpa using hv1
          · nlinarith
        · rcases eq_or_lt_of_le hr1 with h | h
          · rw [h]
            simpa using hv2
          · nlinarith
      refine ⟨y₀, ⟨hy₀U, hy₀V⟩, ?_⟩
      rintro z ⟨hzU, hzV⟩
      -- the straight segment from y₀ to z
      have hseg : ∀ t : unitInterval,
          (1 - (t : ℝ)) • ((y₀ : ℂ)) + (t : ℝ) • ((z : ℂ)) ∉ (T : Set ℂ) := by
        intro t hmem
        have hre : ((1 - (t : ℝ)) • ((y₀ : ℂ)) + (t : ℝ) • ((z : ℂ))).re
            = (1 - (t : ℝ)) * ((y₀ : ℂ)).re + (t : ℝ) * ((z : ℂ)).re := by
          simp [Complex.add_re]
        have hbounds := hcombo ((y₀ : ℂ)).re ((z : ℂ)).re (t : ℝ)
          hy₀V hy₀U hzV hzU t.2.1 t.2.2
        refine hfree _ (Finset.mem_coe.mp hmem) ?_
        rw [hre]
        exact hbounds
      refine ⟨{ toFun := fun t =>
          ⟨(1 - (t : ℝ)) • ((y₀ : ℂ)) + (t : ℝ) • ((z : ℂ)), hseg t⟩
                continuous_toFun := by fun_prop
                source' := by
                  apply Subtype.ext
                  change (1 - (0 : ℝ)) • ((y₀ : ℂ)) + (0 : ℝ) • ((z : ℂ))
                    = (y₀ : ℂ)
                  simp
                target' := by
                  apply Subtype.ext
                  change (1 - (1 : ℝ)) • ((y₀ : ℂ)) + (1 : ℝ) • ((z : ℂ))
                    = (z : ℂ)
                  simp }, ?_⟩
      intro t
      have hre : ((1 - (t : ℝ)) • ((y₀ : ℂ)) + (t : ℝ) • ((z : ℂ))).re
          = (1 - (t : ℝ)) * ((y₀ : ℂ)).re + (t : ℝ) * ((z : ℂ)).re := by
        simp [Complex.add_re]
      have hbounds := hcombo ((y₀ : ℂ)).re ((z : ℂ)).re (t : ℝ)
        hy₀V hy₀U hzV hzU t.2.1 t.2.2
      constructor
      · change ((1 - (t : ℝ)) • ((y₀ : ℂ)) + (t : ℝ) • ((z : ℂ))).re < c₂
        rw [hre]
        exact hbounds.2
      · change c₁ < ((1 - (t : ℝ)) • ((y₀ : ℂ)) + (t : ℝ) • ((z : ℂ))).re
        rw [hre]
        exact hbounds.1
    refine fromPath_mem_of_two_open hUo hVo hcov hUpc hVpc hUVpc
      ⟨hy₀U, hy₀V⟩ H ?_ ?_ γ
    · intro δ hδU
      exact side_transfer (isOpen_lt Complex.continuous_re continuous_const)
        (halfPlaneHomeo c₂) hUside hy₀U hsub δ hδU
    · intro δ hδV
      exact side_transfer (isOpen_lt continuous_const Complex.continuous_re)
        (halfPlaneHomeoGT c₁) hVside hy₀V hsub δ hδV
  -- rebase to an arbitrary basepoint
  intro x₀
  have hpc : IsPathConnected ((T : Set ℂ)ᶜ) :=
    (T.finite_toSet.countable).isPathConnected_compl_of_one_lt_rank hrank
  haveI : PathConnectedSpace {z : ℂ // z ∉ (T : Set ℂ)} := by
    rw [isPathConnected_iff_pathConnectedSpace] at hpc
    exact hpc
  obtain ⟨τ⟩ := PathConnectedSpace.joined x₀ y₀
  exact cellGenAt_rebase τ hstrip

/-! ## The rotation, for configurations with constant real part -/

/-- Multiplication by `I` as a side presentation of the whole plane. -/
noncomputable def rotationHomeo : {z : ℂ // (fun _ : ℂ => True) z} ≃ₜ ℂ where
  toFun z := Complex.I * z.1
  invFun w := ⟨-Complex.I * w, trivial⟩
  left_inv z := by
    apply Subtype.ext
    change -Complex.I * (Complex.I * z.1) = z.1
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  right_inv w := by
    change Complex.I * (-Complex.I * w) = w
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  continuous_toFun := continuous_const.mul continuous_subtype_val
  continuous_invFun := (continuous_const.mul continuous_id).subtype_mk _

/-! ## Assembly -/

private theorem cellGen_aux : ∀ (n : ℕ) (T : Finset ℂ), T.card ≤ n → CellGen T := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    rw [hT0]
    exact cellGen_empty
  | succ n ih =>
    intro T hT
    by_cases hsmall : T.card ≤ n
    · exact ih T hsmall
    · have hcard : T.card = n + 1 := le_antisymm hT (by omega)
      by_cases h1 : T.card ≤ 1
      · interval_cases h : T.card
        · rw [Finset.card_eq_zero.mp h]
          exact cellGen_empty
        · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp h
          exact cellGen_singleton c
      · push Not at h1
        have IH' : ∀ T' : Finset ℂ, T'.card < T.card → CellGen T' := by
          intro T' hT'
          exact ih T' (by omega)
        by_cases hre : ∃ s₁ ∈ T, ∃ s₂ ∈ T, s₁.re ≠ s₂.re
        · exact step_core hre IH'
        · -- all punctures share a real part: rotate by 90°
          push Not at hre
          obtain ⟨s₁, hs₁, s₂, hs₂, hs12⟩ := Finset.one_lt_card.mp h1
          have hcardrot : (sideFinset rotationHomeo T).card = T.card :=
            sideFinset_card_eq _ (fun _ _ => trivial)
          have hrot : ∃ t₁ ∈ sideFinset rotationHomeo T,
              ∃ t₂ ∈ sideFinset rotationHomeo T, t₁.re ≠ t₂.re := by
            refine ⟨Complex.I * s₁, ?_, Complex.I * s₂, ?_, ?_⟩
            · exact mem_sideFinset.mpr ⟨⟨s₁, trivial⟩, Finset.mem_coe.mpr hs₁, rfl⟩
            · exact mem_sideFinset.mpr ⟨⟨s₂, trivial⟩, Finset.mem_coe.mpr hs₂, rfl⟩
            · have hre12 : s₁.re = s₂.re := hre s₁ hs₁ s₂ hs₂
              have him : s₁.im ≠ s₂.im := by
                intro him
                exact hs12 (Complex.ext hre12 him)
              simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
                zero_mul, one_mul, zero_sub]
              exact fun h => him (neg_injective h)
          have hrotgen : CellGen (sideFinset rotationHomeo T) := by
            refine step_core hrot ?_
            intro T' hT'
            refine IH' T' ?_
            rwa [hcardrot] at hT'
          intro x₀ H hsub γ
          exact side_transfer (by rw [Set.setOf_true]; exact isOpen_univ)
            rotationHomeo hrotgen trivial hsub γ (fun t => trivial)

/-- **G3/G4 headline (Layer A).**  For every finite puncture set and every
basepoint, any subgroup of `π₁(ℂ ∖ T, x₀)` containing all cell-spoke
classes contains every loop class. -/
theorem fromPath_mem_of_cellSpokes_subset (T : Finset ℂ)
    (x₀ : {z : ℂ // z ∉ (T : Set ℂ)})
    (H : Subgroup (FundamentalGroup {z : ℂ // z ∉ (T : Set ℂ)} x₀))
    (hsub : CellSpokes T x₀ ⊆ (H : Set _)) (γ : Path x₀ x₀) :
    FundamentalGroup.fromPath (Qmk γ) ∈ H :=
  cellGen_aux T.card T le_rfl x₀ H hsub γ

end Jacobians.Topology
