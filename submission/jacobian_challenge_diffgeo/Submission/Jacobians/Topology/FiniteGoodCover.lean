/-
# π₁ is finitely generated over a finite simply-connected good cover (T-FG engine)

Goal B of `docs/planning/HANDOVER_PARALLEL_ACCOUNT.md` (S2 lane), engine half.
The consumer is `moduleFinite_H1_of_fundamentalGroup_fg`
(`Jacobians/RiemannSurface/HomologyGeneration.lean`, H-lane), which feeds the
discreteness half of `AX_PeriodCycleBasis` from
`[Group.FG (FundamentalGroup X x₀)]`.

**Main result** (`fundamentalGroup_fg_of_goodCover`): if a path-connected
space `X` admits a *finite simply-connected good cover* — finitely many open
sets covering `X`, each simply connected, with path-connected pairwise
intersections — then `π₁(X, x₀)` is finitely generated, with an explicit
generating family indexed by `Fin N × E × E` where `E = Option (Fin N × Fin N)`
(so at most `N·(N²+1)²` generators).

**Proof.** Lebesgue-subdivide a loop `γ` into arcs each inside one cover set
(`exists_lebesgue_subdivision_iUnion`).  Conjugate each arc by *spokes* from
the basepoint to the junctions and telescope: the loop class lies in any
subgroup containing all conjugated-arc classes (`fromPath_concat_conj_mem`,
the membership form of the telescope, which avoids word bookkeeping).  Each
junction lies in the intersection of the two adjacent cover sets; routing its
spoke through a *fixed* anchor point of that intersection (path-connectedness
of intersections) makes the conjugated-arc class depend only on the *indices*
of the cover sets involved — paths with common endpoints inside a simply
connected set are homotopic (`homotopic_of_forall_mem_isSimplyConnected`) —
so every factor is one of the finitely many `coverGen` generators.

The telescoping/Lebesgue method follows the two-open van Kampen development
ported from Kirov (`KirovDolbeault/VanKampen.lean`, Apache 2.0; cf. tom Dieck,
*Algebraic Topology* §2.7–2.8).  The `N`-set generalization, the membership
form of the telescope, and the finite-generator bookkeeping are new here.
Mathlib-only imports.

What this file does *not* prove: that a compact surface *has* a finite
simply-connected good cover (classically: cover by geodesically convex balls;
Mathlib has no Riemannian convexity at our pin).  That existence statement is
the re-isolated named gap — see `docs/planning/GOODCOVER_BLOCKER.md`.
-/
import Mathlib

namespace Jacobians.Topology

open unitInterval Fin Set

/-- Local shorthand for `Path.Homotopic.Quotient.mk` (the structure namespace
below shadows a plain `open`). -/
local notation "Qmk" => Path.Homotopic.Quotient.mk
local notation "Qtrans" => Path.Homotopic.Quotient.trans
local notation "Qsymm" => Path.Homotopic.Quotient.symm
local notation "Qrefl" => Path.Homotopic.Quotient.refl

variable {X : Type*} [TopologicalSpace X]

/-! ### Path classes inside a simply connected subset -/

/-- A loop lying entirely in a simply connected set `W` is nullhomotopic in the
ambient space. -/
theorem nullhomotopic_of_forall_mem_isSimplyConnected {W : Set X}
    (hW : IsSimplyConnected W) {o : X} (L : Path o o) (hL : ∀ t, L t ∈ W) :
    L.Homotopic (Path.refl o) := by
  obtain ⟨-, hforall⟩ := isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hW
  obtain ⟨F, -⟩ := hforall o L hL
  exact ⟨F⟩

/-- **Path-class uniqueness in a simply connected subset.**  Two paths with the
same endpoints, both lying in a simply connected set `W`, are homotopic in the
ambient space. -/
theorem homotopic_of_forall_mem_isSimplyConnected {W : Set X}
    (hW : IsSimplyConnected W) {x y : X} {α β : Path x y}
    (hα : ∀ t, α t ∈ W) (hβ : ∀ t, β t ∈ W) : α.Homotopic β := by
  have hloop : (α.trans β.symm).Homotopic (Path.refl x) := by
    refine nullhomotopic_of_forall_mem_isSimplyConnected hW _ fun t => ?_
    have ht : (α.trans β.symm) t ∈ range (α.trans β.symm) := ⟨t, rfl⟩
    rw [Path.trans_range, Path.symm_range] at ht
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]; exact hα s
    · rw [← hs]; exact hβ s
  -- cancel `β.symm` on the right in the quotient
  have h1 : Qtrans (Qmk α) (Qsymm (Qmk β)) = Qrefl x := by
    rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.eq]
    exact hloop
  have h2 := congrArg (fun z => Path.Homotopic.Quotient.trans z (Qmk β)) h1
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] at h2
  exact Path.Homotopic.Quotient.eq.mp h2

/-! ### Lebesgue subdivision over an arbitrary open cover -/

/-- **Lebesgue subdivision of a path over any open cover.**  For a continuous
`γ : I → X` and an open cover `U : ι → Set X` of `X`, there is a uniform
subdivision `t k = k/(n+1)` of `[0,1]` such that each closed piece
`γ '' [t kᵢ, t kᵢ₊₁]` lies inside a single `U i`.  (`ι`-indexed generalization
of the two-set version in the ported `KirovDolbeault/VanKampen.lean`.) -/
theorem exists_lebesgue_subdivision_iUnion {ι : Type*} {γ : I → X}
    (hγ : Continuous γ) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x, ∃ i, x ∈ U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I), t 0 = 0 ∧ t (last n) = 1 ∧
      ∀ k : Fin n, ∃ i, γ '' Set.uIcc (t k.castSucc) (t k.succ) ⊆ U i := by
  set c : ι → Set I := fun i => γ ⁻¹' U i with hc
  have hcopen : ∀ i, IsOpen (c i) := fun i => (hU i).preimage hγ
  have hccov : (Set.univ : Set I) ⊆ ⋃ i, c i := by
    intro s _
    obtain ⟨i, hi⟩ := hcov (γ s)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hcopen hccov
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, fun k => projIcc 0 1 zero_le_one ((k : ℝ) / (m + 1)), by simp, ?_, ?_⟩
  · have hval : (((last (m + 1) : Fin (m + 2)) : ℕ) : ℝ) / (m + 1) = 1 := by
      rw [Fin.val_last]; push_cast; field_simp
    simp only
    rw [hval, Set.projIcc_right]; rfl
  · intro k
    set N : ℝ := (m : ℝ) + 1 with hN
    have hNpos : 0 < N := by positivity
    have hval_of : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        ((projIcc (0 : ℝ) 1 zero_le_one x : ℝ)) = x := by
      intro x h1 h2
      rw [Set.coe_projIcc, min_eq_right h2, max_eq_right h1]
    have hk_top : ((k.succ : Fin (m + 2)) : ℕ) ≤ m + 1 := by
      rw [Fin.val_succ]; have := k.isLt; omega
    have hcs0 : (0 : ℝ) ≤ (k.castSucc : ℝ) / N := by positivity
    have hsucc1 : (k.succ : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos, hN]; exact_mod_cast hk_top
    have hkle : (k.castSucc : ℝ) / N ≤ (k.succ : ℝ) / N := by
      have h1 : ((k.castSucc : Fin (m + 2)) : ℕ) ≤ ((k.succ : Fin (m + 2)) : ℕ) := by
        rw [Fin.val_castSucc, Fin.val_succ]; omega
      gcongr
    have hcs1 : (k.castSucc : ℝ) / N ≤ 1 := le_trans hkle hsucc1
    have hsucc0 : (0 : ℝ) ≤ (k.succ : ℝ) / N := by positivity
    set a : I := projIcc 0 1 zero_le_one ((k.castSucc : ℝ) / N) with ha
    set b : I := projIcc 0 1 zero_le_one ((k.succ : ℝ) / N) with hb
    have hab : a ≤ b := by
      rw [ha, hb, ← Subtype.coe_le_coe, hval_of _ hcs0 hcs1, hval_of _ hsucc0 hsucc1]
      exact hkle
    obtain ⟨i, hi⟩ := hball a (Set.mem_univ a)
    refine ⟨i, ?_⟩
    rw [Set.uIcc_of_le hab]
    rintro _ ⟨s, hs, rfl⟩
    refine hi ?_
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by
      rw [sub_nonneg]; exact_mod_cast hs.1)]
    have hsb : (s : ℝ) ≤ (b : ℝ) := by exact_mod_cast hs.2
    have hba : (b : ℝ) - (a : ℝ) = 1 / N := by
      rw [ha, hb, hval_of _ hcs0 hcs1, hval_of _ hsucc0 hsucc1, div_sub_div_same]
      congr 1
      push_cast [Fin.val_castSucc, Fin.val_succ]
      ring
    calc (s : ℝ) - (a : ℝ) ≤ (b : ℝ) - (a : ℝ) := by linarith
      _ = 1 / N := hba
      _ < δ := by rw [hN] at hm ⊢; exact hm

/-! ### The membership telescope -/

/-- `fromPath` sends `trans` to (reversed) multiplication: in `End`,
`f * g = g ≫ f` and `≫` is `trans` on path classes. -/
theorem fromPath_trans {o : X} (P Q : Path.Homotopic.Quotient o o) :
    FundamentalGroup.fromPath (P.trans Q) =
      FundamentalGroup.fromPath Q * FundamentalGroup.fromPath P :=
  rfl

theorem fromPath_refl {o : X} :
    FundamentalGroup.fromPath (Qrefl o) = (1 : FundamentalGroup X o) :=
  rfl

/-- Three-term cancellation `p⁻¹ · (p · W) ≃ W` at the path level. -/
theorem homotopic_symm_trans_cancel {o y z : X} (p : Path o y) (W : Path y z) :
    (p.symm.trans (p.trans W)).Homotopic W :=
  ((Path.Homotopic.trans_assoc p.symm p W).symm).trans
    (((Path.Homotopic.symm_trans p).hcomp (Path.Homotopic.refl W)).trans
      (Path.Homotopic.refl_trans W))

/-- **Membership telescope.**  A loop presented as a concatenation of arcs `F`
with junctions `q`, conjugated by spokes `c`, lies in any subgroup containing
every conjugated-arc class `c kᵢ · F k · c kᵢ₊₁⁻¹`.  (Membership form of the
telescoping in the ported `KirovDolbeault/VanKampen.lean`.) -/
theorem fromPath_concat_conj_mem {o : X} (H : Subgroup (FundamentalGroup X o)) :
    ∀ {n : ℕ} (q : Fin (n + 1) → X) (c : (k : Fin (n + 1)) → Path o (q k))
      (F : (k : Fin n) → Path (q k.castSucc) (q k.succ)),
      (∀ k : Fin n, FundamentalGroup.fromPath
        (Qmk ((c k.castSucc).trans ((F k).trans (c k.succ).symm))) ∈ H) →
      FundamentalGroup.fromPath
        (Qmk ((c 0).trans ((Path.concat q F).trans (c (last n)).symm))) ∈ H := by
  intro n
  induction n with
  | zero =>
    intro q c F _
    -- `concat` of zero arcs is `refl (q 0)` and `last 0 = 0`: the loop is
    -- `c 0 · refl · (c 0)⁻¹`, whose class is `1`.
    have hpath : ((c 0).trans ((Path.concat q F).trans (c (last 0)).symm)).Homotopic
        (Path.refl o) := by
      rw [Path.concat_zero]
      exact ((Path.Homotopic.refl _).hcomp (Path.Homotopic.refl_trans _)).trans
        (Path.Homotopic.trans_symm _)
    have hone : Qmk ((c 0).trans ((Path.concat q F).trans (c (last 0)).symm)) = Qrefl o := by
      rw [← Path.Homotopic.Quotient.mk_refl]
      exact Path.Homotopic.Quotient.eq.mpr hpath
    rw [hone, fromPath_refl]
    exact one_mem H
  | succ n ih =>
    intro q c F hfac
    have hinner := ih (fun j => q j.castSucc) (fun k => c k.castSucc)
      (fun k => F k.castSucc) (fun k => hfac k.castSucc)
    have hlast := hfac (last n)
    -- split off the last arc, with the inner concatenation over the beta-form
    -- junction family (defeq to `Path.concat_succ`'s composition form)
    have hsplit : Path.concat q F =
        (Path.concat (fun j : Fin (n + 1) => q j.castSucc)
          (fun k => F k.castSucc)).trans (F (last n)) :=
      Path.concat_succ q F
    -- the conjugated whole is path-homotopic to (inner factor) · (last factor):
    -- both sides reassociate to `c 0 · (concat' · (F last · c top⁻¹))`, with the
    -- middle `c_m⁻¹ · c_m` cancelling on the right-hand side
    have hLR : ((c 0).trans ((Path.concat q F).trans (c (last (n + 1))).symm)).Homotopic
        (((c 0).trans ((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans (c (last n).castSucc).symm)).trans
          ((c (last n).castSucc).trans ((F (last n)).trans (c (last (n + 1))).symm))) := by
      rw [hsplit]
      -- left side ≃ the common right-associated form `c 0 · (concat' · (F last · c top⁻¹))`
      have hL : ((c 0).trans (((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans (F (last n))).trans
              (c (last (n + 1))).symm)).Homotopic
          ((c 0).trans ((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans
              ((F (last n)).trans (c (last (n + 1))).symm))) :=
        (Path.Homotopic.refl (c 0)).hcomp (Path.Homotopic.trans_assoc _ _ _)
      -- right side ≃ the same form, cancelling `c_m⁻¹ · c_m`
      have hR1 : (((c 0).trans ((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans (c (last n).castSucc).symm)).trans
            ((c (last n).castSucc).trans
              ((F (last n)).trans (c (last (n + 1))).symm))).Homotopic
          ((c 0).trans (((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans (c (last n).castSucc).symm).trans
            ((c (last n).castSucc).trans
              ((F (last n)).trans (c (last (n + 1))).symm)))) :=
        Path.Homotopic.trans_assoc _ _ _
      have hR2 : ((((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans (c (last n).castSucc).symm).trans
            ((c (last n).castSucc).trans
              ((F (last n)).trans (c (last (n + 1))).symm)))).Homotopic
          ((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans ((c (last n).castSucc).symm.trans
            ((c (last n).castSucc).trans
              ((F (last n)).trans (c (last (n + 1))).symm)))) :=
        Path.Homotopic.trans_assoc _ _ _
      have hR3 : ((c (last n).castSucc).symm.trans
            ((c (last n).castSucc).trans
              ((F (last n)).trans (c (last (n + 1))).symm))).Homotopic
          ((F (last n)).trans (c (last (n + 1))).symm) :=
        homotopic_symm_trans_cancel _ _
      exact hL.trans (hR1.trans ((Path.Homotopic.refl (c 0)).hcomp
        (hR2.trans ((Path.Homotopic.refl _).hcomp hR3)))).symm
    have key : Qmk ((c 0).trans ((Path.concat q F).trans (c (last (n + 1))).symm)) =
        Qtrans
          (Qmk ((c 0).trans ((Path.concat (fun j : Fin (n + 1) => q j.castSucc)
            (fun k => F k.castSucc)).trans (c (last n).castSucc).symm)))
          (Qmk ((c (last n).castSucc).trans ((F (last n)).trans (c (last (n + 1))).symm))) :=
      (Path.Homotopic.Quotient.eq.mpr hLR).trans
        (Path.Homotopic.Quotient.mk_trans _ _)
    rw [key, fromPath_trans]
    exact mul_mem hlast hinner

/-! ### Finite simply-connected good covers -/

/-- A **finite simply-connected good cover**: finitely many open sets covering
`X`, each simply connected, all pairwise intersections path-connected (when
nonempty).  Classically every compact manifold has one (cover by geodesically
convex balls); Mathlib has no such existence statement at our pin, so the
existence for compact Riemann surfaces is tracked as a named gap
(`docs/planning/GOODCOVER_BLOCKER.md`). -/
structure SimplyConnectedGoodCover (X : Type*) [TopologicalSpace X] where
  /-- number of cover sets -/
  n : ℕ
  /-- the cover sets -/
  U : Fin n → Set X
  isOpen : ∀ i, IsOpen (U i)
  covers : ∀ x : X, ∃ i, x ∈ U i
  simplyConnected : ∀ i, IsSimplyConnected (U i)
  inter_pathConnected : ∀ i j, (U i ∩ U j).Nonempty → IsPathConnected (U i ∩ U j)

namespace SimplyConnectedGoodCover

section Generators

variable (C : SimplyConnectedGoodCover X) (x₀ : X)

/-- Anchor points: `none` is the basepoint `x₀`; `some (a, b)` is a chosen
point of `U a ∩ U b` (junk value `x₀` if the intersection is empty). -/
noncomputable def anchor : Option (Fin C.n × Fin C.n) → X
  | none => x₀
  | some (a, b) =>
    open Classical in
    if h : (C.U a ∩ C.U b).Nonempty then h.choose else x₀

@[simp] theorem anchor_none : C.anchor x₀ none = x₀ := rfl

theorem anchor_mem {a b : Fin C.n} (h : (C.U a ∩ C.U b).Nonempty) :
    C.anchor x₀ (some (a, b)) ∈ C.U a ∩ C.U b := by
  rw [anchor]
  rw [dif_pos h]
  exact h.choose_spec

/-- Re-association of a conjugated factor: splitting each spoke as
(anchor spoke) · (local detour) and regrouping the detours into the middle. -/
theorem mk_conj_reassoc {y₀ p₁ p₂ y₁ y₂ : X} (s₁ : Path y₀ p₁) (d₁ : Path p₁ y₁)
    (Fk : Path y₁ y₂) (s₂ : Path y₀ p₂) (d₂ : Path p₂ y₂) :
    Qmk ((s₁.trans d₁).trans (Fk.trans (s₂.trans d₂).symm)) =
      Qmk (s₁.trans ((d₁.trans (Fk.trans d₂.symm)).trans s₂.symm)) := by
  rw [Path.trans_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

variable [PathConnectedSpace X]

/-- A chosen path from the basepoint to each anchor (the constant path for the
basepoint itself). -/
noncomputable def anchorSpoke : ∀ e : Option (Fin C.n × Fin C.n), Path x₀ (C.anchor x₀ e)
  | none => Path.refl x₀
  | some (a, b) => PathConnectedSpace.somePath x₀ (C.anchor x₀ (some (a, b)))

@[simp] theorem anchorSpoke_none : C.anchorSpoke x₀ none = Path.refl x₀ := rfl

/-- The canonical generators of `π₁(X, x₀)`: for a cover index `b` and two
anchors lying in `U b`, the class of (spoke to first anchor) · (a chosen path
between the anchors inside `U b`) · (spoke to second anchor)⁻¹.  Junk value
`1` if an anchor misses `U b`. -/
noncomputable def coverGen (b : Fin C.n) (e₁ e₂ : Option (Fin C.n × Fin C.n)) :
    FundamentalGroup X x₀ :=
  open Classical in
  if h : C.anchor x₀ e₁ ∈ C.U b ∧ C.anchor x₀ e₂ ∈ C.U b then
    FundamentalGroup.fromPath (Qmk ((C.anchorSpoke x₀ e₁).trans
      ((((C.simplyConnected b).isPathConnected.joinedIn _ h.1 _ h.2).somePath).trans
        (C.anchorSpoke x₀ e₂).symm)))
  else 1

/-- **Factor classification.**  Any loop of the form
`spoke e₁ · μ · spoke e₂⁻¹` with the middle path `μ` inside `U b` represents
the canonical generator `coverGen b e₁ e₂`: inside the simply connected `U b`
the class of `μ` rel endpoints is unique. -/
theorem fromPath_eq_coverGen {b : Fin C.n} {e₁ e₂ : Option (Fin C.n × Fin C.n)}
    (μ : Path (C.anchor x₀ e₁) (C.anchor x₀ e₂)) (hμ : ∀ s, μ s ∈ C.U b) :
    FundamentalGroup.fromPath (Qmk ((C.anchorSpoke x₀ e₁).trans
      (μ.trans (C.anchorSpoke x₀ e₂).symm))) = C.coverGen x₀ b e₁ e₂ := by
  have h : C.anchor x₀ e₁ ∈ C.U b ∧ C.anchor x₀ e₂ ∈ C.U b := by
    constructor
    · have := hμ 0; rwa [μ.source] at this
    · have := hμ 1; rwa [μ.target] at this
  rw [coverGen, dif_pos h]
  have hhom : μ.Homotopic
      (((C.simplyConnected b).isPathConnected.joinedIn _ h.1 _ h.2).somePath) :=
    homotopic_of_forall_mem_isSimplyConnected (C.simplyConnected b) hμ
      (JoinedIn.somePath_mem _)
  have hmk : Qmk ((C.anchorSpoke x₀ e₁).trans (μ.trans (C.anchorSpoke x₀ e₂).symm)) =
      Qmk ((C.anchorSpoke x₀ e₁).trans
        ((((C.simplyConnected b).isPathConnected.joinedIn _ h.1 _ h.2).somePath).trans
          (C.anchorSpoke x₀ e₂).symm)) :=
    Path.Homotopic.Quotient.eq.mpr
      ((Path.Homotopic.refl _).hcomp (hhom.hcomp (Path.Homotopic.refl _)))
  rw [hmk]

end Generators

/-! ### The main theorem -/

/-- **π₁ of a space with a finite simply-connected good cover is finitely
generated** (T-FG engine).  The generating set is the family `coverGen`,
indexed by `Fin C.n × E × E` with `E = Option (Fin C.n × Fin C.n)`. -/
theorem fundamentalGroup_fg_of_goodCover (C : SimplyConnectedGoodCover X)
    [PathConnectedSpace X] (x₀ : X) : Group.FG (FundamentalGroup X x₀) := by
  classical
  rw [Group.fg_def, Subgroup.fg_iff]
  refine ⟨Set.range (fun z : Fin C.n × Option (Fin C.n × Fin C.n) × Option (Fin C.n × Fin C.n)
    => C.coverGen x₀ z.1 z.2.1 z.2.2), ?_, Set.finite_range _⟩
  set S : Set (FundamentalGroup X x₀) :=
    Set.range (fun z : Fin C.n × Option (Fin C.n × Fin C.n) × Option (Fin C.n × Fin C.n)
      => C.coverGen x₀ z.1 z.2.1 z.2.2) with hS
  rw [Subgroup.eq_top_iff']
  intro g
  -- present `g` as the class of an actual loop
  obtain ⟨γ, hγ⟩ : ∃ γ : Path x₀ x₀, FundamentalGroup.fromPath (Qmk γ) = g :=
    ⟨(FundamentalGroup.toPath g).out,
      congrArg FundamentalGroup.fromPath (Quotient.out_eq _)⟩
  -- Lebesgue subdivision of `γ` along the cover
  obtain ⟨N, t, ht0, htl, hsub⟩ :=
    exists_lebesgue_subdivision_iUnion γ.continuous (fun i => C.isOpen i) C.covers
  choose ch hch using hsub
  -- junctions and arcs
  set q : Fin (N + 1) → X := ⇑γ ∘ t with hq
  set F : (k : Fin N) → Path (q k.castSucc) (q k.succ) :=
    fun k => γ.subpath (t k.castSucc) (t k.succ) with hF
  have hrangeF : ∀ k : Fin N, range (F k) ⊆ C.U (ch k) := by
    intro k
    show range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ C.U (ch k)
    rw [Path.range_subpath]
    exact hch k
  have h0 : q 0 = x₀ := by rw [hq]; show γ (t 0) = x₀; rw [ht0]; exact γ.source
  have hl : q (last N) = x₀ := by rw [hq]; show γ (t (last N)) = x₀; rw [htl]; exact γ.target
  -- junction data: an anchor index, and a detour from the anchor to the
  -- junction, lying in every adjacent chart; the two end junctions use the
  -- basepoint anchor with a constant detour.
  have hjunc : ∀ j : Fin (N + 1),
      ∃ (e : Option (Fin C.n × Fin C.n)) (d : Path (C.anchor x₀ e) (q j)),
        (∀ k : Fin N, j = k.castSucc →
          C.anchor x₀ e ∈ C.U (ch k) ∧ ∀ s, d s ∈ C.U (ch k)) ∧
        (∀ k : Fin N, j = k.succ →
          C.anchor x₀ e ∈ C.U (ch k) ∧ ∀ s, d s ∈ C.U (ch k)) ∧
        ((j = 0 ∨ j = last N) → e = none ∧ ∀ s, d s = x₀) := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨none, (Path.refl x₀).cast rfl h0, ?_, ?_, fun _ => ⟨rfl, fun s => rfl⟩⟩
      · intro k hk
        have hx₀ : x₀ ∈ C.U (ch k) := by
          have := hrangeF k (F k).source_mem_range
          rwa [← hk, h0] at this
        exact ⟨hx₀, fun s => hx₀⟩
      · intro k hk
        exact absurd hk.symm (Fin.succ_ne_zero k)
    by_cases hjl : j = last N
    · subst hjl
      refine ⟨none, (Path.refl x₀).cast rfl hl, ?_, ?_, fun _ => ⟨rfl, fun s => rfl⟩⟩
      · intro k hk
        exact absurd hk.symm (Fin.castSucc_lt_last k).ne
      · intro k hk
        have hx₀ : x₀ ∈ C.U (ch k) := by
          have := hrangeF k (F k).target_mem_range
          rwa [← hk, hl] at this
        exact ⟨hx₀, fun s => hx₀⟩
    -- interior junction: it lies in both adjacent charts
    · have hjpos : 0 < (j : ℕ) := by
        rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
        · exact absurd (Fin.ext h) hj0
        · exact h
      have hjlt : (j : ℕ) < N := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp j.isLt) with h | h
        · exact h
        · exact absurd (Fin.ext (h.trans (Fin.val_last N).symm)) hjl
      set kL : Fin N := ⟨(j : ℕ) - 1, by omega⟩ with hkL
      set kR : Fin N := ⟨(j : ℕ), hjlt⟩ with hkR
      have hkLj : kL.succ = j := by
        apply Fin.ext
        simp only [Fin.val_succ, hkL]
        omega
      have hkRj : kR.castSucc = j := by
        apply Fin.ext
        simp only [Fin.val_castSucc, hkR]
      have hqL : q j ∈ C.U (ch kL) := by
        have := hrangeF kL (F kL).target_mem_range
        rwa [hkLj] at this
      have hqR : q j ∈ C.U (ch kR) := by
        have := hrangeF kR (F kR).source_mem_range
        rwa [hkRj] at this
      have hne : (C.U (ch kL) ∩ C.U (ch kR)).Nonempty := ⟨q j, hqL, hqR⟩
      have hanch := C.anchor_mem x₀ hne
      have hjoin : JoinedIn (C.U (ch kL) ∩ C.U (ch kR))
          (C.anchor x₀ (some (ch kL, ch kR))) (q j) :=
        (C.inter_pathConnected _ _ hne).joinedIn _ hanch _ ⟨hqL, hqR⟩
      refine ⟨some (ch kL, ch kR), hjoin.somePath, ?_, ?_, ?_⟩
      · intro k hk
        have hkkR : k = kR := Fin.castSucc_injective N (by rw [← hk, hkRj])
        subst hkkR
        exact ⟨hanch.2, fun s => (hjoin.somePath_mem s).2⟩
      · intro k hk
        have hkkL : k = kL := Fin.succ_injective N (by rw [← hk, hkLj])
        subst hkkL
        exact ⟨hanch.1, fun s => (hjoin.somePath_mem s).1⟩
      · intro h
        rcases h with h | h
        · exact absurd h hj0
        · exact absurd h hjl
  choose E d hpropL hpropR hpropEnd using hjunc
  -- the spokes
  set c : (j : Fin (N + 1)) → Path x₀ (q j) :=
    fun j => (C.anchorSpoke x₀ (E j)).trans (d j) with hc
  -- every conjugated-arc class is a canonical generator
  have hfac : ∀ k : Fin N, FundamentalGroup.fromPath
      (Qmk ((c k.castSucc).trans ((F k).trans (c k.succ).symm))) ∈ Subgroup.closure S := by
    intro k
    have hL := hpropL k.castSucc k rfl
    have hR := hpropR k.succ k rfl
    have hreassoc : Qmk ((c k.castSucc).trans ((F k).trans (c k.succ).symm)) =
        Qmk ((C.anchorSpoke x₀ (E k.castSucc)).trans
          (((d k.castSucc).trans ((F k).trans (d k.succ).symm)).trans
            (C.anchorSpoke x₀ (E k.succ)).symm)) := by
      rw [hc]
      exact mk_conj_reassoc _ _ _ _ _
    have hμ : ∀ s, ((d k.castSucc).trans ((F k).trans (d k.succ).symm)) s ∈ C.U (ch k) := by
      have hsubrange : range ((d k.castSucc).trans ((F k).trans (d k.succ).symm))
          ⊆ C.U (ch k) := by
        rw [Path.trans_range, Path.trans_range, Path.symm_range]
        refine Set.union_subset ?_ (Set.union_subset (hrangeF k) ?_)
        · rintro _ ⟨s, rfl⟩
          exact hL.2 s
        · rintro _ ⟨s, rfl⟩
          exact hR.2 s
      exact fun s => hsubrange ⟨s, rfl⟩
    rw [hreassoc, C.fromPath_eq_coverGen x₀ _ hμ]
    exact Subgroup.subset_closure ⟨(ch k, E k.castSucc, E k.succ), rfl⟩
  -- telescope: the conjugated concatenation lies in the closure
  have htele := fromPath_concat_conj_mem (Subgroup.closure S) q c F hfac
  -- the end spokes are constant
  have hspconst : ∀ (j : Fin (N + 1)), E j = none →
      ∀ u : I, (C.anchorSpoke x₀ (E j)) u = x₀ := by
    intro j hj u
    have := congrArg (fun e => (C.anchorSpoke x₀ e : I → X) u) hj
    simpa using this
  have hcconst : ∀ (j : Fin (N + 1)), j = 0 ∨ j = last N → ∀ s : I, (c j) s = x₀ := by
    intro j hj s
    have hEj := hpropEnd j hj
    show ((C.anchorSpoke x₀ (E j)).trans (d j)) s = x₀
    rw [Path.trans_apply]
    split_ifs
    · exact hspconst j hEj.1 _
    · exact hEj.2 _
  have hc0 : c 0 = (Path.refl x₀).cast rfl h0 := by
    ext s
    rw [Path.cast_coe]
    show (c 0) s = Path.refl x₀ s
    rw [Path.refl_apply]
    exact hcconst 0 (Or.inl rfl) s
  have hcl : c (last N) = (Path.refl x₀).cast rfl hl := by
    ext s
    rw [Path.cast_coe]
    show (c (last N)) s = Path.refl x₀ s
    rw [Path.refl_apply]
    exact hcconst (last N) (Or.inr rfl) s
  -- assemble: the conjugated concatenation is homotopic to `γ` itself
  have hsubγ : γ.subpath (t 0) (t (last N)) = γ.cast h0 hl := by
    ext s
    show (⇑γ ∘ Icc.convexComb (t 0) (t (last N))) s = γ s
    rw [Function.comp_apply, ht0, htl, Icc.convexComb_zero_one]
  have hcs : (Path.concat q F).Homotopic (γ.subpath (t 0) (t (last N))) :=
    Path.Homotopic.concat_subpath γ t
  have hΛγ : ((c 0).trans ((Path.concat q F).trans (c (last N)).symm)).Homotopic γ := by
    rw [hc0, hcl]
    have step1 : (((Path.refl x₀).cast rfl h0).trans
        ((Path.concat q F).trans (((Path.refl x₀).cast rfl hl).symm))).Homotopic
        (((Path.refl x₀).cast rfl h0).trans
          ((γ.cast h0 hl).trans (((Path.refl x₀).cast rfl hl).symm))) :=
      (Path.Homotopic.refl _).hcomp ((hsubγ ▸ hcs).hcomp (Path.Homotopic.refl _))
    have step2 : ((Path.refl x₀).cast rfl h0).trans
        ((γ.cast h0 hl).trans (((Path.refl x₀).cast rfl hl).symm)) =
        (Path.refl x₀).trans (γ.trans (Path.refl x₀).symm) := by
      ext s
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs with hs
      · rfl
      · rw [Path.trans_apply, Path.trans_apply]
        split_ifs with hs'
        · rfl
        · rfl
    have step3 : ((Path.refl x₀).trans (γ.trans (Path.refl x₀).symm)).Homotopic γ := by
      rw [Path.refl_symm]
      exact (Path.Homotopic.refl_trans _).trans (Path.Homotopic.trans_refl γ)
    rw [step2] at step1
    exact step1.trans step3
  have hmkeq : Qmk ((c 0).trans ((Path.concat q F).trans (c (last N)).symm)) = Qmk γ :=
    Path.Homotopic.Quotient.eq.mpr hΛγ
  rw [hmkeq, hγ] at htele
  exact htele

end SimplyConnectedGoodCover

end Jacobians.Topology
