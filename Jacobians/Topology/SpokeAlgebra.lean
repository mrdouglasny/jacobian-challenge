/-
# Spoke algebra — conjugated loop classes under transport, rebasing, and maps

Issue #171 / `docs/planning/B1_GENERATION_ROUTE.md` rungs **G3/G4**
(toolkit).  The generation induction manipulates *spoked classes*: the
class in `π₁(X, x₀)` of `p · γ · p⁻¹` for a loop `γ` at `y` and a spoke
`p : x₀ ⇝ y`.  This file provides the complete algebra these classes obey:

* `spokedClass_eq_transport` — a spoked class is the basepoint transport
  (`fundamentalGroupMulEquivOfPath p.symm`) of the loop class;
* `fundamentalGroupMulEquivOfPath_trans` — transport is functorial in the
  path (composition law), `..._refl` — and unital;
* `spokedClass_refl` — the trivial spoke gives the plain loop class;
* `spokedClass_congr` / `mk_trans_trans_symm_cancel` — spoked classes
  depend only on the homotopy class of the spoke, and a back-and-forth
  `τ · (τ⁻¹ · p)` spoke collapses to `p`;
* `spokedClass_trans` — a composite spoke peels into a re-spoked loop;
* `mapOfEq_spokedClass` — naturality under continuous maps.

Mathlib-only mathematical content (imports `PunctureLoops` for the
transport evaluation formula `fundamentalGroupMulEquivOfPath_fromPath`).
-/
import Jacobians.Topology.PunctureLoops

namespace Jacobians.Topology

open CategoryTheory

local notation "Qmk" => Path.Homotopic.Quotient.mk

variable {X : Type*} [TopologicalSpace X]

/-- **The spoked class**: the element of `π₁(X, x₀)` represented by the loop
`γ` at `y`, conjugated back to the basepoint along the spoke `p`. -/
noncomputable def spokedClass {x₀ y : X} (p : Path x₀ y) (γ : Path y y) :
    FundamentalGroup X x₀ :=
  FundamentalGroup.fromPath (Qmk (p.trans (γ.trans p.symm)))

/-- A spoked class is the basepoint transport of the loop class along the
reversed spoke. -/
theorem spokedClass_eq_transport {x₀ y : X} (p : Path x₀ y) (γ : Path y y) :
    spokedClass p γ
      = FundamentalGroup.fundamentalGroupMulEquivOfPath p.symm
          (FundamentalGroup.fromPath (Qmk γ)) := by
  rw [fundamentalGroupMulEquivOfPath_fromPath p.symm γ, Path.symm_symm]
  rfl

/-- **Composition law for basepoint transport**: transporting along a
concatenation is transporting along the pieces in order. -/
theorem fundamentalGroupMulEquivOfPath_trans {x y z : X} (α : Path x y)
    (β : Path y z) (g : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (α.trans β) g
      = FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (FundamentalGroup.fundamentalGroupMulEquivOfPath α g) := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  have hg : g = FundamentalGroup.fromPath (Qmk γ) := hγ.symm
  rw [hg, fundamentalGroupMulEquivOfPath_fromPath,
    fundamentalGroupMulEquivOfPath_fromPath, fundamentalGroupMulEquivOfPath_fromPath]
  show (Qmk ((α.trans β).symm.trans (γ.trans (α.trans β)))
      : Path.Homotopic.Quotient z z)
    = Qmk (β.symm.trans ((α.symm.trans (γ.trans α)).trans β))
  simp [Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.trans_assoc]

/-- **Transport along the constant path is the identity.** -/
theorem fundamentalGroupMulEquivOfPath_refl {x : X} (g : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (Path.refl x) g = g := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  have hg : g = FundamentalGroup.fromPath (Qmk γ) := hγ.symm
  rw [hg, fundamentalGroupMulEquivOfPath_fromPath]
  show (Qmk ((Path.refl x).symm.trans (γ.trans (Path.refl x)))
      : Path.Homotopic.Quotient x x)
    = Qmk γ
  simp [Path.refl_symm, Path.Homotopic.Quotient.mk_trans]

/-- Basepoint transport depends only on the homotopy class of the path. -/
theorem fundamentalGroupMulEquivOfPath_congr {x y : X} {α α' : Path x y}
    (h : Qmk α = Qmk α') (g : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath α g
      = FundamentalGroup.fundamentalGroupMulEquivOfPath α' g := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  have hg : g = FundamentalGroup.fromPath (Qmk γ) := hγ.symm
  have hsymm : Qmk α.symm = Qmk α'.symm :=
    Quotient.sound (Path.Homotopic.symm₂ (Quotient.exact h))
  rw [hg, fundamentalGroupMulEquivOfPath_fromPath,
    fundamentalGroupMulEquivOfPath_fromPath]
  show FundamentalGroup.fromPath (Qmk (α.symm.trans (γ.trans α)))
    = FundamentalGroup.fromPath (Qmk (α'.symm.trans (γ.trans α')))
  rw [Path.Homotopic.Quotient.mk_trans α.symm (γ.trans α),
    Path.Homotopic.Quotient.mk_trans γ α,
    Path.Homotopic.Quotient.mk_trans α'.symm (γ.trans α'),
    Path.Homotopic.Quotient.mk_trans γ α', h, hsymm]

/-- The inverse of basepoint transport is transport along the reversed
path. -/
theorem fundamentalGroupMulEquivOfPath_symm_eq {x y : X} (τ : Path x y)
    (g : FundamentalGroup X y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath τ).symm g
      = FundamentalGroup.fundamentalGroupMulEquivOfPath τ.symm g := by
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath τ).injective
  rw [MulEquiv.apply_symm_apply, ← fundamentalGroupMulEquivOfPath_trans,
    fundamentalGroupMulEquivOfPath_congr
      (Quotient.sound (Path.Homotopic.symm_trans τ)) g,
    fundamentalGroupMulEquivOfPath_refl]

/-- The trivial spoke gives the plain loop class. -/
theorem spokedClass_refl {x₀ : X} (γ : Path x₀ x₀) :
    spokedClass (Path.refl x₀) γ = FundamentalGroup.fromPath (Qmk γ) := by
  rw [spokedClass_eq_transport, Path.refl_symm,
    fundamentalGroupMulEquivOfPath_refl]

/-- Spoked classes depend only on the homotopy class of the spoke. -/
theorem spokedClass_congr {x₀ y : X} {p p' : Path x₀ y} (γ : Path y y)
    (h : Qmk p = Qmk p') : spokedClass p γ = spokedClass p' γ := by
  have hsymm : Qmk p.symm = Qmk p'.symm :=
    Quotient.sound (Path.Homotopic.symm₂ (Quotient.exact h))
  show FundamentalGroup.fromPath (Qmk (p.trans (γ.trans p.symm)))
    = FundamentalGroup.fromPath (Qmk (p'.trans (γ.trans p'.symm)))
  rw [Path.Homotopic.Quotient.mk_trans p (γ.trans p.symm),
    Path.Homotopic.Quotient.mk_trans γ p.symm,
    Path.Homotopic.Quotient.mk_trans p' (γ.trans p'.symm),
    Path.Homotopic.Quotient.mk_trans γ p'.symm, h, hsymm]

/-- Quotient-level associativity of path concatenation. -/
theorem mk_trans_assoc {w x y z : X} (a : Path w x) (b : Path x y)
    (c : Path y z) :
    Qmk ((a.trans b).trans c) = Qmk (a.trans (b.trans c)) :=
  Quotient.sound (Path.Homotopic.trans_assoc a b c)

/-- A back-and-forth spoke collapses: `τ · (τ⁻¹ · p)` is homotopic to `p`. -/
theorem mk_trans_trans_symm_cancel {x₀ y₀ y : X} (τ : Path x₀ y₀)
    (p : Path x₀ y) :
    Qmk (τ.trans (τ.symm.trans p)) = Qmk p := by
  rw [← mk_trans_assoc]
  have h1 : Qmk (τ.trans τ.symm) = Qmk (Path.refl x₀) :=
    Quotient.sound ⟨(Path.Homotopy.reflTransSymm τ).symm⟩
  rw [Path.Homotopic.Quotient.mk_trans (τ.trans τ.symm) p, h1,
    ← Path.Homotopic.Quotient.mk_trans]
  exact Quotient.sound ⟨Path.Homotopy.reflTrans p⟩

/-- **Peeling a composite spoke**: spoking along `p · q` is spoking along
`p` after re-spoking the loop along `q`. -/
theorem spokedClass_trans {x₀ y z : X} (p : Path x₀ y) (q : Path y z)
    (γ : Path z z) :
    spokedClass (p.trans q) γ = spokedClass p (q.trans (γ.trans q.symm)) := by
  rw [spokedClass_eq_transport, spokedClass_eq_transport]
  have hin : FundamentalGroup.fromPath (Qmk (q.trans (γ.trans q.symm)))
      = FundamentalGroup.fundamentalGroupMulEquivOfPath q.symm
          (FundamentalGroup.fromPath (Qmk γ)) :=
    spokedClass_eq_transport q γ
  rw [hin, Path.trans_symm, fundamentalGroupMulEquivOfPath_trans]

/-- **Naturality**: a continuous map sends spoked classes to spoked classes
of the image data. -/
theorem mapOfEq_spokedClass {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    {x₀ y : X} (p : Path x₀ y) (γ : Path y y) :
    FundamentalGroup.mapOfEq f rfl (spokedClass p γ)
      = spokedClass (p.map f.continuous) (γ.map f.continuous) := by
  show FundamentalGroup.mapOfEq f rfl (FundamentalGroup.fromPath
      (Qmk (p.trans (γ.trans p.symm)))) = _
  rw [FundamentalGroup.mapOfEq_apply, Path.cast_rfl_rfl, Path.map_trans,
    Path.map_trans, ← Path.map_symm]
  rfl

/-- Multiplication in the fundamental group is reverse concatenation of
representatives. -/
theorem fromPath_mul {x₀ : X} (a b : Path x₀ x₀) :
    FundamentalGroup.fromPath (Qmk a) * FundamentalGroup.fromPath (Qmk b)
      = FundamentalGroup.fromPath (Qmk (b.trans a)) :=
  rfl

/-- The constant loop represents the identity. -/
theorem fromPath_refl_eq_one {x₀ : X} :
    FundamentalGroup.fromPath (Qmk (Path.refl x₀)) = 1 :=
  (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk x₀)).symm

/-- The reversed loop represents the inverse. -/
theorem fromPath_symm_eq_inv {x₀ : X} (p : Path x₀ x₀) :
    FundamentalGroup.fromPath (Qmk p.symm)
      = (FundamentalGroup.fromPath (Qmk p))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [fromPath_mul]
  have h : Qmk (p.trans p.symm) = Qmk (Path.refl x₀) :=
    Quotient.sound ⟨(Path.Homotopy.reflTransSymm p).symm⟩
  rw [h, fromPath_refl_eq_one]

/-- **Spoking by a loop is conjugation** by the loop's class. -/
theorem spokedClass_loop_conj {x₀ : X} (w σ : Path x₀ x₀) :
    spokedClass w σ
      = (FundamentalGroup.fromPath (Qmk w))⁻¹
          * FundamentalGroup.fromPath (Qmk σ)
          * FundamentalGroup.fromPath (Qmk w) := by
  rw [← fromPath_symm_eq_inv, fromPath_mul, fromPath_mul]
  rfl

/-- Spoked classes of pointwise-equal data agree, across a propositional
identification of the loop's basepoint. -/
theorem spokedClass_of_eq {x₀ y y' : X} (h : y = y') (p : Path x₀ y)
    (p' : Path x₀ y') (γ : Path y y) (γ' : Path y' y')
    (hp : ∀ t, p t = p' t) (hγ : ∀ t, γ t = γ' t) :
    spokedClass p γ = spokedClass p' γ' := by
  subst h
  have hpe : p = p' := by ext t; exact hp t
  have hγe : γ = γ' := by ext t; exact hγ t
  rw [hpe, hγe]

end Jacobians.Topology
