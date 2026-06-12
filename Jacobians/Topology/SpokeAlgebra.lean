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

end Jacobians.Topology
