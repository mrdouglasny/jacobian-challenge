/-
# Genus-doubling counterexample to categoricity of Buzzard's 24

*Local commentary file — gitignored, NOT part of the Lake build root.*
Compile standalone with:  `lake env lean docs/categoricity/GenusDoublingCounterexample.lean`

## What this shows

Buzzard's challenge (`Jacobians/Challenge.lean`) pins `genus X : ℕ` by a single
property, `genus_eq_zero_iff_homeo` — which constrains only its **vanishing
locus**. Nothing equates `genus X` with the topological genus for `genus ≥ 1`.

So the map `n ↦ 2n`, which preserves "= 0", yields a *second* model of the whole
specification: take

* `genus₂ X := 2 * genus X`
* `Jacobian₂ X := Jacobian X × Jacobian X`   (a complex torus of dimension `2g`)
* `ofCurve₂ := diagonal of ofCurve`           (injective, holomorphic, `↦ 0`)
* `pushforward₂ / pullback₂ := componentwise`, `degree₂ := degree`.

Every one of Buzzard's 24 requirements holds for this model (proved below), yet
`Jacobian₂ X` is a `2g`-dimensional torus — **not** isomorphic to the genuine
`g`-dimensional Jacobian when `g > 0`. Hence the 24, *as literally stated*, do
**not** categorically determine the Jacobian; the hole is the under-specification
of `genus`.

The chart model here is `ModelProd (Fin g → ℂ) (Fin g → ℂ)`, a `2g`-dimensional
ℂ-vector space (`finrank` certified below, = `genus₂ X`), canonically isomorphic
to Buzzard's literal `Fin (genus₂ X) → ℂ`. Re-coordinatising the charts to the
literal model is a routine linear change of coordinates and does not affect the
mathematical content (the dimension is genuinely `2g`).

See `docs/categoricity/CATEGORICITY_24_VS_ALBANESE.md` for the surrounding discussion
(and why pinning `genus` to the true genus does *not* by itself restore
categoricity — that needs the Albanese universal property).
-/
import Jacobians.Challenge

open scoped Manifold ContDiff Topology

namespace GenusDoublingCounterexample

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The doubled genus and the doubled object -/

/-- The "doubled genus". Differs from `genus X` whenever `genus X > 0`, yet
satisfies Buzzard's only genus axiom (`genus_eq_zero_iff_homeo`). -/
noncomputable abbrev genus₂ (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  2 * genus X

/-- The doubled "Jacobian": the square of the genuine Jacobian. A complex torus
of complex dimension `2 * genus X`. -/
abbrev Jacobian₂ (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  Jacobian X × Jacobian X

/-- The product model space, of complex dimension `2 * genus X`. -/
noncomputable abbrev I₂ (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :=
  (𝓘(ℂ, Fin (genus X) → ℂ)).prod 𝓘(ℂ, Fin (genus X) → ℂ)

/-! ## Buzzard's seven typeclass instances, all inherited from the product -/

noncomputable example : AddCommGroup (Jacobian₂ X) := inferInstance
noncomputable example : TopologicalSpace (Jacobian₂ X) := inferInstance
noncomputable example : T2Space (Jacobian₂ X) := inferInstance
noncomputable example : CompactSpace (Jacobian₂ X) := inferInstance
noncomputable example : ConnectedSpace (Jacobian₂ X) := inferInstance
noncomputable example : ChartedSpace (ModelProd (Fin (genus X) → ℂ) (Fin (genus X) → ℂ)) (Jacobian₂ X) :=
  inferInstance
noncomputable example : IsManifold (I₂ X) ω (Jacobian₂ X) := inferInstance
noncomputable example : LieAddGroup (I₂ X) ω (Jacobian₂ X) := inferInstance

/-- **Dimension certification.** The chart model `ModelProd (Fin g→ℂ)(Fin g→ℂ)`
has complex dimension `genus₂ X = 2 * genus X` — genuinely twice the dimension of
the real Jacobian. This is what makes `Jacobian₂ X` a *different object*. -/
theorem finrank_model_eq_genus₂ :
    Module.finrank ℂ ((Fin (genus X) → ℂ) × (Fin (genus X) → ℂ)) = genus₂ X := by
  simp only [genus₂, Module.finrank_prod, Module.finrank_fin_fun]
  ring

/-! ## `genus_eq_zero_iff_homeo` — survives the doubling -/

theorem genus₂_eq_zero_iff_homeo :
    genus₂ X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  have h : genus₂ X = 0 ↔ genus X = 0 := by
    simp only [genus₂]; omega
  rw [h, genus_eq_zero_iff_homeo]

/-! ## The Abel–Jacobi map: the diagonal of `ofCurve` -/

/-- The doubled Abel–Jacobi map `x ↦ (ofCurve P x, ofCurve P x)`. -/
noncomputable def ofCurve₂ (P : X) : X → Jacobian₂ X :=
  fun x => (Jacobian.ofCurve P x, Jacobian.ofCurve P x)

theorem ofCurve₂_self (P : X) : ofCurve₂ P P = 0 :=
  Prod.ext (Jacobian.ofCurve_self P) (Jacobian.ofCurve_self P)

theorem ofCurve₂_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ) (I₂ X) ω (ofCurve₂ P) :=
  (Jacobian.ofCurve_contMDiff P).prodMk (Jacobian.ofCurve_contMDiff P)

theorem ofCurve₂_inj (P : X) (h : 0 < genus₂ X) : Function.Injective (ofCurve₂ P) := by
  have hg : 0 < genus X := by simpa [genus₂] using h
  intro x y hxy
  exact Jacobian.ofCurve_inj P hg (congrArg Prod.fst hxy)

/-! ## Functoriality: componentwise pushforward / pullback -/

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The doubled pushforward, acting componentwise. -/
noncomputable def pushforward₂ (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian₂ X →ₜ+ Jacobian₂ Y :=
  (Jacobian.pushforward f hf).prodMap (Jacobian.pushforward f hf)

/-- The doubled pullback, acting componentwise. -/
noncomputable def pullback₂ (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian₂ Y →ₜ+ Jacobian₂ X :=
  (Jacobian.pullback f hf).prodMap (Jacobian.pullback f hf)

theorem pushforward₂_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (I₂ X) (I₂ Y) ω (pushforward₂ f hf) :=
  (Jacobian.pushforward_contMDiff f hf).prodMap (Jacobian.pushforward_contMDiff f hf)

theorem pullback₂_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (I₂ Y) (I₂ X) ω (pullback₂ f hf) :=
  (Jacobian.pullback_contMDiff f hf).prodMap (Jacobian.pullback_contMDiff f hf)

theorem pushforward₂_id_apply (P : Jacobian₂ X) :
    pushforward₂ id contMDiff_id P = P :=
  Prod.ext (Jacobian.pushforward_id_apply P.1) (Jacobian.pushforward_id_apply P.2)

theorem pullback₂_id_apply (P : Jacobian₂ X) :
    pullback₂ id contMDiff_id P = P :=
  Prod.ext (Jacobian.pullback_id_apply P.1) (Jacobian.pullback_id_apply P.2)

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

theorem pushforward₂_comp_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian₂ X) :
    pushforward₂ (g ∘ f) (hg.comp hf) P = pushforward₂ g hg (pushforward₂ f hf P) :=
  Prod.ext (Jacobian.pushforward_comp_apply f hf g hg P.1)
    (Jacobian.pushforward_comp_apply f hf g hg P.2)

theorem pullback₂_comp_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian₂ Z) :
    pullback₂ (g ∘ f) (hg.comp hf) P = pullback₂ f hf (pullback₂ g hg P) :=
  Prod.ext (Jacobian.pullback_comp_apply f hf g hg P.1)
    (Jacobian.pullback_comp_apply f hf g hg P.2)

/-- The key nontrivial identity `f_* ∘ f^* = deg(f) • id`, componentwise. The
degree is the *same* `ContMDiff.degree f hf` Buzzard uses — no new data. -/
theorem pushforward₂_pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (P : Jacobian₂ Y) :
    pushforward₂ f hf (pullback₂ f hf P) = (ContMDiff.degree f hf) • P := by
  have h1 := Jacobian.pushforward_pullback f hf P.1
  have h2 := Jacobian.pushforward_pullback f hf P.2
  rw [Prod.smul_mk]
  exact Prod.ext h1 h2

/-! ## Conclusion: a genuinely different object -/

/-- The doubled model has strictly larger genus whenever the curve has positive
genus. Since `genus` is the complex dimension of the (compact, connected) torus
`Jacobian₂ X` (`finrank_model_eq_genus₂`), and a compact connected complex Lie
group is determined up to the dimension as a `g`-torus, `Jacobian₂ X` is **not**
isomorphic to the genuine Jacobian. Yet every requirement above holds. So the 24,
as literally stated, do not pin the object. -/
theorem genus₂_ne_genus (h : 0 < genus X) : genus₂ X ≠ genus X := by
  simp only [genus₂]; omega

end GenusDoublingCounterexample
