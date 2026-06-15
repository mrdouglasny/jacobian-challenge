/-
# The generation half of van Kampen, membership form (G1)

Issue #171 / `docs/planning/B1_GENERATION_ROUTE.md` rung **G1**.

**Main result** (`fromPath_mem_of_loops_mem`): let `U : ι → Set X` be an open
cover of `X` with all pairwise intersections path-connected, and let the
basepoint `x₀` lie in every cover set.  Then any subgroup
`H ≤ π₁(X, x₀)` containing the class of every loop at `x₀` that stays inside
a single cover set contains every loop class — i.e. `π₁(X, x₀)` is
*generated* by the single-set loops.  This is the generation half of the
Seifert–van Kampen theorem: no amalgamation, no free products, no pushout.

**Proof.**  Lebesgue-subdivide a loop along the cover
(`exists_lebesgue_subdivision_iUnion`), conjugate the pieces by spokes from
`x₀` to the junctions and telescope (`fromPath_concat_conj_mem`).  Each
interior junction lies in the intersection of the two adjacent cover sets;
since that intersection is path-connected and contains `x₀`, the spoke can
be chosen inside it, so each conjugated factor is a loop inside a single
cover set — a generator.  This is the `FiniteGoodCover` engine with the
anchor layer removed: there the cells were simply connected and the goal was
finite generation; here the cells have arbitrary `π₁` and the conclusion is
relative to `H`.

Downstream (B1, route doc rungs G2–G5): applied with two half-plane cells to
show the puncture lassos generate `π₁(ℂ ∖ T)`.  Mathlib-only imports.
-/
import Jacobians.Topology.FiniteGoodCover

namespace Jacobians.Topology

open unitInterval Fin Set

local notation "Qmk" => Path.Homotopic.Quotient.mk

variable {X : Type*} [TopologicalSpace X]

/-- **The generation half of van Kampen, membership form.**  Over an open
cover with path-connected pairwise intersections all containing the
basepoint, a subgroup containing every single-cover-set loop class contains
every loop class. -/
theorem fromPath_mem_of_loops_mem {ι : Type*} {U : ι → Set X}
    (hopen : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    (hpcInter : ∀ i j, IsPathConnected (U i ∩ U j))
    {x₀ : X} (hx₀ : ∀ i, x₀ ∈ U i)
    (H : Subgroup (FundamentalGroup X x₀))
    (hloops : ∀ (i : ι) (δ : Path x₀ x₀),
      (∀ s, δ s ∈ U i) → FundamentalGroup.fromPath (Qmk δ) ∈ H)
    (γ : Path x₀ x₀) :
    FundamentalGroup.fromPath (Qmk γ) ∈ H := by
  classical
  -- Lebesgue subdivision of `γ` along the cover
  obtain ⟨N, t, ht0, htl, hsub⟩ :=
    exists_lebesgue_subdivision_iUnion γ.continuous hopen hcov
  choose ch hch using hsub
  -- junctions and arcs
  set q : Fin (N + 1) → X := ⇑γ ∘ t with hq
  set F : (k : Fin N) → Path (q k.castSucc) (q k.succ) :=
    fun k => γ.subpath (t k.castSucc) (t k.succ) with hF
  have hrangeF : ∀ k : Fin N, range (F k) ⊆ U (ch k) := by
    intro k
    change range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U (ch k)
    rw [Path.range_subpath]
    exact hch k
  have h0 : q 0 = x₀ := by rw [hq]; change γ (t 0) = x₀; rw [ht0]; exact γ.source
  have hl : q (last N) = x₀ := by rw [hq]; change γ (t (last N)) = x₀; rw [htl]; exact γ.target
  -- spokes: paths from the basepoint to the junctions, inside both adjacent
  -- cover sets; the two end junctions get constant spokes.
  have hjunc : ∀ j : Fin (N + 1),
      ∃ c : Path x₀ (q j),
        (∀ k : Fin N, j = k.castSucc → ∀ s, c s ∈ U (ch k)) ∧
        (∀ k : Fin N, j = k.succ → ∀ s, c s ∈ U (ch k)) ∧
        ((j = 0 ∨ j = last N) → ∀ s, c s = x₀) := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨(Path.refl x₀).cast rfl h0, ?_, ?_, fun _ s => rfl⟩
      · intro k _ s
        change x₀ ∈ U (ch k)
        exact hx₀ (ch k)
      · intro k hk
        exact absurd hk.symm (Fin.succ_ne_zero k)
    by_cases hjl : j = last N
    · subst hjl
      refine ⟨(Path.refl x₀).cast rfl hl, ?_, ?_, fun _ s => rfl⟩
      · intro k hk
        exact absurd hk.symm (Fin.castSucc_lt_last k).ne
      · intro k _ s
        change x₀ ∈ U (ch k)
        exact hx₀ (ch k)
    -- interior junction: it lies in both adjacent cover sets, and so does the
    -- basepoint; route the spoke through their (path-connected) intersection.
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
      have hqL : q j ∈ U (ch kL) := by
        have := hrangeF kL (F kL).target_mem_range
        rwa [hkLj] at this
      have hqR : q j ∈ U (ch kR) := by
        have := hrangeF kR (F kR).source_mem_range
        rwa [hkRj] at this
      have hjoin : JoinedIn (U (ch kL) ∩ U (ch kR)) x₀ (q j) :=
        (hpcInter (ch kL) (ch kR)).joinedIn x₀ ⟨hx₀ _, hx₀ _⟩ (q j) ⟨hqL, hqR⟩
      refine ⟨hjoin.somePath, ?_, ?_, ?_⟩
      · intro k hk s
        have hkkR : k = kR := Fin.castSucc_injective N (by rw [← hk, hkRj])
        subst hkkR
        exact (hjoin.somePath_mem s).2
      · intro k hk s
        have hkkL : k = kL := Fin.succ_injective N (by rw [← hk, hkLj])
        subst hkkL
        exact (hjoin.somePath_mem s).1
      · intro h
        rcases h with h | h
        · exact absurd h hj0
        · exact absurd h hjl
  choose c hpropL hpropR hpropEnd using hjunc
  -- every conjugated-arc factor is a loop inside a single cover set
  have hfac : ∀ k : Fin N, FundamentalGroup.fromPath
      (Qmk ((c k.castSucc).trans ((F k).trans (c k.succ).symm))) ∈ H := by
    intro k
    refine hloops (ch k) _ fun s => ?_
    have hrange : range ((c k.castSucc).trans ((F k).trans (c k.succ).symm))
        ⊆ U (ch k) := by
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      refine Set.union_subset ?_ (Set.union_subset (hrangeF k) ?_)
      · rintro _ ⟨s, rfl⟩
        exact hpropL k.castSucc k rfl s
      · rintro _ ⟨s, rfl⟩
        exact hpropR k.succ k rfl s
    exact hrange ⟨s, rfl⟩
  -- telescope
  have htele := fromPath_concat_conj_mem H q c F hfac
  -- the end spokes are constant
  have hc0 : c 0 = (Path.refl x₀).cast rfl h0 := by
    ext s
    rw [Path.cast_coe]
    show (c 0) s = Path.refl x₀ s
    rw [Path.refl_apply]
    exact hpropEnd 0 (Or.inl rfl) s
  have hcl : c (last N) = (Path.refl x₀).cast rfl hl := by
    ext s
    rw [Path.cast_coe]
    show (c (last N)) s = Path.refl x₀ s
    rw [Path.refl_apply]
    exact hpropEnd (last N) (Or.inr rfl) s
  -- assemble: the conjugated concatenation is homotopic to `γ` itself
  have hsubγ : γ.subpath (t 0) (t (last N)) = γ.cast h0 hl := by
    ext s
    change (⇑γ ∘ Icc.convexComb (t 0) (t (last N))) s = γ s
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
  rwa [hmkeq] at htele

/-- **Two-open generation** (the classical special case).  If
`X = U ∪ V` with `U`, `V` open, `U ∩ V` path-connected containing the
basepoint, then any subgroup containing every `U`-loop class and every
`V`-loop class is all of `π₁(X, x₀)`. -/
theorem fromPath_mem_of_two_open {U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcov : ∀ x : X, x ∈ U ∪ V)
    (hUpc : IsPathConnected U) (hVpc : IsPathConnected V)
    (hUVpc : IsPathConnected (U ∩ V))
    {x₀ : X} (hx₀ : x₀ ∈ U ∩ V)
    (H : Subgroup (FundamentalGroup X x₀))
    (hU : ∀ δ : Path x₀ x₀, (∀ s, δ s ∈ U) → FundamentalGroup.fromPath (Qmk δ) ∈ H)
    (hV : ∀ δ : Path x₀ x₀, (∀ s, δ s ∈ V) → FundamentalGroup.fromPath (Qmk δ) ∈ H)
    (γ : Path x₀ x₀) :
    FundamentalGroup.fromPath (Qmk γ) ∈ H := by
  have hpcInter : ∀ i j : Bool,
      IsPathConnected ((fun b => bif b then U else V) i ∩ (fun b => bif b then U else V) j) := by
    intro i j
    cases i <;> cases j
    · simpa using hVpc
    · simpa [Set.inter_comm] using hUVpc
    · simpa using hUVpc
    · simpa using hUpc
  refine fromPath_mem_of_loops_mem (U := fun b : Bool => bif b then U else V)
    (fun b => by cases b <;> simpa using ‹_›) ?_ hpcInter ?_ H ?_ γ
  · intro x
    rcases hcov x with hx | hx
    · exact ⟨true, by simpa using hx⟩
    · exact ⟨false, by simpa using hx⟩
  · intro b
    cases b
    · simpa using hx₀.2
    · simpa using hx₀.1
  · intro b δ hδ
    cases b
    · exact hV δ (by simpa using hδ)
    · exact hU δ (by simpa using hδ)

end Jacobians.Topology
