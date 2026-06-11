# Lane A blocker — the genus-0 keystone leg is NOT covered by `SerreResidueDirectGenus0*`

*2026-06-10, lane A session 1 (branch `feat/keystone-a-lane`). Severity: not research-grade,
but a gap in the recorded routing plan — needs an owner/lane-R decision before the keystone
can be discharged at `kirovGenus X = 0`.*

## The plan of record (R4_G0_NOTE.md, Decision 4-5)

`docs/planning/R4_G0_NOTE.md` routes the `g = 0` keystone leg "through the snapshot's direct
genus-0 feeders — `SerreResidueDirectGenus0*.lean` (e.g. `residueTheorem_ofAdapted_genus0`,
`residueTheorem_ofCanonicalSimpleInfty_genus0`)", with the case split at the keystone
instantiation. The case split itself is now implemented and proven
(`exists_serreDualityData_genus_split`, `SerreAssemblyPrep.lean`), with the `g = 0` leg as the
named hypothesis `hzero : kirovGenus X = 0 → Nonempty (SerreDualityData 𝔘)`.

## The finding

Close reading of the four `SerreResidueDirectGenus0*` files (`SerreResidueDirectGenus0.lean`,
`...Assemble.lean`, `...Germ.lean`, `...GermDischarge.lean`): every headline there — including
all three `residueTheorem_*_genus0` capstones — is parametrized by

```
ω₀ : HolomorphicOneForms X
```

and concludes `∑ a ∈ poles, formFnResidue ω₀ g a = 0`. The "genus-0" in their names refers to
**Gate A's residual #5** — the `R₀`/`hR₀_*` ∞-vanishing field-group of the trace remainder on
the TARGET `ℙ¹` (`recipCoeff (T − L.R)` at `ζ = 0`), discharged there by Cauchy-at-∞ — **not**
to the source surface having genus 0. At source genus 0 we have `HolomorphicOneForms X = 0`
(`kirovGenus = finrank`), so `ω₀ = 0` and these theorems are vacuously true and carry no
information; they cannot feed a residue pairing.

Consequently the `g = 0` leg of the keystone is closed by NO existing machinery:

* lane R's fine-sheaf functional needs a nonzero holomorphic `ω₀` (R4_G0_NOTE Decision 1-3:
  do NOT fake a witness, do NOT generalize to meromorphic `ω₀` in the `dz`-slot);
* Gate A (`residueTheorem_unconditional`) is likewise `ω₀`-holomorphic, hence vacuous at g=0;
* the `H¹(ℙ¹, 𝒪) = 0` circle in the snapshot is about the literal sphere / about arithmetic
  genus, and `SerreDualityData` needs the pairing `ι_D` bijective for EVERY divisor `D`
  (negative ones included), which does not degenerate away at `g = 0`.

## What IS in place (so the leg is small and sharply-stated)

`SerreAssemblyPrep.lean` already accepts both plausible discharge shapes:

1. **Meromorphic-`ω₀` residue functional.** S1 is genus-uniform:
   `lDim_eq_genus_of_order_eq` gives `lDim K = 0 = kirovGenus` for `K = div ω₀'` of ANY
   germ-nonzero meromorphic `ω₀'` (e.g. `ω₀' = df` from `nonempty_canonicalForm17Data`, which
   holds at every genus). So the leg reduces to: a `GlobalResidue 𝔘 K` (or
   `CousinResidueData 𝔘 K`) over a meromorphic `ω₀'` at `g = 0`, plus `UnwindRegularity` —
   consumption point `exists_serreDualityData_of_globalResidue_meromorphic`. The missing
   analytic atom is a `∑Res = 0` for `ω₀'·g` with MEROMORPHIC `ω₀'` at `g = 0` (the
   trace-to-ℙ¹ route should specialize, since at `g = 0` every meromorphic 1-form is
   `(rational in f)·df` for a degree-1 map — but no Lean artifact exists).
2. **Bespoke `g = 0` `SerreDualityData`.** Any direct construction can feed `hzero` as-is.

## Ask

Owner / lane-R steer on which shape the `g = 0` leg takes, and where it lives (lane R
extension vs. its own mini-lane). Until then `hzero` stays a named hypothesis of
`exists_serreDualityData_genus_split` — never a sorry. The `g ≥ 1` leg is fully reduced to
lane-R outputs and is unaffected.
