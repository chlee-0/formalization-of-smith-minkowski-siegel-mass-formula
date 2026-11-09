import SMSFormula.RationalIdeleFiniteModule

/-!
# The place-indexed rational norm product over an enlarged finite set

The mixed Bruhat word produces one real half-rank amplitude and one native
half-rank amplitude at every place of a supplied finite set.  Matching the
assembled word to the global rational dilation needs the literal statement
that those amplitudes multiply to one.

This file records exactly that, in the place indexing actually used by the
adelic tensor theorems: for a nonzero rational `value` whose norm support is
contained in `places`, the local norm is one at every place outside `places`
and

```text
|value| * prod_{v in places} ‖value‖_v = 1.
```

Only the existing finite support `Rat.padicNormPrimeSupport` and the existing
rational product formula are used.  No new place set, Haar normalization,
character, or idele decomposition is introduced.
-/

noncomputable section

open IsDedekindDomain
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

local instance placeNormProductPrimeFact (v : HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The native local norm of a rational scalar is the literal `padicNorm` of the
prime attached to the place. -/
theorem norm_algebraMap_ratCast_eq_padicNorm (value : ℚ) (v : HeightOneSpectrum ℤ) :
    ‖algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] value‖ =
      ((padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value : ℚ) : ℝ) := by
  rw [show algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] value =
    ((value : ℚ) : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) from rfl]
  exact Padic.eq_padicNorm value

/-- Outside the existing norm support the local norm of a nonzero rational is one. -/
theorem norm_algebraMap_eq_one_of_not_mem_rationalPadicNormSupportPlaces
    {value : ℚ} (hvalue : value ≠ 0) {v : HeightOneSpectrum ℤ}
    (hv : v ∉ rationalPadicNormSupportPlaces value) :
    ‖algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] value‖ = 1 := by
  have hp : Rat.HeightOneSpectrum.primesEquiv v ∉ Rat.padicNormPrimeSupport value := by
    intro hp
    exact hv (Finset.mem_map.mpr
      ⟨Rat.HeightOneSpectrum.primesEquiv v, hp,
        Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v⟩)
  have hnnnorm := Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport
    hvalue (Rat.HeightOneSpectrum.primesEquiv v) hp
  exact congrArg NNReal.toReal hnnnorm

/-- The same statement in the `padicNorm` normalization, which is not type dependent. -/
theorem padicNorm_eq_one_of_not_mem_rationalPadicNormSupportPlaces
    {value : ℚ} (hvalue : value ≠ 0) {v : HeightOneSpectrum ℤ}
    (hv : v ∉ rationalPadicNormSupportPlaces value) :
    padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value = 1 := by
  have h := norm_algebraMap_eq_one_of_not_mem_rationalPadicNormSupportPlaces hvalue hv
  rw [norm_algebraMap_ratCast_eq_padicNorm] at h
  exact_mod_cast h

/-- The rational product formula in the place indexing, valid on every enlargement of
the existing norm support. -/
theorem abs_mul_prod_padicNorm_eq_one_of_subset
    {value : ℚ} (hvalue : value ≠ 0) (places : Finset (HeightOneSpectrum ℤ))
    (hsub : rationalPadicNormSupportPlaces value ⊆ places) :
    |value| * ∏ v ∈ places, padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value = 1 := by
  have hrestrict : ∏ v ∈ places, padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value =
      ∏ v ∈ rationalPadicNormSupportPlaces value,
        padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value := by
    refine (Finset.prod_subset hsub ?_).symm
    intro v _ hv
    exact padicNorm_eq_one_of_not_mem_rationalPadicNormSupportPlaces hvalue hv
  have hmap : ∏ v ∈ rationalPadicNormSupportPlaces value,
      padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value =
        ∏ p ∈ Rat.padicNormPrimeSupport value, padicNorm p.1 value := by
    unfold rationalPadicNormSupportPlaces
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl ?_
    intro p _
    exact congrArg (fun q : {p : ℕ // Nat.Prime p} ↦ padicNorm q.1 value)
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply p)
  rw [hrestrict, hmap]
  exact Rat.abs_mul_prod_padicNorm_padicNormPrimeSupport value hvalue

/-- The real absolute value times the native local norms over any enlargement of the
existing support is one. -/
theorem abs_mul_prod_norm_eq_one_of_subset
    {value : ℚ} (hvalue : value ≠ 0) (places : Finset (HeightOneSpectrum ℤ))
    (hsub : rationalPadicNormSupportPlaces value ⊆ places) :
    |(value : ℝ)| *
        ∏ v ∈ places, ‖algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] value‖ = 1 := by
  have hcast : ∏ v ∈ places, ‖algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] value‖ =
      ((∏ v ∈ places, padicNorm (Rat.HeightOneSpectrum.primesEquiv v).1 value : ℚ) : ℝ) := by
    rw [Rat.cast_prod]
    exact Finset.prod_congr rfl fun v _ ↦ norm_algebraMap_ratCast_eq_padicNorm value v
  have habs : |(value : ℝ)| = ((|value| : ℚ) : ℝ) := by
    rw [Rat.cast_abs]
  rw [hcast, habs, ← Rat.cast_mul, abs_mul_prod_padicNorm_eq_one_of_subset hvalue places hsub,
    Rat.cast_one]

/-- The half-rank amplitudes attached to the real and native Bruhat words cancel
exactly, on every enlargement of the existing norm support. -/
theorem abs_rpow_mul_prod_norm_rpow_eq_one_of_subset
    {value : ℚ} (hvalue : value ≠ 0) (places : Finset (HeightOneSpectrum ℤ))
    (hsub : rationalPadicNormSupportPlaces value ⊆ places) (exponent : ℝ) :
    |(value : ℝ)| ^ exponent *
        ∏ v ∈ places,
          ‖algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] value‖ ^ exponent = 1 := by
  rw [Real.finset_prod_rpow places _ (fun v _ ↦ norm_nonneg _) exponent,
    ← Real.mul_rpow (abs_nonneg _) (Finset.prod_nonneg fun v _ ↦ norm_nonneg _),
    abs_mul_prod_norm_eq_one_of_subset hvalue places hsub, Real.one_rpow]

end RationalQuadraticSpaceMatrix
