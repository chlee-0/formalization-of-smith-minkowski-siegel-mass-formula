import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteLocalInverseVolumeProduct

/-!
# Cutoff products of the differential p-adic inverse stabilizer volumes

The combined differential local correction has an explicit finite prime
support.  This module bounds that support by a natural cutoff and specializes
the exact finite inverse-volume identity to the standard sets
`rationalPrimesUpTo N`.

The resulting cutoff identity remains entirely finite.  No limit, restricted
product, real-place factor, reference Haar comparison, or Tamagawa theorem is
used.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The largest underlying rational prime in the explicit local-correction
support, with value zero when the support is empty. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupportCutoff
    (L : PositiveDefiniteIntegralLattice n) : ℕ :=
  L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport.sup
    (fun q : {p : ℕ // Nat.Prime p} => q.1)

/-- The explicit local-correction support lies in the rational-prime cutoff
defined by its supremum. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport_subset_rationalPrimesUpTo_cutoff
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ⊆
      rationalPrimesUpTo
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupportCutoff := by
  intro q hq
  rw [mem_rationalPrimesUpTo_iff]
  exact Finset.le_sup hq

/-- Every larger natural cutoff still contains the explicit local-correction
support. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport_subset_rationalPrimesUpTo_of_cutoff_le
    (L : PositiveDefiniteIntegralLattice n) {N : ℕ}
    (hN :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupportCutoff ≤
        N) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ⊆
      rationalPrimesUpTo N := by
  exact Finset.Subset.trans
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport_subset_rationalPrimesUpTo_cutoff
    (rationalPrimesUpTo_subset_of_le hN)

/-- The inverse of the finite product of corrected differential stabilizer
volumes over the rational primes bounded by `N`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) : ℝ≥0∞ :=
  (∏ q ∈ rationalPrimesUpTo N,
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q)⁻¹

/-- Every differential inverse-volume cutoff product is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
        N ≠
      0 := by
  unfold
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
  exact ENNReal.inv_ne_zero.mpr
    (L.prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top
      (rationalPrimesUpTo N))

/-- Every differential inverse-volume cutoff product is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct_ne_top
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
        N ≠
      ⊤ := by
  unfold
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
  exact ENNReal.inv_ne_top.mpr
    (L.prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero
      (rationalPrimesUpTo N))

/-- Once the cutoff contains the explicit correction support, the
differential inverse-volume cutoff product is the inverse canonical
correction product times the existing real Schulze--Pillot partial inverse
product embedded in `ENNReal`. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct_eq_inv_localCorrectionFiniteProduct_mul_ENNReal_ofReal_massPartialPrimeInverseProduct_of_cutoff_le
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] {N : ℕ}
    (hN :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupportCutoff ≤
        N) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
        N =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
        ENNReal.ofReal
          (massPartialPrimeInverseProduct L N) := by
  simpa only [
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct,
    massPartialPrimeInverseProduct] using
    L.inv_prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_inv_localCorrectionFiniteProduct_mul_ENNReal_ofReal_massFinitePrimeInverseProduct_of_subset
      (rationalPrimesUpTo N)
      (L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport_subset_rationalPrimesUpTo_of_cutoff_le
        hN)

end PositiveDefiniteIntegralLattice
