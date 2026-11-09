import SMSFormula.PadicSpecialOrthogonalDifferentialLocalInverseVolumePartialProduct

/-!
# Convergence of the differential p-adic inverse-volume cutoff products

The differential inverse-volume cutoff product is eventually the inverse
canonical finite correction times the `ENNReal.ofReal` image of the existing
real Schulze--Pillot partial inverse product.  This module transports an
existing real cutoff-convergence certificate through that eventual identity.

It defines only a convergence predicate for the cutoff products.  No
restricted-product volume, real-place factor, reference Haar comparison, or
Tamagawa theorem is introduced.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Convergence of the internally constructed differential inverse-volume
partial products along the natural prime cutoffs. -/
def
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (V : ℝ≥0∞) : Prop :=
  Filter.Tendsto
    (fun N : ℕ =>
      L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
        N)
    Filter.atTop (nhds V)

/-- Any real Schulze--Pillot cutoff convergence certificate
transports to the differential inverse-volume cutoff products, with the
inverse canonical finite correction kept explicit. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_inv_localCorrectionFiniteProduct_mul_ENNReal_ofReal_of_massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] {P : ℝ}
    (hP : massLocalInverseProductTendsTo L P) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
      (L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
        ENNReal.ofReal P) := by
  unfold massLocalInverseProductTendsTo at hP
  unfold
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
  have hOfReal :
      Filter.Tendsto
        (fun N : ℕ =>
          ENNReal.ofReal (massPartialPrimeInverseProduct L N))
        Filter.atTop (nhds (ENNReal.ofReal P)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hP
  have hCorrectionInvTop :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ ≠
        ⊤ :=
    ENNReal.inv_ne_top.mpr
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_zero
  have hCorrected :
      Filter.Tendsto
        (fun N : ℕ =>
          L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
            ENNReal.ofReal
              (massPartialPrimeInverseProduct L N))
        Filter.atTop
        (nhds
          (L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
            ENNReal.ofReal P)) :=
    ENNReal.Tendsto.const_mul hOfReal (Or.inr hCorrectionInvTop)
  refine Filter.Tendsto.congr' ?_ hCorrected
  filter_upwards [
    Filter.eventually_ge_atTop
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupportCutoff]
      with N hN
  exact
    (L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct_eq_inv_localCorrectionFiniteProduct_mul_ENNReal_ofReal_massPartialPrimeInverseProduct_of_cutoff_le
      hN).symm

end PositiveDefiniteIntegralLattice
