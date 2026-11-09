import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteLocalVolumeProduct

/-!
# Finite inverse products of the corrected p-adic stabilizer volumes

This module inverts the internally proved finite corrected stabilizer-volume
product.  Because inversion in `ENNReal` is not globally multiplicative at
zero and infinity, every inverse-product identity is proved from the existing
nonzero and finite certificates.

The inverse `ENNReal` Schulze--Pillot alpha product is then identified with
the `ENNReal.ofReal` image of the existing real
`massFinitePrimeInverseProduct`.  No limit, restricted product,
real-place factor, reference Haar comparison, or Tamagawa theorem is used.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The inverse of a finite product of positive finite `ENNReal`
Schulze--Pillot alpha factors is the product of their inverses. -/
theorem inv_prod_normalizedLocalDensityENNRealAtPrime_eq_prod_inv
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q)⁻¹ =
      ∏ q ∈ S, (L.normalizedLocalDensityENNRealAtPrime q)⁻¹ := by
  symm
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro q hq
  exact
    ENNReal.inv_mul_cancel
      (L.normalizedLocalDensityENNRealAtPrime_ne_zero q)
      (L.normalizedLocalDensityENNRealAtPrime_ne_top q)

/-- Inverting the finite corrected stabilizer-volume identity isolates the
inverse canonical correction product and the pointwise inverse alpha product.
-/
theorem
    inv_prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_inv_localCorrectionFiniteProduct_mul_prod_inv_normalizedLocalDensityENNRealAtPrime_of_subset
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (S : Finset {p : ℕ // Nat.Prime p})
    (hSupport :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ⊆
        S) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
        ∏ q ∈ S, (L.normalizedLocalDensityENNRealAtPrime q)⁻¹ := by
  let C :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  let A := ∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q
  let V :=
    ∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q
  have hC0 : C ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_zero
  have hCtop : C ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_top
  have hA0 : A ≠ 0 :=
    L.prod_normalizedLocalDensityENNRealAtPrime_ne_zero S
  have hAtop : A ≠ ⊤ :=
    L.prod_normalizedLocalDensityENNRealAtPrime_ne_top S
  have hV : V = C * A :=
    L.prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_localCorrectionFiniteProduct_mul_prod_normalizedLocalDensityENNRealAtPrime_of_subset
      S hSupport
  have hInvMul : V⁻¹ = C⁻¹ * A⁻¹ := by
    rw [hV]
    symm
    apply ENNReal.eq_inv_of_mul_eq_one_left
    calc
      (C⁻¹ * A⁻¹) * (C * A) =
          (C⁻¹ * C) * (A⁻¹ * A) := by
            ac_rfl
      _ = 1 := by
        rw [
          ENNReal.inv_mul_cancel hC0 hCtop,
          ENNReal.inv_mul_cancel hA0 hAtop,
          one_mul]
  change V⁻¹ =
    C⁻¹ * ∏ q ∈ S, (L.normalizedLocalDensityENNRealAtPrime q)⁻¹
  rw [hInvMul,
    L.inv_prod_normalizedLocalDensityENNRealAtPrime_eq_prod_inv S]

/-- Pointwise, the inverse `ENNReal` alpha factor is the `ENNReal.ofReal`
image of the existing real inverse local mass factor. -/
theorem
    inv_normalizedLocalDensityENNRealAtPrime_eq_ENNReal_ofReal_massLocalInverseFactorAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    (L.normalizedLocalDensityENNRealAtPrime q)⁻¹ =
      ENNReal.ofReal (massLocalInverseFactorAtPrime L q) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold normalizedLocalDensityENNRealAtPrime
  change
    (ENNReal.ofReal (normalizedLocalDensity L q.1))⁻¹ =
      ENNReal.ofReal ((normalizedLocalDensity L q.1)⁻¹)
  rw [ENNReal.ofReal_inv_of_pos (normalizedLocalDensity_pos L q.1)]

/-- The finite product of inverse `ENNReal` alpha factors is exactly the
`ENNReal.ofReal` image of the existing real finite inverse local product. -/
theorem
    prod_inv_normalizedLocalDensityENNRealAtPrime_eq_ENNReal_ofReal_massFinitePrimeInverseProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S, (L.normalizedLocalDensityENNRealAtPrime q)⁻¹) =
      ENNReal.ofReal (massFinitePrimeInverseProduct L S) := by
  calc
    (∏ q ∈ S, (L.normalizedLocalDensityENNRealAtPrime q)⁻¹) =
        ∏ q ∈ S,
          ENNReal.ofReal
            (massLocalInverseFactorAtPrime L q) := by
              apply Finset.prod_congr rfl
              intro q _hq
              exact
                L.inv_normalizedLocalDensityENNRealAtPrime_eq_ENNReal_ofReal_massLocalInverseFactorAtPrime
                  q
    _ = ENNReal.ofReal
        (∏ q ∈ S, massLocalInverseFactorAtPrime L q) := by
          rw [ENNReal.ofReal_prod_of_nonneg]
          intro q _hq
          exact (massLocalInverseFactorAtPrime_pos L q).le
    _ = ENNReal.ofReal
        (massFinitePrimeInverseProduct L S) := rfl

/-- Exact finite inverse-volume formula with the canonical finite correction
product and the existing real Schulze--Pillot finite inverse product. -/
theorem
    inv_prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_inv_localCorrectionFiniteProduct_mul_ENNReal_ofReal_massFinitePrimeInverseProduct_of_subset
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (S : Finset {p : ℕ // Nat.Prime p})
    (hSupport :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ⊆
        S) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
        ENNReal.ofReal
          (massFinitePrimeInverseProduct L S) := by
  rw [
    L.inv_prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_inv_localCorrectionFiniteProduct_mul_prod_inv_normalizedLocalDensityENNRealAtPrime_of_subset
      S hSupport,
    L.prod_inv_normalizedLocalDensityENNRealAtPrime_eq_ENNReal_ofReal_massFinitePrimeInverseProduct
      S]

end PositiveDefiniteIntegralLattice
