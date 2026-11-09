import SMSFormula.PadicSpecialOrthogonalDifferentialLocalCorrectionSupport
import SMSFormula.Product

/-!
# The finite product of the p-adic local corrections

The corrected p-adic special-stabilizer volume differs from
`normalizedLocalDensity` by a combined local correction.  Its possible failure to
equal one is supported on the literal union of the Schulze--Pillot bad-prime
finset and the separate rational basis-comparison support.

This module installs the prime instance through the rational-prime subtype,
forms the correction product over that explicit finite union, and proves that
every larger finite prime product has the same value.  It does not evaluate or
split the product and does not form a product of local stabilizer volumes.
-/

noncomputable section

open Matrix
open scoped BigOperators ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The combined local correction indexed by the subtype of rational primes.
The required primality instance is installed from the subtype proof. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  L.localPadicSpecialOrthogonalDifferentialLocalCorrection q.1

/-- The literal union supporting the combined local correction.  Its two
components remain visible and are not merged into another exceptional set. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport
    (L : PositiveDefiniteIntegralLattice n) :
    Finset {p : ℕ // Nat.Prime p} :=
  massBadPrimeSet L ∪
    skewAdjointFixedFormElementaryDetPrimeSupport
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero

/-- Membership in the explicit correction support is membership in one of its
two components. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport_iff
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    q ∈
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ↔
      q ∈ massBadPrimeSet L ∨
        q ∈ skewAdjointFixedFormElementaryDetPrimeSupport
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero := by
  simp only [
    localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport,
    Finset.mem_union]

/-- The canonical finite product of the combined local corrections over their
explicit support. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  ∏ q ∈
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport,
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q

/-- Every subtype-indexed local correction is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q ≠ 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection_ne_zero q.1

/-- Every subtype-indexed local correction is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q ≠ ⊤ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection_ne_top q.1

/-- The finite product of the supported local corrections is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_zero
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct ≠
      0 := by
  unfold
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  exact Finset.prod_ne_zero_iff.mpr fun q _hq ↦
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_ne_zero q

/-- The finite product of the supported local corrections is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_top
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct ≠
      ⊤ := by
  unfold
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  exact ENNReal.prod_ne_top fun q _hq ↦
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_ne_top q

/-- Outside the literal union of the two exceptional supports, the
subtype-indexed local correction is one. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_eq_one_of_not_mem
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq :
      q ∉
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q = 1 := by
  have hqParts :
      q ∉ massBadPrimeSet L ∧
        q ∉ skewAdjointFixedFormElementaryDetPrimeSupport
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero := by
    simpa only [
      localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport,
      Finset.mem_union, not_or] using hq
  simpa only [
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_one_of_not_mem
      q hqParts.1 hqParts.2

/-- Every finite prime set containing the explicit support gives the same
local-correction product as the canonical finite product. -/
theorem
    prod_localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_eq_finiteProduct_of_subset
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (S : Finset {p : ℕ // Nat.Prime p})
    (hSupport :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ⊆
        S) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q) =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct := by
  unfold
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  exact
    (Finset.prod_subset hSupport
      (by
        intro q _hqS hqSupport
        exact
          L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_eq_one_of_not_mem
            q hqSupport)).symm

end PositiveDefiniteIntegralLattice
