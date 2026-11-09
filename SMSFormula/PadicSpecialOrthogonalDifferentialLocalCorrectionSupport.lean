import SMSFormula.PadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection

/-!
# The combined p-adic local correction and its finite support

The internally constructed corrected special-stabilizer volume differs from
`normalizedLocalDensity` by two nonzero finite factors: the intrinsic
coordinate-normalization correction and the selected-fiber correction.  This
module packages their product as one local correction.

At a Schulze--Pillot good prime the combined correction is exactly the p-adic
norm of the rational basis-comparison determinant.  Away from its separate
finite support it is one.  The support theorem states the two exceptional
finsets as a disjunction and forms no prime product.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The product of the intrinsic coordinate-normalization correction and the
selected-fiber correction at a prime. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialLocalCorrection
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0∞ :=
  L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
      p *
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p

/-- The combined local correction is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrection_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection p ≠ 0 := by
  unfold localPadicSpecialOrthogonalDifferentialLocalCorrection
  exact
    mul_ne_zero
      (L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection_ne_zero
        p)
      (L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_ne_zero
        p)

/-- The combined local correction is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrection_ne_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection p ≠ ⊤ := by
  unfold localPadicSpecialOrthogonalDifferentialLocalCorrection
  exact
    ENNReal.mul_ne_top
      (L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection_ne_top
        p)
      (L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_ne_top
        p)

/-- At every prime, the corrected special-stabilizer volume is the combined
local correction times `normalizedLocalDensity`. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_localCorrection_mul_ENNReal_ofReal_normalizedLocalDensity
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrection p *
        ENNReal.ofReal (normalizedLocalDensity L p) := by
  simpa only [localPadicSpecialOrthogonalDifferentialLocalCorrection] using
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_coordinateNormalizationCorrection_mul_densityFiberCorrection_mul_ENNReal_ofReal_normalizedLocalDensity
      p

/-- At a Schulze--Pillot good prime, the combined local correction is exactly
the p-adic norm of the rational fixed/form-adapted basis-comparison
determinant. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_comparisonNorm_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection q.1 =
      (‖algebraMap ℚ ℚ_[q.1]
          (skewAdjointFixedFormElementaryDetScalar
            L.rationalFormMatrix
            (L.form_symm.map (algebraMap ℤ ℚ))
            L.rationalFormMatrix_det_ne_zero)‖₊ : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold localPadicSpecialOrthogonalDifferentialLocalCorrection
  rw [
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection_eq_comparisonNorm_of_not_mem_massBadPrimeSet
      q hq,
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_eq_one_of_not_mem_massBadPrimeSet
      q hq,
    mul_one]

/-- Away from both finite exceptional sets, the combined local correction is
one. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_one_of_not_mem
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hqSP : q ∉ massBadPrimeSet L)
    (hqBasis :
      q ∉ skewAdjointFixedFormElementaryDetPrimeSupport
        L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection q.1 = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_comparisonNorm_of_not_mem_massBadPrimeSet
      q hqSP,
    nnnorm_skewAdjointFixedFormElementaryDetScalar_eq_one_of_not_mem
      L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero q hqBasis]
  rfl

/-- Failure of the combined local correction to equal one is supported on at
least one of the two finite exceptional sets. -/
theorem
    mem_massBadPrimeSet_or_mem_skewAdjointFixedFormElementaryDetPrimeSupport_of_localPadicSpecialOrthogonalDifferentialLocalCorrection_ne_one
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hne :
      letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
      L.localPadicSpecialOrthogonalDifferentialLocalCorrection q.1 ≠ 1) :
    q ∈ massBadPrimeSet L ∨
      q ∈ skewAdjointFixedFormElementaryDetPrimeSupport
        L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero := by
  by_cases hqSP : q ∈ massBadPrimeSet L
  · exact Or.inl hqSP
  · apply Or.inr
    by_contra hqBasis
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    exact hne
      (L.localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_one_of_not_mem
        q hqSP hqBasis)

end PositiveDefiniteIntegralLattice
