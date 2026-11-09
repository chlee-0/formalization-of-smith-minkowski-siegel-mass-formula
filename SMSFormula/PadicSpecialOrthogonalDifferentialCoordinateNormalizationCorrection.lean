import SMSFormula.PadicSpecialOrthogonalDifferentialDensityFiberCorrection
import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeAlphaCancellation
import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeRationalBasisCorrection

/-!
# The exact p-adic coordinate-normalization correction

The all-prime alpha-cancellation statement isolates equality between the
intrinsic differential coordinate normalization and the Schulze--Pillot
coordinate normalization.  Both quantities are nonzero and finite: the first
is the mass of the density-adapted principal kernel, and the second is the
`ENNReal.ofReal` of an explicit positive product.

This module packages their ratio as a nonzero finite coordinate correction and
proves the local formula with both the coordinate and selected fiber
corrections.  At a Schulze--Pillot good prime, the coordinate correction is
exactly the p-adic norm of the rational basis-comparison determinant.  No
bad-prime value or prime product is evaluated.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The intrinsic differential coordinate normalization on the literal
density-adapted inverse-Cayley kernel. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0∞ :=
  (‖(2 : ℚ_[p])‖₊ ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞) *
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p)

/-- The selected-depth Schulze--Pillot coordinate normalization, before
multiplication by the associated-bilinear quotient count. -/
noncomputable def
    selectedCoordinateNormalizationENNReal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0∞ :=
  ENNReal.ofReal
    (((twoPadicNormInvPow p n *
        ((p : ℚ) ^
          localDensityDenominatorExponent n
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p))⁻¹ : ℚ) : ℝ) *
      gramDetPadicNormFactor L p)

/-- The intrinsic-to-Schulze--Pillot coordinate-normalization ratio. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0∞ :=
  L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization p *
    (L.selectedCoordinateNormalizationENNReal p)⁻¹

/-- The selected-depth Schulze--Pillot coordinate normalization is nonzero. -/
theorem selectedCoordinateNormalizationENNReal_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.selectedCoordinateNormalizationENNReal p ≠ 0 := by
  unfold selectedCoordinateNormalizationENNReal
  apply ENNReal.ofReal_ne_zero_iff.mpr
  have hpq : 0 < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpowq :
      0 <
        (p : ℚ) ^
          localDensityDenominatorExponent n
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) :=
    pow_pos hpq _
  have hbaseq :
      0 <
        twoPadicNormInvPow p n *
          ((p : ℚ) ^
            localDensityDenominatorExponent n
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p))⁻¹ :=
    mul_pos (twoPadicNormInvPow_pos p n) (inv_pos.mpr hpowq)
  have hbase :
      0 <
        (((twoPadicNormInvPow p n *
            ((p : ℚ) ^
              localDensityDenominatorExponent n
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                  p))⁻¹ : ℚ) : ℝ)) := by
    exact_mod_cast hbaseq
  exact
    mul_pos hbase (gramDetPadicNormFactor_pos L p)

/-- The selected-depth Schulze--Pillot coordinate normalization is finite. -/
theorem selectedCoordinateNormalizationENNReal_ne_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.selectedCoordinateNormalizationENNReal p ≠ ⊤ := by
  unfold selectedCoordinateNormalizationENNReal
  exact ENNReal.ofReal_ne_top

/-- The intrinsic differential coordinate normalization is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
        p ≠ 0 := by
  let reduction :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let c : ℝ≥0∞ := Nat.card reduction.range
  have hctop : c ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have hvolume0 :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p ≠ 0 :=
    (L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_pos p).ne'
  unfold localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
  rw [
    ← L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_zeroDensity_mul_coordinateMeasure
      p,
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_volume_mul_inv_natCard_range
      p]
  exact mul_ne_zero hvolume0 (ENNReal.inv_ne_zero.mpr hctop)

/-- The intrinsic differential coordinate normalization is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_ne_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
        p ≠ ⊤ := by
  let reduction :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let c : ℝ≥0∞ := Nat.card reduction.range
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (Nat.card_pos : 0 < Nat.card reduction.range).ne'
  have hvolumetop :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p ≠ ⊤ :=
    ne_of_lt
      (L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_lt_top p)
  unfold localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
  rw [
    ← L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_zeroDensity_mul_coordinateMeasure
      p,
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_volume_mul_inv_natCard_range
      p]
  exact
    ENNReal.mul_ne_top hvolumetop (ENNReal.inv_ne_top.mpr hc0)

/-- The coordinate-normalization correction is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
        p ≠ 0 := by
  unfold
    localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
  exact
    mul_ne_zero
      (L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_ne_zero
        p)
      (ENNReal.inv_ne_zero.mpr
        (L.selectedCoordinateNormalizationENNReal_ne_top p))

/-- The coordinate-normalization correction is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection_ne_top
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
        p ≠ ⊤ := by
  unfold
    localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
  exact
    ENNReal.mul_ne_top
      (L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_ne_top
        p)
      (ENNReal.inv_ne_top.mpr
        (L.selectedCoordinateNormalizationENNReal_ne_zero p))

/-- The intrinsic coordinate normalization is exactly its correction times
the selected-depth Schulze--Pillot coordinate normalization. -/
theorem
    localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_eq_coordinateNormalizationCorrection_mul_selectedCoordinateNormalization
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization
        p =
      L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
          p *
        L.selectedCoordinateNormalizationENNReal p := by
  let D :=
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization p
  let N := L.selectedCoordinateNormalizationENNReal p
  have hN0 : N ≠ 0 :=
    L.selectedCoordinateNormalizationENNReal_ne_zero p
  have hNtop : N ≠ ⊤ :=
    L.selectedCoordinateNormalizationENNReal_ne_top p
  change D = (D * N⁻¹) * N
  calc
    D = D * 1 := (mul_one D).symm
    _ = D * (N⁻¹ * N) := by
      rw [ENNReal.inv_mul_cancel hN0 hNtop]
    _ = (D * N⁻¹) * N := by rw [mul_assoc]

private theorem ennreal_eq_of_mul_eq_mul_right_finite
    {a b c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (h : a * c = b * c) :
    a = b := by
  calc
    a = a * 1 := (mul_one a).symm
    _ = a * (c * c⁻¹) := by
      rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = (a * c) * c⁻¹ := by rw [mul_assoc]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b * (c * c⁻¹) := by rw [mul_assoc]
    _ = b * 1 := by
      rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = b := mul_one b

/-- At every prime, the corrected special-stabilizer volume is exactly
`normalizedLocalDensity` multiplied by the intrinsic coordinate-normalization
correction and the selected-fiber correction. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_coordinateNormalizationCorrection_mul_densityFiberCorrection_mul_ENNReal_ofReal_normalizedLocalDensity
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p =
      L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
          p *
        L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p *
        ENNReal.ofReal (normalizedLocalDensity L p) := by
  let V :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p
  let D :=
    L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization p
  let s :=
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection p
  let r :=
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection p
  let A := ENNReal.ofReal (normalizedLocalDensity L p)
  let N := L.selectedCoordinateNormalizationENNReal p
  let Q :=
    associatedBilinearDualQuotientCount L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  have hD : D = s * N := by
    exact
      L.localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization_eq_coordinateNormalizationCorrection_mul_selectedCoordinateNormalization
        p
  have hvolume :
      V * (2 : ℝ≥0∞) = D * r * (Q : ℝ≥0∞) := by
    simpa only [
      V, D, r, Q,
      localPadicSpecialOrthogonalDifferentialIntrinsicCoordinateNormalization]
      using
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_densityFiberCorrection_mul_quotientCount
          p
  have halpha :
      A * (2 : ℝ≥0∞) = N * (Q : ℝ≥0∞) := by
    simpa only [
      A, N, Q, selectedCoordinateNormalizationENNReal]
      using
        L.ENNReal_ofReal_normalizedLocalDensity_mul_two_eq_coordinateNormalization_mul_associatedBilinearDualQuotientCount_at_densityDepth
          p
  apply
    ennreal_eq_of_mul_eq_mul_right_finite
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  calc
    V * (2 : ℝ≥0∞) =
        (D * r) * (Q : ℝ≥0∞) := hvolume
    _ = ((s * N) * r) * (Q : ℝ≥0∞) := by rw [hD]
    _ = (s * r) * (N * (Q : ℝ≥0∞)) := by ac_rfl
    _ = (s * r) * (A * (2 : ℝ≥0∞)) := by rw [halpha]
    _ = ((s * r) * A) * (2 : ℝ≥0∞) :=
      (mul_assoc (s * r) A (2 : ℝ≥0∞)).symm

/-- At a Schulze--Pillot good prime, the intrinsic coordinate-normalization
correction is exactly the p-adic norm of the rational fixed/form-adapted
basis-comparison determinant. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection_eq_comparisonNorm_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
        q.1 =
      (‖algebraMap ℚ ℚ_[q.1]
          (skewAdjointFixedFormElementaryDetScalar
            L.rationalFormMatrix
            (L.form_symm.map (algebraMap ℤ ℚ))
            L.rationalFormMatrix_det_ne_zero)‖₊ : ℝ≥0∞) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let s :=
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
      q.1
  let r :=
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection q.1
  let A := ENNReal.ofReal (normalizedLocalDensity L q.1)
  let c : ℝ≥0∞ :=
    ‖algebraMap ℚ ℚ_[q.1]
      (skewAdjointFixedFormElementaryDetScalar
        L.rationalFormMatrix
        (L.form_symm.map (algebraMap ℤ ℚ))
        L.rationalFormMatrix_det_ne_zero)‖₊
  have hA0 : A ≠ 0 := by
    exact
      ENNReal.ofReal_ne_zero_iff.mpr (normalizedLocalDensity_pos L q.1)
  have hAtop : A ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hr : r = 1 := by
    exact
      L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection_eq_one_of_not_mem_massBadPrimeSet
        q hq
  have hall :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
        s * A := by
    have h :=
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_coordinateNormalizationCorrection_mul_densityFiberCorrection_mul_ENNReal_ofReal_normalizedLocalDensity
        q.1
    simpa only [s, r, A, hr, mul_one] using h
  have hgood :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
        c * A := by
    exact
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_comparisonNorm_mul_ENNReal_ofReal_normalizedLocalDensity_of_not_mem_badPrimeSet
        q hq
  apply ennreal_eq_of_mul_eq_mul_right_finite hA0 hAtop
  calc
    s * A =
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 :=
      hall.symm
    _ = c * A := hgood

end PositiveDefiniteIntegralLattice
