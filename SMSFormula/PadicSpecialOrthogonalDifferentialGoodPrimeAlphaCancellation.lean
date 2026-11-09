import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizerVolumeIntrinsicCoordinateMass

/-!
# Good-prime cancellation against the Schulze--Pillot local factor

This module rewrites the selected-depth formula for `normalizedLocalDensity` in
`ENNReal` and compares it with the intrinsic corrected special-stabilizer
volume outside the finite bad-prime set.

The associated-bilinear quotient count is strictly positive and finite, so it
can be cancelled.  The resulting equivalence reduces the comparison to a
coordinate-normalization identity.  It does not assert that identity or use a
reference-Haar comparison.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem ennreal_eq_of_mul_eq_mul_right
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

/-- At the selected corrected differential density depth, the real
Schulze--Pillot local factor becomes an exact finite `ENNReal` product after
multiplication by two. -/
theorem
    ENNReal_ofReal_normalizedLocalDensity_mul_two_eq_coordinateNormalization_mul_associatedBilinearDualQuotientCount_at_densityDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ENNReal.ofReal (normalizedLocalDensity L p) * (2 : ℝ≥0∞) =
      ENNReal.ofReal
          (((twoPadicNormInvPow p n *
              ((p : ℚ) ^
                localDensityDenominatorExponent n
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    p))⁻¹ : ℚ) : ℝ) *
            gramDetPadicNormFactor L p) *
        (associatedBilinearDualQuotientCount L p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            p) : ℝ≥0∞) := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  let e := localDensityDenominatorExponent n k
  let Q := associatedBilinearDualQuotientCount L p k
  let T : ℚ := twoPadicNormInvPow p n
  let G : ℝ := gramDetPadicNormFactor L p
  let N : ℝ := ((T * ((p : ℚ) ^ e)⁻¹ : ℚ) : ℝ) * G
  have hpq : 0 < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpowq : 0 < (p : ℚ) ^ e := pow_pos hpq _
  have hTq : 0 < T := by
    exact twoPadicNormInvPow_pos p n
  have hbaseq : 0 < T * ((p : ℚ) ^ e)⁻¹ :=
    mul_pos hTq (inv_pos.mpr hpowq)
  have hbase : 0 < ((T * ((p : ℚ) ^ e)⁻¹ : ℚ) : ℝ) := by
    exact_mod_cast hbaseq
  have hG : 0 < G :=
    gramDetPadicNormFactor_pos L p
  have hnormalization : 0 < N :=
    mul_pos hbase hG
  have hreal :
      normalizedLocalDensity L p * 2 =
        N * Q := by
    rw [
      L.normalizedLocalDensity_eq_associatedBilinearDualQuotientCount_at_localPadicSpecialOrthogonalDifferentialDensityDepth
        p]
    change
      (((((1 / 2 : ℚ) * T * ((p : ℚ) ^ e)⁻¹ * (Q : ℚ) : ℚ) : ℝ) *
          G) * 2) =
        N * Q
    unfold N
    push_cast
    ring
  change
    ENNReal.ofReal (normalizedLocalDensity L p) * (2 : ℝ≥0∞) =
      ENNReal.ofReal N * (Q : ℝ≥0∞)
  calc
    ENNReal.ofReal (normalizedLocalDensity L p) * (2 : ℝ≥0∞) =
        ENNReal.ofReal (normalizedLocalDensity L p * 2) := by
      rw [ENNReal.ofReal_mul (normalizedLocalDensity_pos L p).le]
      norm_num
    _ = ENNReal.ofReal (N * Q) := by
      rw [hreal]
    _ = ENNReal.ofReal N * ENNReal.ofReal (Q : ℝ) := by
      rw [ENNReal.ofReal_mul hnormalization.le]
    _ = ENNReal.ofReal N * (Q : ℝ≥0∞) := by
      rw [ENNReal.ofReal_natCast]

/-- Outside the finite bad-prime set, equality of the internally constructed
corrected special-stabilizer volume with `normalizedLocalDensity` is equivalent
to exactly one intrinsic coordinate-normalization identity. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_ENNReal_ofReal_normalizedLocalDensity_iff_coordinateNormalization_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ massBadPrimeSet L) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
          ENNReal.ofReal (normalizedLocalDensity L q.1) ↔
      (‖(2 : ℚ_[q.1])‖₊ ^
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra
              L.rationalFormMatrix) : ℝ≥0∞) *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              q.1) =
        ENNReal.ofReal
          (((twoPadicNormInvPow q.1 n *
              ((q.1 : ℚ) ^
                localDensityDenominatorExponent n
                  (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                    q.1))⁻¹ : ℚ) : ℝ) *
            gramDetPadicNormFactor L q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let Q :=
    associatedBilinearDualQuotientCount L q.1
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
  let A : ℝ≥0∞ :=
    (‖(2 : ℚ_[q.1])‖₊ ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          L.rationalFormMatrix) : ℝ≥0∞) *
      skewAdjointPadicCoordinateMeasure L.rationalFormMatrix q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          q.1)
  let B : ℝ≥0∞ :=
    ENNReal.ofReal
      (((twoPadicNormInvPow q.1 n *
          ((q.1 : ℚ) ^
            localDensityDenominatorExponent n
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                q.1))⁻¹ : ℚ) : ℝ) *
        gramDetPadicNormFactor L q.1)
  have hQpos : 0 < Q := by
    unfold Q associatedBilinearDualQuotientCount
    exact
      coordinateLocalDualQuotientCount_pos_of_admissible L q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
        (associatedBilinearDualPadicDenominatorIntegralPreimage L q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1))
        (associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
          (n := n) L q.1
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1)
          (L.isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            q.1).associated_bilinear_quadratic_depth)
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hQpos.ne'
  have hQtop : (Q : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hvolume :
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          (2 : ℝ≥0∞) =
        A * (Q : ℝ≥0∞) := by
    simpa [A, Q] using
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_mul_two_eq_zeroDensity_mul_coordinateMeasure_mul_quotientCount_of_not_mem_massBadPrimeSet
        q hq
  have halpha :
      ENNReal.ofReal (normalizedLocalDensity L q.1) * (2 : ℝ≥0∞) =
        B * (Q : ℝ≥0∞) := by
    simpa [B, Q] using
      L.ENNReal_ofReal_normalizedLocalDensity_mul_two_eq_coordinateNormalization_mul_associatedBilinearDualQuotientCount_at_densityDepth
        q.1
  change
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 =
          ENNReal.ofReal (normalizedLocalDensity L q.1) ↔
      A = B
  constructor
  · intro h
    apply ennreal_eq_of_mul_eq_mul_right hQ0 hQtop
    calc
      A * (Q : ℝ≥0∞) =
          L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
            (2 : ℝ≥0∞) :=
        hvolume.symm
      _ = ENNReal.ofReal (normalizedLocalDensity L q.1) * (2 : ℝ≥0∞) := by
        rw [h]
      _ = B * (Q : ℝ≥0∞) :=
        halpha
  · intro h
    apply ennreal_eq_of_mul_eq_mul_right
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    calc
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1 *
          (2 : ℝ≥0∞) =
        A * (Q : ℝ≥0∞) :=
      hvolume
      _ = B * (Q : ℝ≥0∞) := by rw [h]
      _ = ENNReal.ofReal (normalizedLocalDensity L q.1) * (2 : ℝ≥0∞) :=
        halpha.symm

end PositiveDefiniteIntegralLattice
