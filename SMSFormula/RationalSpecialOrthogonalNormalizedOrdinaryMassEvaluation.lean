import SMSFormula.RationalSpecialOrthogonalNormalizedOrdinaryMass
import SMSFormula.RationalSpecialOrthogonalNormalizedTamagawaNumber
import SMSFormula.SpecialOrthogonalRealLatticeDifferentialMass

/-!
# Evaluate normalized ordinary mass

The symbolic ordinary-mass theorem expresses the mass through the
reciprocal-volume-rescaled Tamagawa accessor divided by two.  This module
applies the raw value-two theorem.  Cancelling only the scalar two identifies
ordinary genus mass with the inverse real differential mass times the finite
stabilizer inverse volume.

The existing positive rational diagonalization then exposes the rational
congruence, positive-diagonal, fixed elementary, and Gamma factors, with one
inverse around their entire product.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- After the raw Tamagawa value is specialized, ordinary genus mass is the
inverse real differential mass times the finite stabilizer inverse volume. -/
theorem ordinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P := by
  rw [L.ordinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_inv_two_mul_normalizedTamagawaNumber
    inst hP]
  rw [L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_finiteInverseVolume_mul_two
    hn inst hP hconv]
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := by
    apply ENNReal.inv_mul_cancel <;> norm_num
  calc
    (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
          ((2 : ℝ≥0∞)⁻¹ *
            (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P * 2)) =
        (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
          (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P *
            ((2 : ℝ≥0∞)⁻¹ * 2)) := by ac_rfl
    _ = (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P := by
      rw [htwo, mul_one]

/-- A positive rational diagonalization evaluates ordinary genus mass while
retaining the inverse around the complete determinant-and-Gamma product. -/
theorem exists_ordinaryGenusMassENNReal_eq_inv_realGammaProduct_mul_finiteInverseVolume
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ∃ (d : Fin n → ℚ) (W : GL (Fin n) ℚ)
        (hd : ∀ i, 0 < d i),
      Matrix.skewAdjointCongruenceForm L.rationalFormMatrix W =
        Matrix.diagonal d ∧
      ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
        ((↑((Real.toNNReal
            |Matrix.skewAdjointRealCongruenceDetScalar
              L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) *
          ((↑((Real.toNNReal
              |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
            ((Real.toNNReal
                |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| :
                ℝ≥0∞) *
              ENNReal.ofReal
                ((2 : ℝ) ^ (n - 1) *
                    Real.pi ^
                      (((n - 1 : ℕ) : ℝ) *
                        (((n - 1 : ℕ) : ℝ) + 3) / 4) /
                  (∏ k ∈ Finset.range (n - 1),
                    Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))))))⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P := by
  letI : NeZero n := ⟨by
    intro hn0
    subst n
    exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))⟩
  obtain ⟨d, W, hd, hdiag, hreal⟩ :=
    L.exists_concreteRealSpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma
  refine ⟨d, W, hd, hdiag, ?_⟩
  rw [L.ordinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume
    hn inst hP hconv]
  rw [hreal]

end PositiveDefiniteIntegralLattice
