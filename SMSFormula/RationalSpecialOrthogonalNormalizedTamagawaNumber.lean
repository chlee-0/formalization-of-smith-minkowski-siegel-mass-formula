import SMSFormula.RationalSpecialOrthogonalNormalizedDifferentialMeasurableWeilMeasureData
import SMSFormula.RationalSpecialOrthogonalRawTamagawaNumber

/-!
# Reciprocal-volume-scaled special-orthogonal Tamagawa number

The raw lattice value two (`RationalSpecialOrthogonalRawTamagawaNumber`, proved
through intrinsic `tau(Spin)=1`) applies to the raw lattice datum, not to its
reciprocal-volume rescaling.  Combining the raw value two with the
scaling formula gives the normalized accessor as the finite stabilizer
inverse volume times two.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The reciprocal-volume-rescaled datum has the correspondingly scaled
Tamagawa accessor.  It is not asserted to have value two. -/
theorem rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_inverseVolume_mul_two
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal =
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹ *
          2 := by
  rw [L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal
    inst hP]
  rw [L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_two
    hn inst hP hconv]

/-- The same scaling statement with the named finite inverse-volume scalar. -/
theorem rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_finiteInverseVolume_mul_two
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P *
          2 := by
  rw [L.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_inverseVolume_mul_two
    hn inst hP hconv]
  rw [L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume]

end PositiveDefiniteIntegralLattice
