import SMSFormula.SpecialOrthogonalAdelicDifferentialMeasurableWeilQuotientVolume
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume

/-!
# Symbolic proper-mass rearrangement of the differential quotient volume

The internally normalized measurable-Weil quotient identity is rearranged
using only certified nonzero finite `ENNReal` factors.  The real
differential total mass and named finite differential stabilizer volume are
cancelled by their literal reciprocals, leaving the quotient mass symbolic.

The finite inverse volume is then unfolded only far enough to expose the
unevaluated local correction product and the real cutoff-product limit.  No
real-place evaluation, `toReal` distribution, proper-to-ordinary conversion,
reference-Haar comparison, or Tamagawa-number specialization occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The compact real differential Haar has finite total mass. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ ≠ ⊤ := by
  letI : IsFiniteMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
  exact ne_of_lt IsFiniteMeasure.measure_univ_lt_top

/-- Solving the internally normalized quotient-volume identity for proper
class genus mass leaves the sound measurable-Weil quotient mass symbolic and
uses the named reciprocal real and finite-place volumes. -/
theorem
    properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume_mul_differentialTamagawaNumber
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
            P *
          (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
            inst hP).tamagawaNumberENNReal) := by
  let R : ℝ≥0∞ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ
  let I : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P
  let V : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  let M : ℝ≥0∞ :=
    ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ))
  let τ : ℝ≥0∞ :=
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal
  change M = R⁻¹ * (I * τ)
  have hR0 : R ≠ 0 := by
    exact L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
  have hRtop : R ≠ ⊤ := by
    exact L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
  have hIV : I * V = 1 := by
    exact
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_mul_volume_eq_one
        hP
  have hτ : τ = R * (V * M) := by
    exact
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_real_mul_finiteVolume_mul_properClassGenusMass
        inst hP
  calc
    M = (R⁻¹ * R) * ((I * V) * M) := by
      rw [ENNReal.inv_mul_cancel hR0 hRtop, hIV]
      simp
    _ = R⁻¹ * (I * (R * (V * M))) := by
      ac_rfl
    _ = R⁻¹ * (I * τ) := by
      rw [hτ]

/-- Local-correction form of the symbolic proper-mass rearrangement.
The canonical finite correction product is left unevaluated. -/
theorem
    properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_localCorrectionInverse_mul_cutoffLimit_mul_differentialTamagawaNumber
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        ((L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct⁻¹ *
            ENNReal.ofReal P) *
          (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
            inst hP).tamagawaNumberENNReal) := by
  rw [
    L.properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume_mul_differentialTamagawaNumber
      inst hP
  ]
  rfl

/-- Concrete-quotient form of the same symbolic proper-mass rearrangement. -/
theorem
    properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume_mul_concreteDifferentialQuotientMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) =
      (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
            P *
          L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P
            Set.univ) := by
  rw [
    L.properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume_mul_differentialTamagawaNumber
      inst hP,
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_concrete
      inst hP
  ]

end PositiveDefiniteIntegralLattice
