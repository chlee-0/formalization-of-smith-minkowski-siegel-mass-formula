import SMSFormula.SpecialOrthogonalRealLatticeDifferentialMass
import SMSFormula.SpecialOrthogonalAdelicDifferentialProperMassRearrangement
import SMSFormula.RationalSpecialOrthogonalAdelicTangentTopology
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume

/-!
# Differential normalization certificate for the sound adelic Weil datum

The measurable-Weil identity alone is invariant under simultaneous scalar
rescaling.  This module collects the additional facts that fix
the internally constructed datum to the rational invariant differential:

* the full adelic tangent measure is the pushforward of the canonical
  additive coordinate measure;
* its standard rational parallelotope has mass one;
* the finite inverse stabilizer volume is the limit of the internally
  constructed local differential cutoff products; and
* the ambient and quotient measures are the constructed
  differential datum.

The resulting certificate is rigid under common scalar rescaling.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Normalization evidence tying a sound measurable-Weil datum
to the rational invariant differential and the convergent finite differential
product. -/
structure
    RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix) : Prop where
  data_eq :
    D =
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP
  tangentCoordinateMeasure_eq :
    L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure =
      Measure.map
        L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateContinuousLinearEquiv
        L.rationalQuadraticSpaceMatrix.invariantDifferentialAdeleCoordinateNormalization.measure
  tangentStandardParallelotope_eq_one :
    L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure
        L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentStandardParallelotope =
      1
  finiteInverseVolumeProduct_tendsto :
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
        P)

namespace RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate

/-- An actual cutoff convergence certificate produces the complete
differential normalization certificate for the constructed
measurable-Weil datum. -/
def of_massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
      L inst hP
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP) := by
  letI : NeZero n := ⟨by
    intro hn
    subst n
    exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))⟩
  refine
    { data_eq := rfl
      tangentCoordinateMeasure_eq :=
        L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map_continuousLinearEquiv
      tangentStandardParallelotope_eq_one :=
        L.rationalQuadraticSpaceMatrix.fullAdelicSkewAdjointTangentCoordinateMeasure_standardParallelotope
      finiteInverseVolumeProduct_tendsto := ?_ }
  exact
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo
      hconv

/-- A certified datum's quotient mass is nonzero. -/
theorem tamagawaNumberENNReal_ne_zero
    {L : PositiveDefiniteIntegralLattice n} [Nonempty (Fin n)]
    {inst : Fintype L.ConcreteProperRationalDoubleCosetSet}
    {P : ℝ} {hP : 0 < P}
    {D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP D) :
    D.tamagawaNumberENNReal ≠ 0 := by
  rw [
    C.data_eq,
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_real_mul_finiteVolume_mul_properClassGenusMass
      inst hP
  ]
  apply mul_ne_zero
  · exact L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
  apply mul_ne_zero
  · exact
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P
  apply ENNReal.ofReal_ne_zero_iff.mpr
  exact_mod_cast L.properClassGenusMass_pos

/-- A certified datum's quotient mass is finite. -/
theorem tamagawaNumberENNReal_ne_top
    {L : PositiveDefiniteIntegralLattice n} [Nonempty (Fin n)]
    {inst : Fintype L.ConcreteProperRationalDoubleCosetSet}
    {P : ℝ} {hP : 0 < P}
    {D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP D) :
    D.tamagawaNumberENNReal ≠ ⊤ := by
  rw [
    C.data_eq,
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_tamagawaNumberENNReal_eq_real_mul_finiteVolume_mul_properClassGenusMass
      inst hP
  ]
  apply ENNReal.mul_ne_top
  · exact L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
  apply ENNReal.mul_ne_top
  · exact
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP
  exact ENNReal.ofReal_ne_top

/-- The differential normalization certificate excludes every nontrivial
simultaneous scalar rescaling of its ambient and quotient measures. -/
theorem smul_normalized_iff
    {L : PositiveDefiniteIntegralLattice n} [Nonempty (Fin n)]
    {inst : Fintype L.ConcreteProperRationalDoubleCosetSet}
    {P : ℝ} {hP : 0 < P}
    {D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP D)
    (c : ℝ≥0∞) :
    RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP (D.smul c) ↔
      c = 1 := by
  constructor
  · intro Cc
    have hdata : D.smul c = D :=
      Cc.data_eq.trans C.data_eq.symm
    have hmass := congrArg
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData.tamagawaNumberENNReal
      hdata
    rw [
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData.tamagawaNumberENNReal_smul
    ] at hmass
    let m := D.tamagawaNumberENNReal
    have hm0 : m ≠ 0 := C.tamagawaNumberENNReal_ne_zero
    have hmtop : m ≠ ⊤ := C.tamagawaNumberENNReal_ne_top
    change c * m = m at hmass
    calc
      c = c * (m * m⁻¹) := by
        rw [ENNReal.mul_inv_cancel hm0 hmtop, mul_one]
      _ = (c * m) * m⁻¹ := by ac_rfl
      _ = m * m⁻¹ := by rw [hmass]
      _ = 1 := ENNReal.mul_inv_cancel hm0 hmtop
  · rintro rfl
    have hsmul : D.smul 1 = D := by
      cases D
      simp [
        RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData.smul
      ]
    exact
      { data_eq := hsmul.trans C.data_eq
        tangentCoordinateMeasure_eq := C.tangentCoordinateMeasure_eq
        tangentStandardParallelotope_eq_one :=
          C.tangentStandardParallelotope_eq_one
        finiteInverseVolumeProduct_tendsto :=
          C.finiteInverseVolumeProduct_tendsto }

end RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate

end PositiveDefiniteIntegralLattice
