import SMSFormula.RationalSpecialOrthogonalRawFullAdelicDifferentialNormalization
import SMSFormula.SpecialOrthogonalAdelicMeasurableWeilMeasureData

/-!
# Raw invariant-differential measurable-Weil data

This module combines the sound measurable-Weil datum with the
corrected raw full-adelic differential normalization.  The quotient measure
and measurable Weil identity remain exactly those stored in the
datum; the structure adds only the connected ambient normalization.

For the lattice datum, the differential normalization
certificate supplies the finite stabilizer-volume
scale.  No scalar rescaling, quotient-mass evaluation, Tamagawa theorem,
genus mass, local density, or reference Haar measure occurs.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Sound measurable-Weil data whose ambient measure has the corrected raw
invariant-differential normalization with the explicit finite scale `a`. -/
structure IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
    (V : RationalQuadraticSpaceMatrix n)
    (a : ℝ≥0∞)
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) : Prop where
  adelicMeasure_normalized :
    V.IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale
      a D.adelicMeasure

/-- Sound measurable-Weil data whose ambient measure has the corrected raw
invariant-differential normalization at its certified finite scale. -/
structure IsRawInvariantDifferentialMeasurableWeilMeasureData
    (V : RationalQuadraticSpaceMatrix n)
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V) : Prop where
  adelicMeasure_normalized :
    V.IsRawInvariantDifferentialFullAdelicGroupMeasure D.adelicMeasure

namespace IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale

/-- Forgetting the explicit finite scale gives the corrected raw
measurable-Weil normalization. -/
def toIsRawInvariantDifferentialMeasurableWeilMeasureData
    {V : RationalQuadraticSpaceMatrix n}
    {a : ℝ≥0∞}
    {D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V}
    (C : IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale V a D) :
    IsRawInvariantDifferentialMeasurableWeilMeasureData V D :=
  ⟨a, C.adelicMeasure_normalized⟩

end IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {n : ℕ}

namespace RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate

/-- A datum-level differential certificate gives the corresponding ambient
certificate without changing either measure or the stored Weil identity. -/
def toAmbientCertificate
    {L : PositiveDefiniteIntegralLattice n} [Nonempty (Fin n)] [NeZero n]
    {inst : Fintype L.ConcreteProperRationalDoubleCosetSet}
    {P : ℝ} {hP : 0 < P}
    {D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP D) :
    RationalQuadraticSpaceMatrixFullAdelicAmbientDifferentialNormalizationCertificate
      L P D.adelicMeasure := by
  refine
    { measure_eq := ?_
      tangentCoordinateMeasure_eq := C.tangentCoordinateMeasure_eq
      tangentStandardParallelotope_eq_one :=
        C.tangentStandardParallelotope_eq_one
      finiteInverseVolumeProduct_tendsto :=
        C.finiteInverseVolumeProduct_tendsto }
  have hdata := congrArg
    RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData.adelicMeasure
    C.data_eq
  simpa only [
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData]
    using hdata

/-- A certified lattice datum has the corrected raw measurable-Weil
normalization at the finite stabilizer-volume scale. -/
def toIsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
    {L : PositiveDefiniteIntegralLattice n} [Nonempty (Fin n)]
    {inst : Fintype L.ConcreteProperRationalDoubleCosetSet}
    {P : ℝ} {hP : 0 < P}
    {D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP D) :
    L.rationalQuadraticSpaceMatrix
        |>.IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
          (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)
          D := by
  letI : NeZero n := ⟨by
    intro hn
    subst n
    exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))⟩
  exact ⟨
    RationalQuadraticSpaceMatrix.IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale.of_latticeAmbientCertificate
      L hP C.toAmbientCertificate⟩

/-- A certified lattice datum satisfies the existential corrected
raw measurable-Weil normalization. -/
def toIsRawInvariantDifferentialMeasurableWeilMeasureData
    {L : PositiveDefiniteIntegralLattice n} [Nonempty (Fin n)]
    {inst : Fintype L.ConcreteProperRationalDoubleCosetSet}
    {P : ℝ} {hP : 0 < P}
    {D :
      RationalQuadraticSpaceMatrix.SpecialOrthogonalAdelicMeasurableWeilMeasureData
        L.rationalQuadraticSpaceMatrix}
    (C :
      RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate
        L inst hP D) :
    L.rationalQuadraticSpaceMatrix
        |>.IsRawInvariantDifferentialMeasurableWeilMeasureData D :=
  C.toIsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
    |>.toIsRawInvariantDifferentialMeasurableWeilMeasureData

end RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate

/-- The raw lattice differential measurable-Weil datum has the
corrected scale-explicit normalization whenever its local inverse products
have the certified cutoff limit. -/
def rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_isRawInvariantDifferentialWithScale
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix
        |>.IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
          (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)
          (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
            inst hP) :=
  (RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate.of_massLocalInverseProductTendsTo
      L inst hP hconv)
    |>.toIsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale

/-- The raw lattice differential measurable-Weil datum satisfies the
corrected existential normalization whenever its local inverse products have
the certified cutoff limit. -/
def rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_isRawInvariantDifferential
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix
        |>.IsRawInvariantDifferentialMeasurableWeilMeasureData
          (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
            inst hP) :=
  (RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate.of_massLocalInverseProductTendsTo
      L inst hP hconv)
    |>.toIsRawInvariantDifferentialMeasurableWeilMeasureData

end PositiveDefiniteIntegralLattice
