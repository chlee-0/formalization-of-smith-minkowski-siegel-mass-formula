import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientBind
import SMSFormula.RationalIdeleClassDifferentialWeilComparison

/-!
# Differential-Weil fibers on the horizontal GSpin quotient

The horizontal fiber measure uses Mathlib's independently selected Haar
measure on rational idele classes.  This file replaces only that fiber
normalization by the quotient induced from compact-normalized differential
idele Haar.  The orbit pushforward is unchanged, and the comparison scalar
from `RationalIdeleClassDifferentialWeilComparison` propagates through the
descended `SO`-indexed kernel and its bind.

Thus the concrete horizontal bind is exactly the independent class-Haar
scalar times a differential-Weil fiber bind over the raw `SO` quotient
measure.  No ambient `GSpin` quotient identity is asserted here; identifying
this differential bind with the calibrated fundamental-domain quotient is a
separate central-extension Weil argument.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The actual horizontal orbit measure obtained from the differential Weil
quotient on rational idele classes. -/
noncomputable def horizontalDifferentialWeilFiberMeasure
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.map
    (fun c : RationalIdeleClassGroup =>
      V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        c z)
    rationalIdeleClassDifferentialWeilQuotientMeasure

/-- Integration against a differential-Weil horizontal orbit is the literal
idele-class quotient integral. -/
theorem lintegral_horizontalDifferentialWeilFiberMeasure
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ w, f w ∂V.horizontalDifferentialWeilFiberMeasure z =
      ∫⁻ c : RationalIdeleClassGroup,
        f (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) ∂rationalIdeleClassDifferentialWeilQuotientMeasure := by
  rw [horizontalDifferentialWeilFiberMeasure]
  exact lintegral_map' hf.aemeasurable
    (V.measurable_rationalIdeleClassOrbitMap z).aemeasurable

/-- On an ambient representative, the differential-Weil orbit integral is
the restriction of differential idele Haar to its exact rational
fundamental domain. -/
theorem lintegral_horizontalDifferentialWeilFiberMeasure_mk
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (f : V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ w, f w
        ∂V.horizontalDifferentialWeilFiberMeasure
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
        f (V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a * x))
        ∂rationalIdeleDifferentialHaarMeasure := by
  rw [V.lintegral_horizontalDifferentialWeilFiberMeasure _ f hf,
    rationalIdeleClassDifferentialWeilQuotientMeasure]
  calc
    ∫⁻ c : RationalIdeleClassGroup,
        f (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x))
        ∂Measure.map rationalIdeleClassQuotientMap
          (rationalIdeleDifferentialHaarMeasure.restrict
            rationalIdeleMeasurableFundamentalDomain) =
      ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
        f (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          (rationalIdeleClassQuotientMap a)
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x))
        ∂rationalIdeleDifferentialHaarMeasure := by
      exact lintegral_map'
        (hf.comp
          (V.measurable_rationalIdeleClassOrbitMap
            (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x))).aemeasurable
        rationalIdeleClassQuotientMap_isCoveringMap.continuous.measurable.aemeasurable
    _ = _ := rfl

/-- The independently normalized horizontal fiber is the explicit class-Haar
conversion scalar times the differential-Weil orbit measure. -/
theorem horizontalFiberHaarMeasure_eq_smul_differentialWeilFiberMeasure
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.horizontalFiberHaarMeasure z =
      rationalIdeleClassHaarToDifferentialWeilScalar •
        V.horizontalDifferentialWeilFiberMeasure z := by
  rw [horizontalFiberHaarMeasure, horizontalDifferentialWeilFiberMeasure,
    rationalIdeleClassHaarMeasure_eq_smul_differentialWeilQuotient,
    Measure.map_smul]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

/-! ## Measurable descent over the rational adelic SO quotient -/

/-- A measurable `SO`-indexed kernel at differential-Weil idele-class scale.
It is defined by cancelling the certified nonzero class-Haar scalar from the
already measurable descended fiber kernel; the next theorem identifies every
value with the literal differential-Weil orbit pushforward. -/
noncomputable def horizontalDifferentialWeilFiberKernelAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    ProbabilityTheory.Kernel
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  let a := rationalIdeleClassHaarToDifferentialWeilScalar
  let κ := L.horizontalFiberHaarKernelAtSO inst
  ⟨fun q => a⁻¹ • κ q, by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply]
    exact measurable_const.mul (κ.measurable_coe hA)⟩

@[simp]
theorem horizontalDifferentialWeilFiberKernelAtSO_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.horizontalDifferentialWeilFiberKernelAtSO inst q =
      rationalIdeleClassHaarToDifferentialWeilScalar⁻¹ •
        L.horizontalFiberHaarKernelAtSO inst q :=
  rfl

/-- Every descended differential-Weil fiber is the literal orbit pushforward
through any representative supplied by the existing definition-only lift. -/
theorem horizontalDifferentialWeilFiberKernelAtSO_eq_orbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.horizontalDifferentialWeilFiberKernelAtSO inst q =
      L.rationalQuadraticSpaceMatrix.horizontalDifferentialWeilFiberMeasure
        (L.rationalQuadraticSpaceMatrix.horizontalFiberHaarKernelLift
          (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective
            L) q) := by
  let V := L.rationalQuadraticSpaceMatrix
  let z := V.horizontalFiberHaarKernelLift
    (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L) q
  rw [L.horizontalDifferentialWeilFiberKernelAtSO_apply inst q,
    L.horizontalFiberHaarKernelAtSO_apply]
  unfold RationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO
  rw [V.horizontalFiberHaarMeasure_eq_smul_differentialWeilFiberMeasure z,
    smul_smul]
  rw [inv_mul_cancel₀
    (rationalIdeleClassHaarToDifferentialWeilScalar_pos.ne')]
  exact one_smul _ _

/-- Pulling the descended differential-Weil kernel back along the actual
horizontal projection recovers the differential orbit through that point.
This is the section-free form used in the iterated Weil identity. -/
theorem horizontalDifferentialWeilFiberKernelAtSO_comp_horizontalMap
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    L.horizontalDifferentialWeilFiberKernelAtSO inst
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
          z) =
      L.rationalQuadraticSpaceMatrix.horizontalDifferentialWeilFiberMeasure z := by
  rw [L.horizontalDifferentialWeilFiberKernelAtSO_apply,
    L.horizontalFiberHaarKernelAtSO_comp_horizontalMap,
    L.rationalQuadraticSpaceMatrix.horizontalFiberHaarKernel_apply,
    L.rationalQuadraticSpaceMatrix.horizontalFiberHaarMeasure_eq_smul_differentialWeilFiberMeasure,
    smul_smul]
  rw [inv_mul_cancel₀
    (rationalIdeleClassHaarToDifferentialWeilScalar_pos.ne')]
  exact one_smul _ _

/-- Conversely the original descended class-Haar fiber is the explicit
comparison scalar times the descended differential-Weil fiber. -/
theorem horizontalFiberHaarKernelAtSO_eq_smul_differentialWeil
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.horizontalFiberHaarKernelAtSO inst q =
      rationalIdeleClassHaarToDifferentialWeilScalar •
        L.horizontalDifferentialWeilFiberKernelAtSO inst q := by
  rw [L.horizontalDifferentialWeilFiberKernelAtSO_apply inst q, smul_smul,
    mul_inv_cancel₀
      (rationalIdeleClassHaarToDifferentialWeilScalar_pos.ne'), one_smul]

/-! ## Binding over an arbitrary SO quotient measure -/

/-- Bind the literal differential-Weil central fibers against a measure on
the rational adelic `SO` quotient. -/
noncomputable def horizontalDifferentialWeilSOFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (μSO : Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.bind μSO (L.horizontalDifferentialWeilFiberKernelAtSO inst)

/-- The concrete class-Haar fiber bind differs from the differential-Weil
fiber bind by exactly the independent idele-class comparison scalar. -/
theorem horizontalSOFiberHaarBoundMeasure_eq_smul_differentialWeil
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (μSO : Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.horizontalSOFiberHaarBoundMeasure inst μSO =
      rationalIdeleClassHaarToDifferentialWeilScalar •
        L.horizontalDifferentialWeilSOFiberBoundMeasure inst μSO := by
  ext A hA
  rw [horizontalSOFiberHaarBoundMeasure,
    horizontalDifferentialWeilSOFiberBoundMeasure,
    Measure.bind_apply hA
      (L.horizontalFiberHaarKernelAtSO inst).measurable.aemeasurable,
    Measure.smul_apply,
    Measure.bind_apply hA
      (L.horizontalDifferentialWeilFiberKernelAtSO inst).measurable.aemeasurable]
  change
    (∫⁻ q, L.horizontalFiberHaarKernelAtSO inst q A ∂μSO) =
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        ∫⁻ q, L.horizontalDifferentialWeilFiberKernelAtSO inst q A ∂μSO
  simp_rw [L.horizontalFiberHaarKernelAtSO_eq_smul_differentialWeil inst,
    Measure.smul_apply]
  change
    (∫⁻ q,
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        L.horizontalDifferentialWeilFiberKernelAtSO inst q A ∂μSO) = _
  rw [lintegral_const_mul _
    ((L.horizontalDifferentialWeilFiberKernelAtSO inst).measurable_coe hA)]

/-- At the raw lattice `SO` quotient scale, the horizontal concrete bind
carries exactly the same independent idele-class conversion scalar. -/
theorem horizontalRawSOFiberHaarBoundMeasure_eq_smul_differentialWeil
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData) :
    L.horizontalRawSOFiberHaarBoundMeasure inst D =
      rationalIdeleClassHaarToDifferentialWeilScalar •
        L.horizontalDifferentialWeilSOFiberBoundMeasure inst
          D.specialOrthogonalData.quotientMeasure := by
  exact L.horizontalSOFiberHaarBoundMeasure_eq_smul_differentialWeil inst
    D.specialOrthogonalData.quotientMeasure

end PositiveDefiniteIntegralLattice
