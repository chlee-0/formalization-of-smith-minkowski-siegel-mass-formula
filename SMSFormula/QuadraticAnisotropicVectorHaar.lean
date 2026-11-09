import SMSFormula.QuadraticAnisotropicDecompositionIsometry
import SMSFormula.QuadraticRegularValueDifferential
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace QuadraticMap

variable {field space : Type*} [NontriviallyNormedField field] [CompleteSpace field]
  [CharZero field] [NormedAddCommGroup space] [NormedSpace field space]
  [FiniteDimensional field space]

def anisotropicOrthogonalDecompositionContinuousLinearEquiv
    (form : QuadraticForm field space) (point : space) (hpoint : form point ≠ 0) :
    (form.anisotropicOrthogonal point × field) ≃L[field] space :=
  (form.anisotropicOrthogonalDecompositionEquiv point hpoint).toContinuousLinearEquiv

theorem anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply
    (form : QuadraticForm field space) (point : space) (hpoint : form point ≠ 0)
    (coordinates : form.anisotropicOrthogonal point × field) :
    form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint coordinates =
      coordinates.2 • point + coordinates.1 :=
  form.anisotropicOrthogonalDecompositionEquiv_apply point hpoint coordinates.1 coordinates.2

variable [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace space] [BorelSpace space] [MeasurableSpace field] [BorelSpace field]
  (form : QuadraticForm field space) (point : space) (hpoint : form point ≠ 0)
  (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure field)
  (vectorHaar : Measure space)
  [Measure.IsAddHaarMeasure transverseHaar] [Measure.IsAddHaarMeasure scalarHaar]
  [Measure.IsAddHaarMeasure vectorHaar] [SigmaFinite transverseHaar] [SigmaFinite scalarHaar]

def anisotropicOrthogonalProductHaarScalar : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (Measure.map (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint)
      (transverseHaar.prod scalarHaar)) vectorHaar

omit [LocallyCompactSpace space] in
theorem anisotropicOrthogonalProductHaarScalar_pos :
    0 < form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar := by
  let equivalence := form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint
  letI : Measure.IsAddHaarMeasure (Measure.map equivalence (transverseHaar.prod scalarHaar)) :=
    equivalence.isAddHaarMeasure_map _
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem map_anisotropicOrthogonal_productHaar :
    Measure.map (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint)
      (transverseHaar.prod scalarHaar) =
      form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar •
        vectorHaar := by
  let equivalence := form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint
  letI : Measure.IsAddHaarMeasure (Measure.map equivalence (transverseHaar.prod scalarHaar)) :=
    equivalence.isAddHaarMeasure_map _
  exact Measure.isAddLeftInvariant_eq_smul _ _

theorem lintegral_anisotropicOrthogonal_productHaar
    (integrand : space → ℝ≥0∞) (hintegrand : Measurable integrand) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞) *
        (∫⁻ vector, integrand vector ∂vectorHaar) =
      ∫⁻ transverse, ∫⁻ scalar, integrand (scalar • point + transverse) ∂scalarHaar ∂transverseHaar := by
  let equivalence := form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint
  have hmap := form.map_anisotropicOrthogonal_productHaar point hpoint transverseHaar scalarHaar vectorHaar
  calc
    _ = ∫⁻ vector, integrand vector ∂Measure.map equivalence (transverseHaar.prod scalarHaar) := by
      rw [hmap, lintegral_smul_measure]
      rfl
    _ = ∫⁻ coordinates, integrand (equivalence coordinates) ∂transverseHaar.prod scalarHaar :=
      lintegral_map hintegrand equivalence.continuous.measurable
    _ = _ := by
      rw [lintegral_prod (fun coordinates => integrand (equivalence coordinates))
        (hintegrand.comp equivalence.continuous.measurable).aemeasurable]
      simp only [equivalence, anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply]

theorem lintegral_quadraticValue_anisotropicOrthogonal
    (weight : space → ℝ≥0∞) (hweight : Measurable weight)
    (test : field → ℝ≥0∞) (htest : Measurable test) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞) *
        (∫⁻ vector, weight vector * test (form vector) ∂vectorHaar) =
      ∫⁻ transverse : form.anisotropicOrthogonal point, ∫⁻ scalar,
        weight (scalar • point + transverse) *
          test (form.orthogonalRestriction point transverse + scalar ^ 2 * form point)
        ∂scalarHaar ∂transverseHaar := by
  have hcontinuous : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector => (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  rw [form.lintegral_anisotropicOrthogonal_productHaar point hpoint transverseHaar scalarHaar vectorHaar
    (fun vector => weight vector * test (form vector)) (hweight.mul (htest.comp hcontinuous.measurable))]
  apply lintegral_congr
  intro transverse
  apply lintegral_congr
  intro scalar
  congr 2
  have hvalue := (form.anisotropicOrthogonalDecompositionIsometryEquiv point hpoint).map_app
    (transverse, scalar)
  simpa only [anisotropicOrthogonalDecompositionIsometryEquiv_apply, anisotropicOrthogonalSum,
    prod_apply, anisotropicScalarLine_apply_eq_sq_mul] using hvalue

theorem lintegral_quadraticValueMeasure_anisotropicOrthogonal
    (weight : space → ℝ≥0∞) (hweight : Measurable weight)
    (test : field → ℝ≥0∞) (htest : Measurable test) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞) *
        (∫⁻ value, test value ∂Measure.map form (vectorHaar.withDensity weight)) =
      ∫⁻ transverse : form.anisotropicOrthogonal point, ∫⁻ scalar,
        weight (scalar • point + transverse) *
          test (form.orthogonalRestriction point transverse + scalar ^ 2 * form point)
        ∂scalarHaar ∂transverseHaar := by
  have hcontinuous : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector => (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  rw [lintegral_map htest hcontinuous.measurable,
    lintegral_withDensity_eq_lintegral_mul vectorHaar hweight
      (g := fun vector => test (form vector)) (htest.comp hcontinuous.measurable)]
  exact form.lintegral_quadraticValue_anisotropicOrthogonal point hpoint transverseHaar scalarHaar
    vectorHaar weight hweight test htest

end QuadraticMap
