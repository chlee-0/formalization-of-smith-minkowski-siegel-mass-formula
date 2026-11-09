import SMSFormula.QuadraticScalarOrthogonalTransport

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace QuadraticMap

variable {field space : Type*} [NontriviallyNormedField field] [CompleteSpace field]
  [CharZero field] [NormedAddCommGroup space] [NormedSpace field space]
  [FiniteDimensional field space] [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace space] [BorelSpace space] [MeasurableSpace field] [BorelSpace field]
  [SecondCountableTopology field]

def scalarVectorHaarModulus (scalar : field) (hscalar : scalar ≠ 0)
    (vectorHaar : Measure space) [vectorHaar.IsAddHaarMeasure] : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (Measure.map (LinearEquiv.smulOfNeZero field space scalar hscalar).toContinuousLinearEquiv vectorHaar)
    vectorHaar

omit [CharZero field] [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace field] [BorelSpace field] [SecondCountableTopology field] in
theorem scalarVectorHaarModulus_pos (scalar : field) (hscalar : scalar ≠ 0)
    (vectorHaar : Measure space) [vectorHaar.IsAddHaarMeasure] :
    0 < scalarVectorHaarModulus scalar hscalar vectorHaar := by
  letI := (LinearEquiv.smulOfNeZero field space scalar hscalar).toContinuousLinearEquiv.isAddHaarMeasure_map vectorHaar
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

omit [CharZero field] [MeasurableSpace field] [BorelSpace field] [SecondCountableTopology field] in
theorem map_scalarVectorHaar (scalar : field) (hscalar : scalar ≠ 0)
    (vectorHaar : Measure space) [vectorHaar.IsAddHaarMeasure] :
    Measure.map (LinearEquiv.smulOfNeZero field space scalar hscalar).toContinuousLinearEquiv vectorHaar =
      scalarVectorHaarModulus scalar hscalar vectorHaar • vectorHaar := by
  letI := (LinearEquiv.smulOfNeZero field space scalar hscalar).toContinuousLinearEquiv.isAddHaarMeasure_map vectorHaar
  exact Measure.isAddLeftInvariant_eq_smul _ _

theorem map_scalar_anisotropicOrthogonal_productHaar (form : QuadraticForm field space)
    (point : space) (hpoint : form point ≠ 0) (scalar : field) (hscalar : scalar ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure field)
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] [SigmaFinite transverseHaar] [SigmaFinite scalarHaar] :
    Measure.map (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar))
      ((Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseHaar).prod scalarHaar) =
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar *
      scalarVectorHaarModulus scalar hscalar vectorHaar) • vectorHaar := by
  have hproduct :
      (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseHaar).prod scalarHaar =
      Measure.map (Prod.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) id)
        (transverseHaar.prod scalarHaar) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map transverseHaar scalarHaar
        (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar).continuous.measurable measurable_id)
  rw [hproduct, Measure.map_map
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)).continuous.measurable
    ((form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar).continuous.measurable.prodMap measurable_id)]
  have hcommute :
      (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
        (form.quadratic_smul_ne_zero point hpoint scalar hscalar)) ∘
        Prod.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) id =
      (LinearEquiv.smulOfNeZero field space scalar hscalar).toContinuousLinearEquiv ∘
        form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint := by
    funext coordinates
    exact form.anisotropicOrthogonalDecomposition_scalar point hpoint scalar hscalar coordinates
  rw [hcommute, ← Measure.map_map
    (LinearEquiv.smulOfNeZero field space scalar hscalar).toContinuousLinearEquiv.continuous.measurable
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).continuous.measurable,
    form.map_anisotropicOrthogonal_productHaar point hpoint transverseHaar scalarHaar vectorHaar,
    Measure.map_smul, map_scalarVectorHaar scalar hscalar vectorHaar, smul_smul]

theorem anisotropicOrthogonalProductHaarScalar_scalar (form : QuadraticForm field space)
    (point : space) (hpoint : form point ≠ 0) (scalar : field) (hscalar : scalar ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure field)
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] [SigmaFinite transverseHaar] [SigmaFinite scalarHaar] :
    form.anisotropicOrthogonalProductHaarScalar (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)
      (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseHaar)
      scalarHaar vectorHaar =
    form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar *
      scalarVectorHaarModulus scalar hscalar vectorHaar := by
  change Measure.addHaarScalarFactor
    (Measure.map (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar))
      ((Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseHaar).prod scalarHaar))
    vectorHaar = _
  simp only [form.map_scalar_anisotropicOrthogonal_productHaar point hpoint scalar hscalar
    transverseHaar scalarHaar vectorHaar,
    Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one]

end QuadraticMap
