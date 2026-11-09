import SMSFormula.QuadraticAnisotropicVectorHaar
import SMSFormula.RationalQuadraticIsometrySpinCandidateCrossWitnessCoefficient

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace QuadraticMap.IsometryEquiv

variable {field space : Type*} [NontriviallyNormedField field] [CompleteSpace field]
  [CharZero field] [NormedAddCommGroup space] [NormedSpace field space]
  [FiniteDimensional field space] (form : QuadraticForm field space)

def valueFiberMap (isometry : form.IsometryEquiv form) (value : field) :
    {vector : space // form vector = value} → {vector : space // form vector = value} :=
  fun vector ↦ ⟨isometry vector.val, (isometry.map_app vector.val).trans vector.property⟩

omit [CharZero field] in
theorem continuous_valueFiberMap (isometry : form.IsometryEquiv form) (value : field) :
    Continuous (isometry.valueFiberMap form value) :=
  (isometry.toLinearEquiv.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk _

def anisotropicOrthogonalContinuousLinearEquiv (isometry : form.IsometryEquiv form) (point : space) :
    form.anisotropicOrthogonal point ≃L[field] form.anisotropicOrthogonal (isometry point) :=
  (isometry.restrictBetweenAnisotropicOrthogonals form point (isometry point) rfl).toLinearEquiv.toContinuousLinearEquiv

theorem coe_anisotropicOrthogonalContinuousLinearEquiv (isometry : form.IsometryEquiv form)
    (point : space) (transverse : form.anisotropicOrthogonal point) :
    (isometry.anisotropicOrthogonalContinuousLinearEquiv form point transverse : space) = isometry transverse := rfl

theorem anisotropicOrthogonalDecomposition_transport (isometry : form.IsometryEquiv form)
    (point : space) (hpoint : form point ≠ 0)
    (coordinates : form.anisotropicOrthogonal point × field) :
    form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
      (by simpa only [isometry.map_app] using hpoint)
      (isometry.anisotropicOrthogonalContinuousLinearEquiv form point coordinates.1, coordinates.2) =
    isometry (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint coordinates) := by
  simp only [QuadraticMap.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply,
    coe_anisotropicOrthogonalContinuousLinearEquiv, map_add, map_smul]

theorem anisotropicOrthogonalCoordinates_transport (isometry : form.IsometryEquiv form)
    (point : space) (hpoint : form point ≠ 0) (vector : space) :
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
      (by simpa only [isometry.map_app] using hpoint)).symm (isometry vector) =
    (isometry.anisotropicOrthogonalContinuousLinearEquiv form point
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).1,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2) := by
  apply (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
    (by simpa only [isometry.map_app] using hpoint)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, isometry.anisotropicOrthogonalDecomposition_transport form point hpoint,
    ContinuousLinearEquiv.apply_symm_apply]

variable [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace space] [BorelSpace space] [MeasurableSpace field] [BorelSpace field]
  [SecondCountableTopology field]

omit [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace field] [BorelSpace field] [SecondCountableTopology field] in
theorem isAddHaarMeasure_map_anisotropicOrthogonal (isometry : form.IsometryEquiv form)
    (point : space) (transverseHaar : Measure (form.anisotropicOrthogonal point))
    [transverseHaar.IsAddHaarMeasure] :
    (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar).IsAddHaarMeasure :=
  (isometry.anisotropicOrthogonalContinuousLinearEquiv form point).isAddHaarMeasure_map transverseHaar

def vectorHaarModulus (isometry : form.IsometryEquiv form) (vectorHaar : Measure space)
    [vectorHaar.IsAddHaarMeasure] : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.map isometry.toLinearEquiv.toContinuousLinearEquiv vectorHaar) vectorHaar

omit [CharZero field] [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace field] [BorelSpace field] [SecondCountableTopology field] in
theorem vectorHaarModulus_pos (isometry : form.IsometryEquiv form) (vectorHaar : Measure space)
    [vectorHaar.IsAddHaarMeasure] : 0 < isometry.vectorHaarModulus form vectorHaar := by
  letI := isometry.toLinearEquiv.toContinuousLinearEquiv.isAddHaarMeasure_map vectorHaar
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

omit [CharZero field] [MeasurableSpace field] [BorelSpace field] [SecondCountableTopology field] in
theorem map_vectorHaar (isometry : form.IsometryEquiv form) (vectorHaar : Measure space)
    [vectorHaar.IsAddHaarMeasure] :
    Measure.map isometry.toLinearEquiv.toContinuousLinearEquiv vectorHaar =
      isometry.vectorHaarModulus form vectorHaar • vectorHaar := by
  letI := isometry.toLinearEquiv.toContinuousLinearEquiv.isAddHaarMeasure_map vectorHaar
  exact Measure.isAddLeftInvariant_eq_smul _ _

theorem map_transported_anisotropicOrthogonal_productHaar
    (isometry : form.IsometryEquiv form) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure field)
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] [SigmaFinite transverseHaar] [SigmaFinite scalarHaar] :
    Measure.map (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
      (by simpa only [isometry.map_app] using hpoint))
      ((Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar).prod scalarHaar) =
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar *
      isometry.vectorHaarModulus form vectorHaar) • vectorHaar := by
  have hproduct :
      (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar).prod scalarHaar =
      Measure.map (Prod.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) id)
        (transverseHaar.prod scalarHaar) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map transverseHaar scalarHaar
        (isometry.anisotropicOrthogonalContinuousLinearEquiv form point).continuous.measurable measurable_id)
  rw [hproduct, Measure.map_map
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
      (by simpa only [isometry.map_app] using hpoint)).continuous.measurable
    ((isometry.anisotropicOrthogonalContinuousLinearEquiv form point).continuous.measurable.prodMap measurable_id)]
  have hcommute :
      (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
        (by simpa only [isometry.map_app] using hpoint)) ∘
        Prod.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) id =
      isometry.toLinearEquiv.toContinuousLinearEquiv ∘
        form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint := by
    funext coordinates
    exact isometry.anisotropicOrthogonalDecomposition_transport form point hpoint coordinates
  rw [hcommute, ← Measure.map_map isometry.toLinearEquiv.toContinuousLinearEquiv.continuous.measurable
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).continuous.measurable,
    form.map_anisotropicOrthogonal_productHaar point hpoint transverseHaar scalarHaar vectorHaar,
    Measure.map_smul, isometry.map_vectorHaar form vectorHaar, smul_smul]

theorem anisotropicOrthogonalProductHaarScalar_transport
    (isometry : form.IsometryEquiv form) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (scalarHaar : Measure field)
    (vectorHaar : Measure space) [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure]
    [vectorHaar.IsAddHaarMeasure] [SigmaFinite transverseHaar] [SigmaFinite scalarHaar] :
    form.anisotropicOrthogonalProductHaarScalar (isometry point)
      (by simpa only [isometry.map_app] using hpoint)
      (Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar)
      scalarHaar vectorHaar =
    form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar *
      isometry.vectorHaarModulus form vectorHaar := by
  change Measure.addHaarScalarFactor
    (Measure.map (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
      (by simpa only [isometry.map_app] using hpoint))
      ((Measure.map (isometry.anisotropicOrthogonalContinuousLinearEquiv form point) transverseHaar).prod scalarHaar))
    vectorHaar = _
  simp only [isometry.map_transported_anisotropicOrthogonal_productHaar form point hpoint transverseHaar scalarHaar vectorHaar,
    Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one]

end QuadraticMap.IsometryEquiv
