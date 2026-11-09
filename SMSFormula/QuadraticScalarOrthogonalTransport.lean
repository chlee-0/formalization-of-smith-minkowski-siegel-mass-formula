import SMSFormula.QuadraticAnisotropicVectorHaar

noncomputable section

namespace QuadraticMap

variable {field space : Type*} [NontriviallyNormedField field] [CompleteSpace field]
  [CharZero field] [NormedAddCommGroup space] [NormedSpace field space]
  [FiniteDimensional field space]

omit [CompleteSpace field] [FiniteDimensional field space] in
theorem anisotropicOrthogonal_smul_eq (form : QuadraticForm field space)
    (point : space) (scalar : field) (hscalar : scalar ≠ 0) :
    form.anisotropicOrthogonal (scalar • point) = form.anisotropicOrthogonal point := by
  ext vector
  rw [form.mem_anisotropicOrthogonal_iff, form.mem_anisotropicOrthogonal_iff]
  change form.associated (scalar • point) vector = 0 ↔ form.associated point vector = 0
  simp [LinearMap.smul_apply, smul_eq_mul, hscalar]

def scalarOrthogonalContinuousLinearEquiv (form : QuadraticForm field space)
    (point : space) (scalar : field) (hscalar : scalar ≠ 0) :
    form.anisotropicOrthogonal point ≃L[field] form.anisotropicOrthogonal (scalar • point) :=
  (LinearEquiv.smulOfNeZero field (form.anisotropicOrthogonal point) scalar hscalar : form.anisotropicOrthogonal point ≃ₗ[field]
    form.anisotropicOrthogonal point).toContinuousLinearEquiv |>.trans
      (ContinuousLinearEquiv.ofEq _ _ (form.anisotropicOrthogonal_smul_eq point scalar hscalar).symm)

theorem coe_scalarOrthogonalContinuousLinearEquiv (form : QuadraticForm field space)
    (point : space) (scalar : field) (hscalar : scalar ≠ 0)
    (transverse : form.anisotropicOrthogonal point) :
    (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse : space) =
      scalar • (transverse : space) := rfl

omit [CompleteSpace field] [CharZero field] [FiniteDimensional field space] in
theorem quadratic_smul_ne_zero (form : QuadraticForm field space)
    (point : space) (hpoint : form point ≠ 0) (scalar : field) (hscalar : scalar ≠ 0) :
    form (scalar • point) ≠ 0 := by
  simpa only [QuadraticMap.map_smul, smul_eq_mul, pow_two] using mul_ne_zero (pow_ne_zero 2 hscalar) hpoint

theorem anisotropicOrthogonalDecomposition_scalar (form : QuadraticForm field space)
    (point : space) (hpoint : form point ≠ 0) (scalar : field) (hscalar : scalar ≠ 0)
    (coordinates : form.anisotropicOrthogonal point × field) :
    form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)
      (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar coordinates.1, coordinates.2) =
    scalar • form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint coordinates := by
  simp only [anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply,
    coe_scalarOrthogonalContinuousLinearEquiv, smul_add]
  rw [smul_comm coordinates.2 scalar point]

theorem anisotropicOrthogonalCoordinates_scalar (form : QuadraticForm field space)
    (point : space) (hpoint : form point ≠ 0) (scalar : field) (hscalar : scalar ≠ 0) (vector : space) :
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)).symm (scalar • vector) =
    (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).1,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2) := by
  apply (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
    (form.quadratic_smul_ne_zero point hpoint scalar hscalar)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, form.anisotropicOrthogonalDecomposition_scalar point hpoint scalar hscalar,
    ContinuousLinearEquiv.apply_symm_apply]

theorem scalarSquareBranchParameter (form : QuadraticForm field space)
    (point : space) (scalar : field) (hscalar : scalar ≠ 0)
    (transverse : form.anisotropicOrthogonal point) (value : field) :
    (scalar ^ 2 * value - form.orthogonalRestriction (scalar • point)
      (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse)) /
        form (scalar • point) = (value - form.orthogonalRestriction point transverse) / form point := by
  simp only [orthogonalRestriction_apply, coe_scalarOrthogonalContinuousLinearEquiv,
    QuadraticMap.map_smul, smul_eq_mul, ← pow_two]
  rw [← mul_sub, mul_div_mul_left _ _ (pow_ne_zero 2 hscalar)]

def scalarValueFiberMap (form : QuadraticForm field space) (scalar value : field) :
    {vector : space // form vector = value} → {vector : space // form vector = scalar ^ 2 * value} :=
  fun vector ↦ ⟨scalar • vector.val, by simp only [QuadraticMap.map_smul, smul_eq_mul, vector.property, pow_two]⟩

omit [CompleteSpace field] [CharZero field] [FiniteDimensional field space] in
theorem continuous_scalarValueFiberMap (form : QuadraticForm field space) (scalar value : field) :
    Continuous (form.scalarValueFiberMap scalar value) :=
  (continuous_const.smul continuous_subtype_val).subtype_mk _

end QuadraticMap
