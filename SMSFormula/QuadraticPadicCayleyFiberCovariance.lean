import SMSFormula.QuadraticPadicCayleyLerayBranch
import SMSFormula.RationalSpecialOrthogonalVectorHaar

/-! The normalized fiber measure at `x_old` and its group translates. For the
unit Haars on lower coordinates and on the higher coordinate space, and a
supplied Haar `ν` on `ℚ_p`, the product Haar scalar of the anisotropic
decomposition at `x_old = e_last` is `ν(ℤ_p)`, so the normalized fiber
measure at `x_old` is `ν(ℤ_p)⁻¹` times the lower-coordinate fiber measure that
carries the local Leray identity. By the special-orthogonal covariance
(vector-Haar modulus one), the normalized fiber measure at every translate
`g · x_old` is the push-forward of that one along `g`, so translates of a fiber
piece have equal normalized mass. No chart, section, baseline or scalar Haar
normalization is chosen: `ν` is supplied and appears explicitly. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance fcPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance fcPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

/-- The product Haar scalar of the anisotropic decomposition at `x_old`, for
the unit Haars and a supplied scalar Haar `ν`, is `ν(ℤ_p)`. -/
theorem anisotropicOrthogonalProductHaarScalar_last_unitHaar :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalProductHaarScalar
      lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) ν
      (Padic.unitHaar p (Fin (n+1))) : ℝ≥0∞) = ν (closedBall 0 1) := by
  set q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] with hq
  have hx : q lastCoordinateVector ≠ 0 := by
    rw [hq, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha
  set e := W.lastOrthogonalLowerEquiv a ha p with he
  set D := q.anisotropicOrthogonalDecompositionContinuousLinearEquiv lastCoordinateVector hx with hD
  haveI : (Measure.map e.symm (Padic.unitHaar p (Fin n))).IsAddHaarMeasure :=
    e.symm.isAddHaarMeasure_map _
  haveI : ProperSpace (q.anisotropicOrthogonal lastCoordinateVector) := FiniteDimensional.proper ℚ_[p] _
  haveI : SigmaFinite (Measure.map e.symm (Padic.unitHaar p (Fin n))) := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.map D ((Measure.map e.symm (Padic.unitHaar p (Fin n))).prod ν)).IsAddHaarMeasure := D.isAddHaarMeasure_map _
  have hsmul := Measure.isAddLeftInvariant_eq_smul (Measure.map D ((Measure.map e.symm (Padic.unitHaar p (Fin n))).prod ν))
    (Padic.unitHaar p (Fin (n+1)))
  have hball : MeasurableSet (closedBall (0 : Fin (n+1) → ℚ_[p]) 1) := measurableSet_closedBall
  have hpre : D ⁻¹' closedBall (0 : Fin (n+1) → ℚ_[p]) 1 =
      (e ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1) ×ˢ closedBall (0 : ℚ_[p]) 1 := by
    ext ⟨t, u⟩
    have h1 : ∀ i : Fin n, (u • (lastCoordinateVector : Fin (n+1) → ℚ_[p]) + t.1) i.castSucc =
        e t i := by
      intro i
      rw [he, lastOrthogonalLowerEquiv_apply]
      simp [lastCoordinateVector, Fin.castSucc_ne_last]
    have h2 : (u • (lastCoordinateVector : Fin (n+1) → ℚ_[p]) + t.1) (Fin.last n) = u := by
      simp [lastCoordinateVector, W.lastOrthogonal_coordinate_zero a ha t]
    simp only [mem_preimage, mem_prod, mem_closedBall_zero_iff]
    rw [hD, anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply,
      pi_norm_le_iff_of_nonneg zero_le_one, pi_norm_le_iff_of_nonneg zero_le_one,
      Fin.forall_fin_succ', h2]
    simp only [h1]
  have hcube : Measure.map D ((Measure.map e.symm (Padic.unitHaar p (Fin n))).prod ν) (closedBall 0 1) = ν (closedBall 0 1) := by
    rw [Measure.map_apply D.continuous.measurable hball, hpre, Measure.prod_prod,
      Measure.map_apply e.symm.continuous.measurable
        (measurableSet_closedBall.preimage e.continuous.measurable)]
    have hid : e.symm ⁻¹' (e ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1) = closedBall 0 1 := by
      ext w; simp
    rw [hid, Padic.unitHaar_unitCube, one_mul]
  have h := congrArg (fun m : Measure (Fin (n+1) → ℚ_[p]) ↦ m (closedBall 0 1)) hsmul
  simp only [Measure.smul_apply, Padic.unitHaar_unitCube, ENNReal.smul_def, smul_eq_mul, mul_one] at h
  rw [hcube] at h
  exact h.symm

/-- The normalized fiber measure at `x_old` is `ν(ℤ_p)⁻¹` times the
lower-coordinate fiber measure. -/
theorem normalized_lastSquareBranchFiberMeasure_eq (value : ℚ_[p]) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalProductHaarScalar
      lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) ν
      (Padic.unitHaar p (Fin (n+1))) : ℝ≥0∞)⁻¹ •
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
        p lastCoordinateVector
        (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) value =
    (ν (closedBall 0 1))⁻¹ •
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
        p lastCoordinateVector
        (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) value := by
  rw [W.anisotropicOrthogonalProductHaarScalar_last_unitHaar a ha p ν]

/-- Group translates of the normalized fiber measure: for every element `g` of
the higher special-orthogonal group and every Haar on the anisotropic complement
of `g · x_old`, the normalized fiber measure at `g · x_old` is the push-forward
along `g` of `ν(ℤ_p)⁻¹` times the lower-coordinate fiber measure at `x_old`. -/
theorem normalized_fiberMeasure_translate
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])
    (targetHaar : Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)))
    [targetHaar.IsAddHaarMeasure] (value : ℚ_[p]) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalProductHaarScalar
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)
      (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last];
          exact (map_ne_zero _).mpr ha)
      targetHaar ν (Padic.unitHaar p (Fin (n+1))) : ℝ≥0∞)⁻¹ •
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
        p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)
        (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last];
            exact (map_ne_zero _).mpr ha)
        targetHaar value =
    Measure.map (((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) value)
      ((ν (closedBall 0 1))⁻¹ •
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
          p lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) value) := by
  haveI : (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))).IsAddHaarMeasure :=
    (W.lastOrthogonalLowerEquiv a ha p).symm.isAddHaarMeasure_map _
  rw [← W.normalized_lastSquareBranchFiberMeasure_eq a ha p ν value]
  exact (W.nonisotropicLastExtension a ha).padicSpecialOrthogonal_normalized_branch_covariance p g
    lastCoordinateVector
    (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
    (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n)))
    targetHaar ν (Padic.unitHaar p (Fin (n+1))) value

/-- Equal normalized masses of translates: the normalized fiber mass at `g · x_old`
of a measurable fiber set is `ν(ℤ_p)⁻¹` times the lower-coordinate fiber mass at
`x_old` of its pull-back along `g`. -/
theorem normalized_fiberMeasure_translate_apply
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])
    (targetHaar : Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)))
    [targetHaar.IsAddHaarMeasure] (value : ℚ_[p])
    {T : Set {y : Fin (n+1) → ℚ_[p] //
      (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = value}}
    (hT : MeasurableSet T) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalProductHaarScalar
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)
      (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last];
          exact (map_ne_zero _).mpr ha)
      targetHaar ν (Padic.unitHaar p (Fin (n+1))) : ℝ≥0∞)⁻¹ *
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
        p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)
        (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last];
            exact (map_ne_zero _).mpr ha)
        targetHaar value T =
    (ν (closedBall 0 1))⁻¹ *
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure
        p lastCoordinateVector
        (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) value
        ((((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) value) ⁻¹' T) := by
  have h := congrArg (fun m ↦ m T) (W.normalized_fiberMeasure_translate a ha p ν g targetHaar value)
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rw [h, Measure.map_apply ((QuadraticMap.IsometryEquiv.continuous_valueFiberMap _ _ _).measurable) hT,
    Measure.smul_apply, smul_eq_mul]

end RationalQuadraticSpaceMatrix
