import SMSFormula.PadicCoordinateVectorHaar
import SMSFormula.QuadraticAnisotropicVectorHaar
import SMSFormula.RationalCliffordGeneralSpinUnitSquareLocalChart
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import SMSFormula.ContinuousDensityNormalization
import SMSFormula.OpenRegionCompactTestMeasureExt
import SMSFormula.QuadraticIsometryOrthogonalHaarTransport
import SMSFormula.QuadraticPadicSquareBranchHaarIndependence
import SMSFormula.RationalSpecialOrthogonalSpinorNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

theorem map_real_coordinateHaar_of_det_eq_one {index : Type*} [Fintype index]
    (haar : Measure (index → ℝ)) [haar.IsAddHaarMeasure]
    (linear : (index → ℝ) ≃L[ℝ] (index → ℝ))
    (hdet : LinearMap.det linear.toLinearMap = 1) : Measure.map linear haar = haar := by
  simpa only [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] using
    map_linearMap_addHaar_pi_eq_smul_addHaar (hdet.trans_ne one_ne_zero) haar

end MeasureTheory.Measure

namespace RationalQuadraticSpaceMatrix

variable {rank : ℕ} (space : RationalQuadraticSpaceMatrix rank)

theorem specialOrthogonalMatrixGroupIsometryEquiv_det_eq_one
    (field : Type*) [Field field] [CharZero field] [Algebra ℚ field]
    (element : space.specialOrthogonalMatrixGroup field) :
    LinearMap.det (space.specialOrthogonalMatrixGroupIsometryEquiv field element).toLinearEquiv.toLinearMap = 1 := by
  have hdet := (space.specialOrthogonalMatrixGroupDetOneIsometryHom field element).property
  simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val hdet

theorem map_realSpecialOrthogonal_vectorHaar
    (element : space.specialOrthogonalMatrixGroup ℝ)
    (vectorHaar : Measure (Fin rank → ℝ)) [vectorHaar.IsAddHaarMeasure] :
    Measure.map (space.specialOrthogonalMatrixGroupIsometryEquiv ℝ element).toLinearEquiv.toContinuousLinearEquiv
      vectorHaar = vectorHaar :=
  Measure.map_real_coordinateHaar_of_det_eq_one vectorHaar _
    (space.specialOrthogonalMatrixGroupIsometryEquiv_det_eq_one ℝ element)

theorem realSpecialOrthogonal_vectorHaarModulus_eq_one
    (element : space.specialOrthogonalMatrixGroup ℝ)
    (vectorHaar : Measure (Fin rank → ℝ)) [vectorHaar.IsAddHaarMeasure] :
    (space.specialOrthogonalMatrixGroupIsometryEquiv ℝ element).vectorHaarModulus
      (space.commutativeScalarExtensionQuadraticForm ℝ) vectorHaar = 1 := by
  simp only [QuadraticMap.IsometryEquiv.vectorHaarModulus,
    space.map_realSpecialOrthogonal_vectorHaar element vectorHaar, Measure.addHaarScalarFactor_self]

section Padic

variable (prime : ℕ) [Fact prime.Prime]

local instance specialOrthogonalVectorHaarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance specialOrthogonalVectorHaarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

theorem map_padicSpecialOrthogonal_vectorHaar
    (element : space.specialOrthogonalMatrixGroup ℚ_[prime])
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (Fin rank → ℚ_[prime]))
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] :
    Measure.map (space.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[prime] element).toLinearEquiv.toContinuousLinearEquiv
      vectorHaar = vectorHaar :=
  Padic.map_vectorHaar_of_det_eq_one prime scalarHaar vectorHaar _
    (space.specialOrthogonalMatrixGroupIsometryEquiv_det_eq_one ℚ_[prime] element)

theorem padicSpecialOrthogonal_vectorHaarModulus_eq_one
    (element : space.specialOrthogonalMatrixGroup ℚ_[prime])
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (Fin rank → ℚ_[prime]))
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] :
    (space.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[prime] element).vectorHaarModulus
      (space.commutativeScalarExtensionQuadraticForm ℚ_[prime]) vectorHaar = 1 := by
  simp only [QuadraticMap.IsometryEquiv.vectorHaarModulus,
    space.map_padicSpecialOrthogonal_vectorHaar prime element scalarHaar vectorHaar, Measure.addHaarScalarFactor_self]

theorem padicSpecialOrthogonal_normalized_branch_covariance
    (element : space.specialOrthogonalMatrixGroup ℚ_[prime]) (point : Fin rank → ℚ_[prime])
    (hpoint : space.commutativeScalarExtensionQuadraticForm ℚ_[prime] point ≠ 0)
    (sourceHaar : Measure ((space.commutativeScalarExtensionQuadraticForm ℚ_[prime]).anisotropicOrthogonal point))
    (targetHaar : Measure ((space.commutativeScalarExtensionQuadraticForm ℚ_[prime]).anisotropicOrthogonal
      (space.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[prime] element point)))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure (Fin rank → ℚ_[prime]))
    [sourceHaar.IsAddHaarMeasure] [targetHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    let form := space.commutativeScalarExtensionQuadraticForm ℚ_[prime]
    let isometry := space.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[prime] element
    (form.anisotropicOrthogonalProductHaarScalar (isometry point)
      (by simpa only [form, isometry.map_app] using hpoint) targetHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (isometry point)
        (by simpa only [form, isometry.map_app] using hpoint) targetHaar value =
    Measure.map (isometry.valueFiberMap form value)
      ((form.anisotropicOrthogonalProductHaarScalar point hpoint sourceHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime point hpoint sourceHaar value) := by
  simpa only [space.padicSpecialOrthogonal_vectorHaarModulus_eq_one prime element scalarHaar vectorHaar,
    ENNReal.coe_one, inv_one, one_smul] using
    (space.commutativeScalarExtensionQuadraticForm ℚ_[prime]).padicSquareBranchFiberMeasure_normalized_isometry_of_targetHaar prime
      (space.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[prime] element) point hpoint sourceHaar targetHaar
      scalarHaar vectorHaar value

end Padic

end RationalQuadraticSpaceMatrix
