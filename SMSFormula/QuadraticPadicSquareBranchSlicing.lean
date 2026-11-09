import SMSFormula.QuadraticAnisotropicVectorHaar
import SMSFormula.RationalPadicUnitSquareAdditiveSubstitution

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]

def padicSquareBranchWeight (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (weight : space → ℝ≥0∞) : space → ℝ≥0∞ :=
  ((fun vector ↦ (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector |>.2) ⁻¹'
    Rat.padicUnitSquareScalarSource prime).indicator weight

theorem measurable_padicSquareBranchWeight (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (weight : space → ℝ≥0∞) (hweight : Measurable weight) :
    Measurable (form.padicSquareBranchWeight prime point hpoint weight) := by
  apply hweight.indicator
  exact (Rat.isOpen_padicUnitSquareScalarSource prime).measurableSet.preimage
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.snd.measurable)

omit [MeasurableSpace space] [BorelSpace space] in
theorem padicSquareBranchWeight_apply (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (weight : space → ℝ≥0∞)
    (transverse : form.anisotropicOrthogonal point) (scalar : ℚ_[prime]) :
    form.padicSquareBranchWeight prime point hpoint weight (scalar • point + transverse) =
      (Rat.padicUnitSquareScalarSource prime).indicator (fun value ↦ weight (value • point + transverse)) scalar := by
  classical
  have hcoordinates : (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
      (scalar • point + transverse) = (transverse, scalar) := by
    rw [← form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply point hpoint (transverse, scalar)]
    exact (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm_apply_apply _
  simp [padicSquareBranchWeight, Set.indicator, hcoordinates]

variable [LocallyCompactSpace space] [SecondCountableTopology space]

theorem lintegral_padicSquareBranch_valueMeasure (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (transverseHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [Measure.IsAddHaarMeasure transverseHaar] [Measure.IsAddHaarMeasure scalarHaar]
    [Measure.IsAddHaarMeasure vectorHaar]
    (weight : space → ℝ≥0∞) (hweight : Measurable weight)
    (test : ℚ_[prime] → ℝ≥0∞) (htest : Measurable test) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞) *
      (∫⁻ value, test value ∂Measure.map form
        (vectorHaar.withDensity (form.padicSquareBranchWeight prime point hpoint weight))) =
      ∫⁻ transverse : form.anisotropicOrthogonal point,
        ∫⁻ value in (fun unit : ℚ_[prime]ˣ ↦ form.orthogonalRestriction point transverse + form point * (unit : ℚ_[prime])) ''
          (Rat.unitSquareIdentityChart ℚ_[prime]).target,
          weight (Rat.padicUnitSquareScalarInverse prime
            ((value - form.orthogonalRestriction point transverse) / form point) • point + transverse) * test value /
            (‖2 * form point * Rat.padicUnitSquareScalarInverse prime
              ((value - form.orthogonalRestriction point transverse) / form point)‖₊ : ℝ≥0∞) ∂scalarHaar ∂transverseHaar := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal point) :=
    (form.anisotropicOrthogonal point).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  rw [form.lintegral_quadraticValueMeasure_anisotropicOrthogonal point hpoint transverseHaar scalarHaar vectorHaar
    (form.padicSquareBranchWeight prime point hpoint weight) (form.measurable_padicSquareBranchWeight prime point hpoint weight hweight)
    test htest]
  apply lintegral_congr
  intro transverse
  calc
    _ = ∫⁻ scalar, (Rat.padicUnitSquareScalarSource prime).indicator
        (fun value ↦ weight (value • point + transverse) *
          test (form.orthogonalRestriction point transverse + value ^ 2 * form point)) scalar ∂scalarHaar := by
      apply lintegral_congr
      intro scalar
      rw [form.padicSquareBranchWeight_apply, Set.indicator_mul_left]
    _ = ∫⁻ scalar in Rat.padicUnitSquareScalarSource prime, weight (scalar • point + transverse) *
        test (form.orthogonalRestriction point transverse + form point * scalar ^ 2) ∂scalarHaar := by
      rw [lintegral_indicator (Rat.isOpen_padicUnitSquareScalarSource prime).measurableSet]
      simp only [mul_comm (form point)]
    _ = _ := Rat.lintegral_padicUnitSquareScalarSource_weighted_value prime scalarHaar
      (form.orthogonalRestriction point transverse) (form point) hpoint
      (fun scalar ↦ weight (scalar • point + transverse)) test

end QuadraticMap
