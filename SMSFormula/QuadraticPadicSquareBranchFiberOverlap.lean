import SMSFormula.QuadraticPadicSquareBranchFiberFinite
import SMSFormula.QuadraticPadicSquareBranchCompatibility
import SMSFormula.OpenRegionCompactTestMeasureExt

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchFiberOverlapMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchFiberOverlapBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

def padicSquareBranchOverlap (form : QuadraticForm ℚ_[prime] space) (firstPoint secondPoint : space)
    (hfirst : form firstPoint ≠ 0) (hsecond : form secondPoint ≠ 0) : Set space :=
  {vector | ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv firstPoint hfirst).symm vector).2 ∈
      Rat.padicUnitSquareScalarSource prime ∧
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv secondPoint hsecond).symm vector).2 ∈
      Rat.padicUnitSquareScalarSource prime}

theorem isOpen_padicSquareBranchOverlap (form : QuadraticForm ℚ_[prime] space) (firstPoint secondPoint : space)
    (hfirst : form firstPoint ≠ 0) (hsecond : form secondPoint ≠ 0) :
    IsOpen (form.padicSquareBranchOverlap prime firstPoint secondPoint hfirst hsecond) :=
  ((Rat.isOpen_padicUnitSquareScalarSource prime).preimage
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv firstPoint hfirst).symm.continuous.snd).inter
  ((Rat.isOpen_padicUnitSquareScalarSource prime).preimage
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv secondPoint hsecond).symm.continuous.snd)

variable [LocallyCompactSpace space] [SecondCountableTopology space]
  [MeasurableSpace space] [BorelSpace space]

set_option backward.isDefEq.respectTransparency false in
theorem padicSquareBranchFiberMeasure_normalized_restrict_overlap_eq
    (form : QuadraticForm ℚ_[prime] space) (firstPoint secondPoint : space)
    (hfirst : form firstPoint ≠ 0) (hsecond : form secondPoint ≠ 0)
    (firstHaar : Measure (form.anisotropicOrthogonal firstPoint))
    (secondHaar : Measure (form.anisotropicOrthogonal secondPoint))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [firstHaar.IsAddHaarMeasure] [secondHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    ((form.anisotropicOrthogonalProductHaarScalar firstPoint hfirst firstHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime firstPoint hfirst firstHaar value).restrict
        (Subtype.val ⁻¹' form.padicSquareBranchOverlap prime firstPoint secondPoint hfirst hsecond) =
    ((form.anisotropicOrthogonalProductHaarScalar secondPoint hsecond secondHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime secondPoint hsecond secondHaar value).restrict
        (Subtype.val ⁻¹' form.padicSquareBranchOverlap prime firstPoint secondPoint hfirst hsecond) := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal firstPoint) :=
    (form.anisotropicOrthogonal firstPoint).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : LocallyCompactSpace (form.anisotropicOrthogonal secondPoint) :=
    (form.anisotropicOrthogonal secondPoint).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  apply Measure.closedSubtype_restrict_eq_of_compact_ambient_tests {vector | form vector = value}
    (isClosed_eq hform continuous_const) _ _ _
    (form.isOpen_padicSquareBranchOverlap prime firstPoint secondPoint hfirst hsecond)
  · intro compactSet hcompact hsubset
    erw [Measure.smul_apply]
    rw [smul_eq_mul]
    apply ENNReal.mul_lt_top
    · exact (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (ne_of_gt
        (form.anisotropicOrthogonalProductHaarScalar_pos firstPoint hfirst firstHaar scalarHaar vectorHaar)))).lt_top
    · apply form.padicSquareBranchFiberMeasure_compact_lt_top prime firstPoint hfirst firstHaar value compactSet hcompact
      intro vector hvector
      rw [form.range_padicSquareBranchFiberMap prime firstPoint hfirst value]
      exact (hsubset hvector).1
  · intro compactSet hcompact hsubset
    erw [Measure.smul_apply]
    rw [smul_eq_mul]
    apply ENNReal.mul_lt_top
    · exact (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (ne_of_gt
        (form.anisotropicOrthogonalProductHaarScalar_pos secondPoint hsecond secondHaar scalarHaar vectorHaar)))).lt_top
    · apply form.padicSquareBranchFiberMeasure_compact_lt_top prime secondPoint hsecond secondHaar value compactSet hcompact
      intro vector hvector
      rw [form.range_padicSquareBranchFiberMap prime secondPoint hsecond value]
      exact (hsubset hvector).2
  · intro weight hcontinuous hcompact hsupport
    simp only [lintegral_smul_measure, smul_eq_mul]
    erw [form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime firstPoint hfirst firstHaar value
      (fun vector ↦ ENNReal.ofReal (weight vector)) hcontinuous.measurable.ennreal_ofReal,
      form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime secondPoint hsecond secondHaar value
      (fun vector ↦ ENNReal.ofReal (weight vector)) hcontinuous.measurable.ennreal_ofReal]
    simpa only [div_eq_mul_inv, mul_comm] using
      form.padicSquareBranch_normalized_density_eq prime firstPoint secondPoint hfirst hsecond firstHaar secondHaar
        scalarHaar vectorHaar weight hcontinuous hcompact
        (fun vector hvector ↦ (hsupport hvector).1) (fun vector hvector ↦ (hsupport hvector).2) value

end QuadraticMap
