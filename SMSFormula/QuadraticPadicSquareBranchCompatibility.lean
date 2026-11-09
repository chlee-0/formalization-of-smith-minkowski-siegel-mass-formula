import SMSFormula.QuadraticPadicSquareBranchContinuity
import SMSFormula.ContinuousDensityNormalization

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchCompatibilityMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchCompatibilityBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]

omit [MeasurableSpace space] [BorelSpace space] in
theorem padicSquareBranchWeight_eq_of_support (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (weight : space → ℝ)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) :
    form.padicSquareBranchWeight prime point hpoint (fun vector ↦ ENNReal.ofReal (weight vector)) =
      (fun vector ↦ ENNReal.ofReal (weight vector)) := by
  classical
  funext vector
  by_cases hzero : weight vector = 0
  · simp [padicSquareBranchWeight, Set.indicator, hzero]
  · unfold padicSquareBranchWeight
    exact Set.indicator_of_mem (show vector ∈ _ from hbranch vector (subset_tsupport weight hzero))
      (fun vector ↦ ENNReal.ofReal (weight vector))

variable [LocallyCompactSpace space] [SecondCountableTopology space]

theorem padicSquareBranch_normalized_density_eq
    (form : QuadraticForm ℚ_[prime] space) (firstPoint secondPoint : space)
    (hfirst : form firstPoint ≠ 0) (hsecond : form secondPoint ≠ 0)
    (firstHaar : Measure (form.anisotropicOrthogonal firstPoint))
    (secondHaar : Measure (form.anisotropicOrthogonal secondPoint))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [firstHaar.IsAddHaarMeasure] [secondHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (weight : space → ℝ) (hweight : Continuous weight) (hcompact : HasCompactSupport weight)
    (hfirstBranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv firstPoint hfirst).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime)
    (hsecondBranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv secondPoint hsecond).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) (value : ℚ_[prime]) :
    form.padicSquareBranchValueDensity prime firstPoint firstHaar (fun vector ↦ ENNReal.ofReal (weight vector)) value /
      (form.anisotropicOrthogonalProductHaarScalar firstPoint hfirst firstHaar scalarHaar vectorHaar : ℝ≥0∞) =
    form.padicSquareBranchValueDensity prime secondPoint secondHaar (fun vector ↦ ENNReal.ofReal (weight vector)) value /
      (form.anisotropicOrthogonalProductHaarScalar secondPoint hsecond secondHaar scalarHaar vectorHaar : ℝ≥0∞) := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal firstPoint) :=
    (form.anisotropicOrthogonal firstPoint).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : LocallyCompactSpace (form.anisotropicOrthogonal secondPoint) :=
    (form.anisotropicOrthogonal secondPoint).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hfirstMeasure := form.map_padicSquareBranch_withDensity prime firstPoint hfirst firstHaar scalarHaar vectorHaar
    (fun vector ↦ ENNReal.ofReal (weight vector)) hweight.measurable.ennreal_ofReal
  have hsecondMeasure := form.map_padicSquareBranch_withDensity prime secondPoint hsecond secondHaar scalarHaar vectorHaar
    (fun vector ↦ ENNReal.ofReal (weight vector)) hweight.measurable.ennreal_ofReal
  rw [form.padicSquareBranchWeight_eq_of_support prime firstPoint hfirst weight hfirstBranch] at hfirstMeasure
  rw [form.padicSquareBranchWeight_eq_of_support prime secondPoint hsecond weight hsecondBranch] at hsecondMeasure
  exact congrFun (Measure.continuous_density_div_eq_of_smul_eq scalarHaar
    (Measure.map form (vectorHaar.withDensity (fun vector ↦ ENNReal.ofReal (weight vector)))) _ _
    (form.continuous_padicSquareBranchValueDensity_of_compactSupport prime firstPoint hfirst firstHaar
      weight hweight hcompact hfirstBranch)
    (form.continuous_padicSquareBranchValueDensity_of_compactSupport prime secondPoint hsecond secondHaar
      weight hweight hcompact hsecondBranch) _ _
    (ne_of_gt (form.anisotropicOrthogonalProductHaarScalar_pos firstPoint hfirst firstHaar scalarHaar vectorHaar))
    (ne_of_gt (form.anisotropicOrthogonalProductHaarScalar_pos secondPoint hsecond secondHaar scalarHaar vectorHaar))
    hfirstMeasure hsecondMeasure) value

end QuadraticMap
