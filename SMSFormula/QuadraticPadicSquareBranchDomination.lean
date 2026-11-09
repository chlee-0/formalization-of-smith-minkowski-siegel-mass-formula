import SMSFormula.QuadraticPadicSquareBranchKernel
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchDominationMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchDominationBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space]

def padicSquareBranchTransverseSupport (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (weight : space → ℝ) : Set (form.anisotropicOrthogonal point) :=
  (fun vector ↦ (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector |>.1) ''
    tsupport weight

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem isCompact_padicSquareBranchTransverseSupport (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (weight : space → ℝ)
    (hcompact : HasCompactSupport weight) :
    IsCompact (form.padicSquareBranchTransverseSupport prime point hpoint weight) :=
  hcompact.isCompact.image
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.fst

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem exists_pos_padicSquareBranch_jacobian_lower_bound (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (weight : space → ℝ)
    (hcompact : HasCompactSupport weight)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ vector ∈ tsupport weight,
      lower ≤ ‖2 * form point *
        ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2‖ := by
  apply hcompact.isCompact.exists_forall_le'
    ((continuous_const.mul
      (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous.snd).norm.continuousOn)
  intro vector hvector
  exact norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hpoint)
    (Rat.padicUnitSquareScalarSource_ne_zero prime (hbranch vector hvector)))

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchValueKernel_eq_zero_of_not_mem_transverseSupport
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (weight : space → ℝ) (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime])
    (htransverse : transverse ∉ form.padicSquareBranchTransverseSupport prime point hpoint weight) :
    form.padicSquareBranchValueKernel prime point (fun vector ↦ ENNReal.ofReal (weight vector))
      (transverse, value) = 0 := by
  classical
  unfold padicSquareBranchValueKernel
  by_cases htarget : (value - form.orthogonalRestriction point transverse) / form point ∈
      Rat.padicUnitSquareScalarTarget prime
  · rw [Set.indicator_of_mem (show (transverse, value) ∈ _ from htarget)]
    dsimp only
    let scalar := Rat.padicUnitSquareTargetSupportedInverse prime
      ((value - form.orthogonalRestriction point transverse) / form point)
    have hcoordinates : (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
        (scalar • point + transverse) = (transverse, scalar) := by
      rw [← form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply point hpoint (transverse, scalar)]
      exact (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm_apply_apply _
    have hzero : weight (scalar • point + transverse) = 0 := by
      by_contra hnonzero
      apply htransverse
      exact ⟨scalar • point + transverse, subset_tsupport weight hnonzero, congrArg Prod.fst hcoordinates⟩
    change ENNReal.ofReal (weight (scalar • point + transverse)) / _ = 0
    rw [hzero, ENNReal.ofReal_zero, ENNReal.zero_div]
  · exact Set.indicator_of_notMem (show (transverse, value) ∉ _ from htarget) _

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem exists_padicSquareBranchValueKernel_compact_majorant
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (weight : space → ℝ) (hweight : Continuous weight) (hcompact : HasCompactSupport weight)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ transverse value,
      form.padicSquareBranchValueKernel prime point (fun vector ↦ ENNReal.ofReal (weight vector))
        (transverse, value) ≤
      (form.padicSquareBranchTransverseSupport prime point hpoint weight).indicator
        (fun _ ↦ ENNReal.ofReal bound) transverse := by
  classical
  let coordinates := (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
  have hdenominator : Continuous (fun vector ↦ ‖2 * form point * (coordinates vector).2‖) :=
    (continuous_const.mul coordinates.continuous.snd).norm
  obtain ⟨lower, hlower, hlower_bound⟩ :=
    form.exists_pos_padicSquareBranch_jacobian_lower_bound prime point hpoint weight hcompact hbranch
  have hratio : ContinuousOn (fun vector ↦ weight vector / ‖2 * form point * (coordinates vector).2‖)
      (tsupport weight) := hweight.continuousOn.div hdenominator.continuousOn
        (fun vector hvector ↦ ne_of_gt (hlower.trans_le (hlower_bound vector hvector)))
  obtain ⟨bound, hbound⟩ := hcompact.isCompact.bddAbove_image hratio
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro transverse value
  by_cases htransverse : transverse ∈ form.padicSquareBranchTransverseSupport prime point hpoint weight
  · rw [Set.indicator_of_mem htransverse]
    unfold padicSquareBranchValueKernel
    by_cases htarget : (value - form.orthogonalRestriction point transverse) / form point ∈
        Rat.padicUnitSquareScalarTarget prime
    · rw [Set.indicator_of_mem (show (transverse, value) ∈ _ from htarget)]
      dsimp only
      let scalar := Rat.padicUnitSquareTargetSupportedInverse prime
        ((value - form.orthogonalRestriction point transverse) / form point)
      have hcoordinates : coordinates (scalar • point + transverse) = (transverse, scalar) := by
        rw [← form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply point hpoint (transverse, scalar)]
        exact (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm_apply_apply _
      rw [ENNReal.coe_nnreal_eq (‖2 * form point * scalar‖₊)]
      change ENNReal.ofReal (weight (scalar • point + transverse)) /
        ENNReal.ofReal ‖2 * form point * scalar‖ ≤ _
      by_cases hzero : weight (scalar • point + transverse) = 0
      · simp only [hzero, ENNReal.ofReal_zero, ENNReal.zero_div, zero_le]
      · have hsupport := subset_tsupport weight hzero
        have hpositive : 0 < ‖2 * form point * scalar‖ := by
          have hpos : 0 < ‖2 * form point * (coordinates (scalar • point + transverse)).2‖ :=
            hlower.trans_le (hlower_bound _ hsupport)
          simpa only [hcoordinates] using hpos
        rw [← ENNReal.ofReal_div_of_pos hpositive]
        apply ENNReal.ofReal_le_ofReal
        have hle := hbound (mem_image_of_mem
          (fun vector ↦ weight vector / ‖2 * form point * (coordinates vector).2‖) hsupport)
        exact le_trans (by simpa only [hcoordinates] using hle) (le_max_left bound 0)
    · rw [Set.indicator_of_notMem (show (transverse, value) ∉ _ from htarget)]
      exact zero_le
  · rw [form.padicSquareBranchValueKernel_eq_zero_of_not_mem_transverseSupport prime
      point hpoint weight transverse value htransverse]
    exact zero_le

omit [SecondCountableTopology space] in
theorem padicSquareBranchValueDensity_lt_top_of_compactSupport
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    [IsFiniteMeasureOnCompacts transverseHaar]
    (weight : space → ℝ) (hweight : Continuous weight) (hcompact : HasCompactSupport weight)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) (value : ℚ_[prime]) :
    form.padicSquareBranchValueDensity prime point transverseHaar (fun vector ↦ ENNReal.ofReal (weight vector))
      value < ∞ := by
  obtain ⟨bound, _, hbound⟩ := form.exists_padicSquareBranchValueKernel_compact_majorant prime
    point hpoint weight hweight hcompact hbranch
  have hcompact_transverse := form.isCompact_padicSquareBranchTransverseSupport prime point hpoint weight hcompact
  calc
    _ ≤ ∫⁻ transverse, (form.padicSquareBranchTransverseSupport prime point hpoint weight).indicator
        (fun _ ↦ ENNReal.ofReal bound) transverse ∂transverseHaar :=
      lintegral_mono (fun transverse ↦ hbound transverse value)
    _ = ENNReal.ofReal bound * transverseHaar (form.padicSquareBranchTransverseSupport prime point hpoint weight) :=
      lintegral_indicator_const hcompact_transverse.measurableSet _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcompact_transverse.measure_lt_top

end QuadraticMap
