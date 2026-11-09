import SMSFormula.QuadraticPadicSquareBranchDomination
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchContinuityMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchContinuityBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space]

def padicSquareBranchForwardSupport (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (weight : space → ℝ) :
    Set (form.anisotropicOrthogonal point × ℚ_[prime]) :=
  (fun vector ↦
    let coordinates := (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector
    (coordinates.1, form.orthogonalRestriction point coordinates.1 + form point * coordinates.2 ^ 2)) ''
      tsupport weight

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem isCompact_padicSquareBranchForwardSupport (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (weight : space → ℝ)
    (hcompact : HasCompactSupport weight) :
    IsCompact (form.padicSquareBranchForwardSupport prime point hpoint weight) := by
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  have hcoordinates := (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm.continuous
  exact hcompact.isCompact.image (hcoordinates.fst.prodMk
    ((hquadratic.comp hcoordinates.fst).add (continuous_const.mul (hcoordinates.snd.pow 2))))

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchForwardSupport_subset_target (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (weight : space → ℝ)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) :
    form.padicSquareBranchForwardSupport prime point hpoint weight ⊆
      (fun pair : form.anisotropicOrthogonal point × ℚ_[prime] ↦
        (pair.2 - form.orthogonalRestriction point pair.1) / form point) ⁻¹'
          Rat.padicUnitSquareScalarTarget prime := by
  rintro pair ⟨vector, hvector, rfl⟩
  dsimp only [mem_preimage]
  obtain ⟨unit, hunit, heq⟩ := hbranch vector hvector
  refine ⟨Rat.unitSquareIdentityChart ℚ_[prime] unit, (Rat.unitSquareIdentityChart ℚ_[prime]).map_source hunit, ?_⟩
  simp only [Rat.unitSquareIdentityChart_apply, Units.val_pow_eq_pow_val]
  rw [heq]
  field_simp
  ring

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchValueKernel_eq_zero_of_not_mem_forwardSupport
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (weight : space → ℝ) (pair : form.anisotropicOrthogonal point × ℚ_[prime])
    (hpair : pair ∉ form.padicSquareBranchForwardSupport prime point hpoint weight) :
    form.padicSquareBranchValueKernel prime point (fun vector ↦ ENNReal.ofReal (weight vector)) pair = 0 := by
  classical
  unfold padicSquareBranchValueKernel
  by_cases htarget : (pair.2 - form.orthogonalRestriction point pair.1) / form point ∈
      Rat.padicUnitSquareScalarTarget prime
  · rw [Set.indicator_of_mem (show pair ∈ _ from htarget)]
    dsimp only
    rw [Rat.padicUnitSquareTargetSupportedInverse_eq prime htarget]
    let scalar := Rat.padicUnitSquareScalarInverse prime
      ((pair.2 - form.orthogonalRestriction point pair.1) / form point)
    have hcoordinates : (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
        (scalar • point + pair.1) = (pair.1, scalar) := by
      rw [← form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply point hpoint (pair.1, scalar)]
      exact (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm_apply_apply _
    have hvalue : form.orthogonalRestriction point pair.1 + form point * scalar ^ 2 = pair.2 :=
      Rat.padicUnitSquareScalarInverse_affine_target prime _ _ hpoint
        ((Rat.mem_padicUnitSquareScalarAffineTarget_iff prime _ _ hpoint _).mpr htarget)
    have hzero : weight (scalar • point + pair.1) = 0 := by
      by_contra hnonzero
      apply hpair
      refine ⟨scalar • point + pair.1, subset_tsupport weight hnonzero, ?_⟩
      dsimp only
      rw [hcoordinates]
      exact Prod.ext rfl hvalue
    change ENNReal.ofReal (weight (scalar • point + pair.1)) / _ = 0
    rw [hzero, ENNReal.ofReal_zero, ENNReal.zero_div]
  · exact Set.indicator_of_notMem (show pair ∉ _ from htarget) _

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem continuous_padicSquareBranchValueKernel_of_compactSupport
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (weight : space → ℝ) (hweight : Continuous weight) (hcompact : HasCompactSupport weight)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) :
    Continuous (form.padicSquareBranchValueKernel prime point (fun vector ↦ ENNReal.ofReal (weight vector))) := by
  classical
  let parameter := fun pair : form.anisotropicOrthogonal point × ℚ_[prime] ↦
    (pair.2 - form.orthogonalRestriction point pair.1) / form point
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  have hparameter : Continuous parameter := (continuous_snd.sub (hquadratic.comp continuous_fst)).div_const _
  have hopen : IsOpen (parameter ⁻¹' Rat.padicUnitSquareScalarTarget prime) :=
    (Rat.isOpen_padicUnitSquareScalarTarget prime).preimage hparameter
  apply continuous_iff_continuousAt.mpr
  intro pair
  by_cases htarget : parameter pair ∈ Rat.padicUnitSquareScalarTarget prime
  · have hinverse : ContinuousAt (fun target ↦ Rat.padicUnitSquareScalarInverse prime (parameter target)) pair :=
      ((Rat.continuousOn_padicUnitSquareScalarInverse prime (parameter pair) htarget).continuousAt
        ((Rat.isOpen_padicUnitSquareScalarTarget prime).mem_nhds htarget)).comp hparameter.continuousAt
    have hvector : ContinuousAt (fun target : form.anisotropicOrthogonal point × ℚ_[prime] ↦
        Rat.padicUnitSquareScalarInverse prime (parameter target) • point + target.1) pair :=
      (hinverse.smul continuousAt_const).add (continuous_subtype_val.comp continuous_fst).continuousAt
    have hpositive (target : form.anisotropicOrthogonal point × ℚ_[prime])
        (hmem : parameter target ∈ Rat.padicUnitSquareScalarTarget prime) :
        0 < ‖2 * form point * Rat.padicUnitSquareScalarInverse prime (parameter target)‖ :=
      norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hpoint)
        (Rat.padicUnitSquareScalarSource_ne_zero prime (Rat.padicUnitSquareScalarInverse_mem_and_sq prime hmem).1))
    have hcontinuous : ContinuousAt (fun target : form.anisotropicOrthogonal point × ℚ_[prime] ↦
        ENNReal.ofReal (weight (Rat.padicUnitSquareScalarInverse prime (parameter target) • point + target.1) /
          ‖2 * form point * Rat.padicUnitSquareScalarInverse prime (parameter target)‖)) pair :=
      ENNReal.continuous_ofReal.continuousAt.comp ((hweight.continuousAt.comp hvector).div
        (continuousAt_const.mul hinverse).norm (ne_of_gt (hpositive pair htarget)))
    apply hcontinuous.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds htarget] with target hmem
    unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_mem hmem]
    dsimp only
    rw [Rat.padicUnitSquareTargetSupportedInverse_eq prime hmem]
    simpa only [← coe_nnnorm, ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_div_of_pos (hpositive target hmem)).symm
  · have hnot : pair ∉ form.padicSquareBranchForwardSupport prime point hpoint weight :=
      fun hmem ↦ htarget (form.padicSquareBranchForwardSupport_subset_target prime point hpoint weight hbranch hmem)
    have hclosed := (form.isCompact_padicSquareBranchForwardSupport prime point hpoint weight hcompact).isClosed
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hclosed.isOpen_compl.mem_nhds hnot] with target hmem
    exact form.padicSquareBranchValueKernel_eq_zero_of_not_mem_forwardSupport prime point hpoint weight target hmem

omit [SecondCountableTopology space] in
theorem continuous_padicSquareBranchValueDensity_of_compactSupport
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    [IsFiniteMeasureOnCompacts transverseHaar]
    (weight : space → ℝ) (hweight : Continuous weight) (hcompact : HasCompactSupport weight)
    (hbranch : ∀ vector ∈ tsupport weight,
      ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector).2 ∈
        Rat.padicUnitSquareScalarSource prime) :
    Continuous (form.padicSquareBranchValueDensity prime point transverseHaar
      (fun vector ↦ ENNReal.ofReal (weight vector))) := by
  obtain ⟨bound, _, hbound⟩ := form.exists_padicSquareBranchValueKernel_compact_majorant prime
    point hpoint weight hweight hcompact hbranch
  have hcarrier := form.isCompact_padicSquareBranchTransverseSupport prime point hpoint weight hcompact
  have hkernel := form.continuous_padicSquareBranchValueKernel_of_compactSupport prime
    point hpoint weight hweight hcompact hbranch
  apply continuous_iff_continuousAt.mpr
  intro value
  apply tendsto_lintegral_filter_of_dominated_convergence
    ((form.padicSquareBranchTransverseSupport prime point hpoint weight).indicator (fun _ ↦ ENNReal.ofReal bound))
  · exact Filter.Eventually.of_forall (fun target ↦
      (hkernel.comp (continuous_id.prodMk continuous_const)).measurable)
  · exact Filter.Eventually.of_forall (fun target ↦
      Filter.Eventually.of_forall (fun transverse ↦ hbound transverse target))
  · rw [lintegral_indicator_const hcarrier.measurableSet]
    exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcarrier.measure_lt_top)
  · exact Filter.Eventually.of_forall (fun transverse ↦
      (hkernel.comp (continuous_const.prodMk continuous_id)).continuousAt)

end QuadraticMap
