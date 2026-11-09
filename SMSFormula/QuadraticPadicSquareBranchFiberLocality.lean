import SMSFormula.QuadraticPadicSquareBranchKernel

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]

theorem padicSquareBranch_inverse_vector_value (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime])
    (htarget : (value - form.orthogonalRestriction point transverse) / form point ∈
      Rat.padicUnitSquareScalarTarget prime) :
    form (Rat.padicUnitSquareTargetSupportedInverse prime
      ((value - form.orthogonalRestriction point transverse) / form point) • point + transverse) = value := by
  rw [Rat.padicUnitSquareTargetSupportedInverse_eq prime htarget]
  let scalar := Rat.padicUnitSquareScalarInverse prime
    ((value - form.orthogonalRestriction point transverse) / form point)
  have hquadratic : form (scalar • point + transverse) =
      form.orthogonalRestriction point transverse + scalar ^ 2 * form point := by
    simpa only [anisotropicOrthogonalDecompositionIsometryEquiv_apply, anisotropicOrthogonalSum,
      prod_apply, anisotropicScalarLine_apply_eq_sq_mul] using
      (form.anisotropicOrthogonalDecompositionIsometryEquiv point hpoint).map_app (transverse, scalar)
  rw [hquadratic, mul_comm (scalar ^ 2)]
  exact Rat.padicUnitSquareScalarInverse_affine_target prime _ _ hpoint
    ((Rat.mem_padicUnitSquareScalarAffineTarget_iff prime _ _ hpoint _).mpr htarget)

theorem padicSquareBranchValueKernel_eq_of_eqOn_fiber (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (first second : space → ℝ≥0∞)
    (value : ℚ_[prime]) (hweights : Set.EqOn first second {vector | form vector = value})
    (transverse : form.anisotropicOrthogonal point) :
    form.padicSquareBranchValueKernel prime point first (transverse, value) =
      form.padicSquareBranchValueKernel prime point second (transverse, value) := by
  classical
  by_cases htarget : (value - form.orthogonalRestriction point transverse) / form point ∈
      Rat.padicUnitSquareScalarTarget prime
  · unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_mem (show (transverse, value) ∈ _ from htarget),
      Set.indicator_of_mem (show (transverse, value) ∈ _ from htarget)]
    dsimp only
    rw [hweights (form.padicSquareBranch_inverse_vector_value prime point hpoint transverse value htarget)]
  · unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_notMem (show (transverse, value) ∉ _ from htarget),
      Set.indicator_of_notMem (show (transverse, value) ∉ _ from htarget)]

variable [MeasurableSpace space]

theorem padicSquareBranchValueDensity_eq_of_eqOn_fiber (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point))
    (first second : space → ℝ≥0∞) (value : ℚ_[prime])
    (hweights : Set.EqOn first second {vector | form vector = value}) :
    form.padicSquareBranchValueDensity prime point transverseMeasure first value =
      form.padicSquareBranchValueDensity prime point transverseMeasure second value :=
  lintegral_congr (form.padicSquareBranchValueKernel_eq_of_eqOn_fiber prime point hpoint first second value hweights)

end QuadraticMap
