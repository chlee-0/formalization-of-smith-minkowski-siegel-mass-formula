import SMSFormula.RationalAdeleCoordinateGaussianEigen
import SMSFormula.RationalAdeleHaarOverlap

/-!
# The standard overlap test: measurable, bounded by one, integrable, positive near the origin

The overlap argument runs on `phi = e^{-pi|x_inf|^2} 1_{Zhat^n}`, which is the existing
coordinate Gaussian--indicator test at width one -- known to be a Fourier eigenfunction with
`kappa = 1`.  This file supplies the three elementary properties the overlap layer asks for, so
that `overlap_ne_top` and `overlap_pos` instantiate at it unconditionally.

Negative scope: no Fourier transform is used here, and the transpose symmetry of the overlap is
proved separately (`adelicOverlap_standardOverlapTest_transpose`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

/-! ## Measurability -/

theorem measurable_rationalInfiniteAdeleGaussian (b : ℂ) :
    Measurable (rationalInfiniteAdeleGaussian b) := by
  unfold rationalInfiniteAdeleGaussian
  refine Complex.measurable_exp.comp ?_
  exact ((Complex.continuous_ofReal.comp
    rationalInfiniteAdeleContinuousAddEquivReal.continuous).pow 2).measurable.const_mul _

theorem measurable_rationalFiniteAdeleIntegralIndicator :
    Measurable rationalFiniteAdeleIntegralIndicator := by
  unfold rationalFiniteAdeleIntegralIndicator
  exact measurable_const.indicator isOpen_integralFiniteAdeleSubring.measurableSet

theorem measurable_rationalAdeleGaussianIntegralTest (b : ℂ) :
    Measurable (rationalAdeleGaussianIntegralTest b) := by
  unfold rationalAdeleGaussianIntegralTest
  exact ((measurable_rationalInfiniteAdeleGaussian b).comp measurable_fst).mul
    (measurable_rationalFiniteAdeleIntegralIndicator.comp measurable_snd)

theorem measurable_rationalAdeleCoordinateGaussianIntegralTest (d : ℕ) (b : ℂ) :
    Measurable (rationalAdeleCoordinateGaussianIntegralTest d b) := by
  unfold rationalAdeleCoordinateGaussianIntegralTest
  exact Finset.measurable_prod _ fun i _ ↦
    (measurable_rationalAdeleGaussianIntegralTest b).comp (measurable_pi_apply i)

/-! ## The nonnegative overlap test -/

/-- The nonnegative modulus of the existing coordinate Gaussian--indicator test at width one. -/
def standardOverlapTest (d : ℕ) (x : Fin d → RationalAdele) : ℝ≥0∞ :=
  ENNReal.ofReal ‖rationalAdeleCoordinateGaussianIntegralTest d 1 x‖

theorem measurable_standardOverlapTest (d : ℕ) : Measurable (standardOverlapTest d) :=
  (measurable_rationalAdeleCoordinateGaussianIntegralTest d 1).norm.ennreal_ofReal

/-- Each scalar factor has modulus at most one. -/
theorem norm_rationalAdeleGaussianIntegralTest_one_le (z : RationalAdele) :
    ‖rationalAdeleGaussianIntegralTest 1 z‖ ≤ 1 := by
  rw [rationalAdeleGaussianIntegralTest, norm_mul]
  have hg : ‖rationalInfiniteAdeleGaussian 1 z.1‖ ≤ 1 := by
    rw [rationalInfiniteAdeleGaussian, Complex.norm_exp]
    refine Real.exp_le_one_iff.2 ?_
    have : (-(Real.pi : ℂ) * 1 *
        ((rationalInfiniteAdeleContinuousAddEquivReal z.1 : ℝ) : ℂ) ^ 2).re =
        -(Real.pi) * (rationalInfiniteAdeleContinuousAddEquivReal z.1 : ℝ) ^ 2 := by
      simp [pow_two]
    rw [this]
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    nlinarith [sq_nonneg ((rationalInfiniteAdeleContinuousAddEquivReal z.1 : ℝ))]
  have hi : ‖rationalFiniteAdeleIntegralIndicator z.2‖ ≤ 1 := by
    rw [rationalFiniteAdeleIntegralIndicator]
    by_cases h : z.2 ∈ (integralFiniteAdeleSubring : Set RationalFiniteAdele)
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  calc ‖rationalInfiniteAdeleGaussian 1 z.1‖ * ‖rationalFiniteAdeleIntegralIndicator z.2‖
      ≤ 1 * 1 := by
        exact mul_le_mul hg hi (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The bound: the standard overlap test is at most one. -/
theorem standardOverlapTest_le_one (d : ℕ) (x : Fin d → RationalAdele) :
    standardOverlapTest d x ≤ 1 := by
  rw [standardOverlapTest, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rationalAdeleCoordinateGaussianIntegralTest, norm_prod]
  exact Finset.prod_le_one (fun i _ ↦ norm_nonneg _)
    (fun i _ ↦ norm_rationalAdeleGaussianIntegralTest_one_le (x i))

/-- The integrability: the standard overlap test has finite integral. -/
theorem lintegral_standardOverlapTest_ne_top (d : ℕ) :
    (∫⁻ x, standardOverlapTest d x ∂(rationalAdeleCoordinateAddHaarMeasure d)) ≠ ⊤ := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by simp
  have hint := (integrable_rationalAdeleCoordinateGaussianIntegralTest hb d).hasFiniteIntegral
  refine ne_of_lt ?_
  refine lt_of_le_of_lt (le_of_eq ?_) hint
  refine lintegral_congr fun x ↦ ?_
  rw [standardOverlapTest, ofReal_norm_eq_enorm]

/-! ## Positivity near the origin -/

/-- The open unit box of the scalar adele: real part of absolute value below one, finite part
integral. -/
def unitBoxAdele : Set RationalAdele :=
  {z | |(rationalInfiniteAdeleContinuousAddEquivReal z.1 : ℝ)| < 1} ∩
    {z | z.2 ∈ (integralFiniteAdeleSubring : Set RationalFiniteAdele)}

theorem isOpen_unitBoxAdele : IsOpen unitBoxAdele := by
  refine IsOpen.inter ?_ ?_
  · exact isOpen_lt
      ((continuous_abs).comp
        (rationalInfiniteAdeleContinuousAddEquivReal.continuous.comp continuous_fst))
      continuous_const
  · exact isOpen_integralFiniteAdeleSubring.preimage continuous_snd

theorem zero_mem_unitBoxAdele : (0 : RationalAdele) ∈ unitBoxAdele := by
  constructor
  · show |(rationalInfiniteAdeleContinuousAddEquivReal (0 : RationalAdele).1 : ℝ)| < 1
    have h0 : (0 : RationalAdele).1 = 0 := rfl
    rw [h0, map_zero]
    norm_num
  · show (0 : RationalAdele).2 ∈ (integralFiniteAdeleSubring : Set RationalFiniteAdele)
    exact Subring.zero_mem _

/-- On the unit box the scalar test has modulus at least `exp (-pi)`. -/
theorem exp_neg_pi_le_norm_rationalAdeleGaussianIntegralTest_one {z : RationalAdele}
    (hz : z ∈ unitBoxAdele) :
    Real.exp (-Real.pi) ≤ ‖rationalAdeleGaussianIntegralTest 1 z‖ := by
  obtain ⟨hreal, hfin⟩ := hz
  have hfin' : z.2 ∈ (integralFiniteAdeleSubring : Set RationalFiniteAdele) := hfin
  set t : ℝ := rationalInfiniteAdeleContinuousAddEquivReal z.1 with ht
  have habs : |t| < 1 := hreal
  have hsq : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  rw [rationalAdeleGaussianIntegralTest, norm_mul,
    rationalFiniteAdeleIntegralIndicator, Set.indicator_of_mem hfin']
  rw [rationalInfiniteAdeleGaussian, Complex.norm_exp]
  have hre : (-(Real.pi : ℂ) * 1 * ((t : ℝ) : ℂ) ^ 2).re = -(Real.pi) * t ^ 2 := by
    simp [pow_two]
  rw [hre, norm_one, mul_one]
  refine Real.exp_le_exp.2 ?_
  nlinarith [Real.pi_pos]

/-- The open coordinate unit box. -/
def unitBoxCoordinate (d : ℕ) : Set (Fin d → RationalAdele) :=
  {x | ∀ i, x i ∈ unitBoxAdele}

theorem isOpen_unitBoxCoordinate (d : ℕ) : IsOpen (unitBoxCoordinate d) := by
  rw [unitBoxCoordinate, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_unitBoxAdele.preimage (continuous_apply i)

theorem zero_mem_unitBoxCoordinate (d : ℕ) :
    (0 : Fin d → RationalAdele) ∈ unitBoxCoordinate d := fun _ ↦ zero_mem_unitBoxAdele

/-- The lower bound on the coordinate unit box. -/
theorem le_standardOverlapTest_of_mem_unitBoxCoordinate (d : ℕ)
    {x : Fin d → RationalAdele} (hx : x ∈ unitBoxCoordinate d) :
    ENNReal.ofReal (Real.exp (-Real.pi) ^ d) ≤ standardOverlapTest d x := by
  rw [standardOverlapTest]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rationalAdeleCoordinateGaussianIntegralTest, norm_prod]
  calc Real.exp (-Real.pi) ^ d
      = ∏ _i : Fin d, Real.exp (-Real.pi) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i : Fin d, ‖rationalAdeleGaussianIntegralTest 1 (x i)‖ := by
        refine Finset.prod_le_prod (fun i _ ↦ (Real.exp_pos _).le) ?_
        exact fun i _ ↦ exp_neg_pi_le_norm_rationalAdeleGaussianIntegralTest_one (hx i)

/-! ## The two overlap hypotheses, discharged -/

theorem adelicOverlap_standardOverlapTest_ne_top (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    adelicOverlap (standardOverlapTest d) N ≠ ⊤ :=
  adelicOverlap_ne_top (standardOverlapTest_le_one d) (lintegral_standardOverlapTest_ne_top d) N

theorem adelicOverlap_standardOverlapTest_pos (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    0 < adelicOverlap (standardOverlapTest d) N :=
  adelicOverlap_pos (measurable_standardOverlapTest d)
    (c := ENNReal.ofReal (Real.exp (-Real.pi) ^ d))
    (by
      refine (ENNReal.ofReal_pos.2 ?_).ne'
      positivity)
    (isOpen_unitBoxCoordinate d) (zero_mem_unitBoxCoordinate d)
    (fun x hx ↦ le_standardOverlapTest_of_mem_unitBoxCoordinate d hx) N

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

open PositiveDefiniteIntegralLattice

/-- A full-adelic orthogonal matrix preserves the
fixed coordinate Haar as soon as the standard overlap test has transpose-symmetric overlaps.
Every other hypothesis of the overlap argument is proved. -/
theorem fullAdelicOrthogonal_measurePreserving_of_standardOverlap_transpose
    (V : RationalQuadraticSpaceMatrix n)
    (hsym : ∀ N : Matrix (Fin n) (Fin n) RationalAdele,
      adelicOverlap (standardOverlapTest n) N =
        adelicOverlap (standardOverlapTest n) N.transpose)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) :=
  V.fullAdelicOrthogonal_measurePreserving_of_adelicOverlap_transpose
    (measurable_standardOverlapTest n) hsym
    (fun h ↦ adelicOverlap_standardOverlapTest_pos n h.1)
    (fun h ↦ adelicOverlap_standardOverlapTest_ne_top n h.1) g

end RationalQuadraticSpaceMatrix

end
