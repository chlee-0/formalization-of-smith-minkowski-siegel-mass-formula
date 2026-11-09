import SMSFormula.RationalAdeleStandardOverlapTest
import SMSFormula.RationalAdeleTransposePairing

/-!
# The coordinate character moves a matrix to its transpose

The one lemma left in the overlap argument is the transpose symmetry of the overlap.  Its
algebraic half is that the fixed coordinate character sees only the coordinate dot product, so
the already formalized pairing identity `<N x, y> = <x, N^T y>` transfers directly to it.

Negative scope: a character identity only.  No integral is computed, no Fubini is applied, and the
transpose symmetry of the overlap is not proved here.
-/

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The coordinate character is the scalar character of the coordinate sum. -/
theorem rationalAdeleCoordinateFourierChar_eq_sum (d : ℕ) (u : Fin d → RationalAdele) :
    rationalAdeleCoordinateFourierChar d u = rationalAdeleFourierChar (∑ i, u i) := by
  rw [rationalAdeleCoordinateFourierChar_apply]
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
        ← AddChar.map_add_eq_mul]

/-- Hence the character of the coordinatewise product is the character of the dot product. -/
theorem rationalAdeleCoordinateFourierChar_mul_eq_dotProduct (d : ℕ)
    (v w : Fin d → RationalAdele) :
    rationalAdeleCoordinateFourierChar d (v * w) =
      rationalAdeleFourierChar (dotProduct v w) := by
  rw [rationalAdeleCoordinateFourierChar_eq_sum]
  rfl

/-- The character transpose identity: the fixed coordinate character carries a full-adelic matrix
to its transpose, by the already formalized pairing identity. -/
theorem rationalAdeleCoordinateFourierChar_mulVec_transpose
    (N : Matrix (Fin n) (Fin n) RationalAdele) (v x : Fin n → RationalAdele) :
    rationalAdeleCoordinateFourierChar n (-(v * N.mulVec x)) =
      rationalAdeleCoordinateFourierChar n (-(x * N.transpose.mulVec v)) := by
  have hneg : ∀ u w : Fin n → RationalAdele,
      rationalAdeleCoordinateFourierChar n (-(u * w)) =
        rationalAdeleFourierChar (-(dotProduct u w)) := by
    intro u w
    rw [rationalAdeleCoordinateFourierChar_eq_sum]
    congr 1
    simp only [Pi.neg_apply, Pi.mul_apply, Finset.sum_neg_distrib]
    rfl
  rw [hneg, hneg]
  congr 2
  calc dotProduct v (N.mulVec x) = dotProduct (N.mulVec x) v := dotProduct_comm _ _
    _ = dotProduct x (N.transpose.mulVec v) := dotProduct_mulVec_transpose N x v

/-! ## The test as a nonnegative real function -/

/-- The scalar test, as a nonnegative real. -/
def realScalarGaussianIntegralTest (z : RationalAdele) : ℝ :=
  Real.exp (-Real.pi * (rationalInfiniteAdeleContinuousAddEquivReal z.1) ^ 2) *
    Set.indicator (integralFiniteAdeleSubring : Set RationalFiniteAdele) (fun _ ↦ (1 : ℝ)) z.2

theorem realScalarGaussianIntegralTest_nonneg (z : RationalAdele) :
    0 ≤ realScalarGaussianIntegralTest z := by
  refine mul_nonneg (Real.exp_nonneg _) ?_
  by_cases h : z.2 ∈ (integralFiniteAdeleSubring : Set RationalFiniteAdele)
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]

theorem rationalAdeleGaussianIntegralTest_one_eq_ofReal (z : RationalAdele) :
    rationalAdeleGaussianIntegralTest 1 z = ((realScalarGaussianIntegralTest z : ℝ) : ℂ) := by
  rw [rationalAdeleGaussianIntegralTest, realScalarGaussianIntegralTest,
    rationalInfiniteAdeleGaussian, rationalFiniteAdeleIntegralIndicator]
  push_cast
  congr 1
  · ring_nf
  · by_cases h : z.2 ∈ (integralFiniteAdeleSubring : Set RationalFiniteAdele)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      norm_num
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      norm_num

/-- The coordinate test, as a nonnegative real. -/
def realCoordinateGaussianIntegralTest (d : ℕ) (x : Fin d → RationalAdele) : ℝ :=
  ∏ i, realScalarGaussianIntegralTest (x i)

theorem realCoordinateGaussianIntegralTest_nonneg (d : ℕ) (x : Fin d → RationalAdele) :
    0 ≤ realCoordinateGaussianIntegralTest d x :=
  Finset.prod_nonneg fun i _ ↦ realScalarGaussianIntegralTest_nonneg (x i)

theorem rationalAdeleCoordinateGaussianIntegralTest_one_eq_ofReal (d : ℕ)
    (x : Fin d → RationalAdele) :
    rationalAdeleCoordinateGaussianIntegralTest d 1 x =
      ((realCoordinateGaussianIntegralTest d x : ℝ) : ℂ) := by
  rw [rationalAdeleCoordinateGaussianIntegralTest, realCoordinateGaussianIntegralTest,
    Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ ↦
    rationalAdeleGaussianIntegralTest_one_eq_ofReal (x i)

theorem norm_rationalAdeleCoordinateGaussianIntegralTest_one (d : ℕ)
    (x : Fin d → RationalAdele) :
    ‖rationalAdeleCoordinateGaussianIntegralTest d 1 x‖ =
      realCoordinateGaussianIntegralTest d x := by
  rw [rationalAdeleCoordinateGaussianIntegralTest_one_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (realCoordinateGaussianIntegralTest_nonneg d x)]

@[simp]
theorem standardOverlapTest_eq_ofReal (d : ℕ) (x : Fin d → RationalAdele) :
    standardOverlapTest d x = ENNReal.ofReal (realCoordinateGaussianIntegralTest d x) := by
  rw [standardOverlapTest, norm_rationalAdeleCoordinateGaussianIntegralTest_one]

/-! ## The complex overlap and its transpose symmetry -/

/-- The complex overlap of the standard test. -/
def complexAdelicOverlap (d : ℕ) (N : Matrix (Fin d) (Fin d) RationalAdele) : ℂ :=
  ∫ x, rationalAdeleCoordinateGaussianIntegralTest d 1 x *
      rationalAdeleCoordinateGaussianIntegralTest d 1 (N.mulVec x)
    ∂(rationalAdeleCoordinateAddHaarMeasure d)

private theorem measurable_overlapKernel (d : ℕ) (N : Matrix (Fin d) (Fin d) RationalAdele) :
    Measurable (fun p : (Fin d → RationalAdele) × (Fin d → RationalAdele) ↦
      rationalAdeleCoordinateGaussianIntegralTest d 1 p.1 *
        ((rationalAdeleCoordinateFourierChar d (-(p.2 * N.mulVec p.1)) : ℂ) *
          rationalAdeleCoordinateGaussianIntegralTest d 1 p.2)) := by
  have hchar : Measurable (fun p : (Fin d → RationalAdele) × (Fin d → RationalAdele) ↦
      ((rationalAdeleCoordinateFourierChar d (-(p.2 * N.mulVec p.1)) : ℂ))) := by
    refine (continuous_subtype_val.comp
      ((continuous_rationalAdeleCoordinateFourierChar d).comp ?_)).measurable
    exact continuous_neg.comp
      (continuous_snd.mul ((continuous_fullAdelicMatrixMulVec N).comp continuous_fst))
  exact ((measurable_rationalAdeleCoordinateGaussianIntegralTest d 1).comp measurable_fst).mul
    (hchar.mul
      ((measurable_rationalAdeleCoordinateGaussianIntegralTest d 1).comp measurable_snd))

private theorem integrable_overlapKernel (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    Integrable (fun p : (Fin d → RationalAdele) × (Fin d → RationalAdele) ↦
      rationalAdeleCoordinateGaussianIntegralTest d 1 p.1 *
        ((rationalAdeleCoordinateFourierChar d (-(p.2 * N.mulVec p.1)) : ℂ) *
          rationalAdeleCoordinateGaussianIntegralTest d 1 p.2))
      ((rationalAdeleCoordinateAddHaarMeasure d).prod
        (rationalAdeleCoordinateAddHaarMeasure d)) := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by simp
  have hphi := integrable_rationalAdeleCoordinateGaussianIntegralTest hb d
  have hmaj : Integrable (fun p : (Fin d → RationalAdele) × (Fin d → RationalAdele) ↦
      ‖rationalAdeleCoordinateGaussianIntegralTest d 1 p.1‖ *
        ‖rationalAdeleCoordinateGaussianIntegralTest d 1 p.2‖)
      ((rationalAdeleCoordinateAddHaarMeasure d).prod
        (rationalAdeleCoordinateAddHaarMeasure d)) :=
    hphi.norm.mul_prod hphi.norm
  refine Integrable.mono' hmaj (measurable_overlapKernel d N).aestronglyMeasurable ?_
  filter_upwards with p
  rw [norm_mul, norm_mul]
  have hone : ‖((rationalAdeleCoordinateFourierChar d (-(p.2 * N.mulVec p.1)) : ℂ))‖ = 1 := by
    simp
  rw [hone, one_mul]

/-- The transpose symmetry of the complex overlap, by one absolutely integrable double integral
against the fixed coordinate character. -/
theorem complexAdelicOverlap_transpose (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    complexAdelicOverlap d N = complexAdelicOverlap d N.transpose := by
  set mu := rationalAdeleCoordinateAddHaarMeasure d with hmu
  set phi := rationalAdeleCoordinateGaussianIntegralTest d 1 with hphi
  have heigen := rationalAdeleCoordinate_fourierIntegral_gaussianIntegralTest_one d
  have hexp : ∀ z : Fin d → RationalAdele,
      phi z = ∫ y, ((rationalAdeleCoordinateFourierChar d (-(y * z)) : ℂ)) * phi y ∂mu := by
    intro z
    have := congrFun heigen z
    rw [Fourier.fourierIntegral_def] at this
    rw [hphi, ← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ rfl)
  calc complexAdelicOverlap d N
      = ∫ x, ∫ y, phi x *
          (((rationalAdeleCoordinateFourierChar d (-(y * N.mulVec x)) : ℂ)) * phi y) ∂mu ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        show phi x * phi (N.mulVec x) =
          ∫ y, phi x *
            (((rationalAdeleCoordinateFourierChar d (-(y * N.mulVec x)) : ℂ)) * phi y) ∂mu
        rw [integral_const_mul]
        exact congrArg (fun t : ℂ ↦ phi x * t) (hexp (N.mulVec x))
    _ = ∫ y, ∫ x, phi x *
          (((rationalAdeleCoordinateFourierChar d (-(y * N.mulVec x)) : ℂ)) * phi y) ∂mu ∂mu :=
        integral_integral_swap (integrable_overlapKernel d N)
    _ = ∫ y, phi y * phi (N.transpose.mulVec y) ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
        show (∫ x, phi x *
            (((rationalAdeleCoordinateFourierChar d (-(y * N.mulVec x)) : ℂ)) * phi y) ∂mu)
          = phi y * phi (N.transpose.mulVec y)
        rw [hexp (N.transpose.mulVec y), ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        show phi x *
            (((rationalAdeleCoordinateFourierChar d (-(y * N.mulVec x)) : ℂ)) * phi y) =
          phi y *
            (((rationalAdeleCoordinateFourierChar d
              (-(x * N.transpose.mulVec y)) : ℂ)) * phi x)
        rw [rationalAdeleCoordinateFourierChar_mulVec_transpose N y x]
        ring
    _ = complexAdelicOverlap d N.transpose := rfl

/-! ## From the complex overlap to the `ENNReal` overlap -/

theorem realCoordinateGaussianIntegralTest_le_one (d : ℕ) (x : Fin d → RationalAdele) :
    realCoordinateGaussianIntegralTest d x ≤ 1 := by
  have h := standardOverlapTest_le_one d x
  rw [standardOverlapTest_eq_ofReal, ← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 h

theorem measurable_realCoordinateGaussianIntegralTest (d : ℕ) :
    Measurable (realCoordinateGaussianIntegralTest d) := by
  have h := (measurable_rationalAdeleCoordinateGaussianIntegralTest d 1).norm
  simpa only [norm_rationalAdeleCoordinateGaussianIntegralTest_one] using h

theorem integrable_realCoordinateGaussianIntegralTest (d : ℕ) :
    Integrable (realCoordinateGaussianIntegralTest d)
      (rationalAdeleCoordinateAddHaarMeasure d) := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by simp
  have hphi := integrable_rationalAdeleCoordinateGaussianIntegralTest hb d
  refine ⟨(measurable_realCoordinateGaussianIntegralTest d).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (le_of_eq ?_) hphi.hasFiniteIntegral
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
    abs_of_nonneg (realCoordinateGaussianIntegralTest_nonneg d x),
    norm_rationalAdeleCoordinateGaussianIntegralTest_one]

theorem integrable_realCoordinateOverlapIntegrand (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    Integrable (fun x ↦ realCoordinateGaussianIntegralTest d x *
        realCoordinateGaussianIntegralTest d (N.mulVec x))
      (rationalAdeleCoordinateAddHaarMeasure d) := by
  have hmeas : Measurable (fun x ↦ realCoordinateGaussianIntegralTest d x *
      realCoordinateGaussianIntegralTest d (N.mulVec x)) :=
    (measurable_realCoordinateGaussianIntegralTest d).mul
      ((measurable_realCoordinateGaussianIntegralTest d).comp
        (continuous_fullAdelicMatrixMulVec N).measurable)
  refine Integrable.mono' (integrable_realCoordinateGaussianIntegralTest d)
    hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (realCoordinateGaussianIntegralTest_nonneg d x)
    (realCoordinateGaussianIntegralTest_nonneg d _))]
  calc realCoordinateGaussianIntegralTest d x *
        realCoordinateGaussianIntegralTest d (N.mulVec x)
      ≤ realCoordinateGaussianIntegralTest d x * 1 := by
        exact mul_le_mul_of_nonneg_left (realCoordinateGaussianIntegralTest_le_one d _)
          (realCoordinateGaussianIntegralTest_nonneg d x)
    _ = realCoordinateGaussianIntegralTest d x := mul_one _

theorem adelicOverlap_standardOverlapTest_eq_ofReal (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    adelicOverlap (standardOverlapTest d) N =
      ENNReal.ofReal (∫ x, realCoordinateGaussianIntegralTest d x *
        realCoordinateGaussianIntegralTest d (N.mulVec x)
        ∂(rationalAdeleCoordinateAddHaarMeasure d)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_realCoordinateOverlapIntegrand d N)
    (Filter.Eventually.of_forall fun x ↦ mul_nonneg
      (realCoordinateGaussianIntegralTest_nonneg d x)
      (realCoordinateGaussianIntegralTest_nonneg d _))]
  refine lintegral_congr fun x ↦ ?_
  rw [standardOverlapTest_eq_ofReal, standardOverlapTest_eq_ofReal,
    ← ENNReal.ofReal_mul (realCoordinateGaussianIntegralTest_nonneg d x)]

theorem complexAdelicOverlap_eq_ofReal (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    complexAdelicOverlap d N =
      ((∫ x, realCoordinateGaussianIntegralTest d x *
        realCoordinateGaussianIntegralTest d (N.mulVec x)
        ∂(rationalAdeleCoordinateAddHaarMeasure d) : ℝ) : ℂ) := by
  rw [complexAdelicOverlap]
  have heq : (fun x ↦ rationalAdeleCoordinateGaussianIntegralTest d 1 x *
      rationalAdeleCoordinateGaussianIntegralTest d 1 (N.mulVec x)) =
      fun x ↦ ((realCoordinateGaussianIntegralTest d x *
        realCoordinateGaussianIntegralTest d (N.mulVec x) : ℝ) : ℂ) := by
    funext x
    rw [rationalAdeleCoordinateGaussianIntegralTest_one_eq_ofReal,
      rationalAdeleCoordinateGaussianIntegralTest_one_eq_ofReal, ← Complex.ofReal_mul]
  rw [heq]
  exact Complex.ofRealCLM.integral_comp_comm (integrable_realCoordinateOverlapIntegrand d N)

/-- The transpose symmetry of the overlap -- the last lemma of the overlap argument. -/
theorem adelicOverlap_standardOverlapTest_transpose (d : ℕ)
    (N : Matrix (Fin d) (Fin d) RationalAdele) :
    adelicOverlap (standardOverlapTest d) N =
      adelicOverlap (standardOverlapTest d) N.transpose := by
  have h := complexAdelicOverlap_transpose d N
  rw [complexAdelicOverlap_eq_ofReal, complexAdelicOverlap_eq_ofReal] at h
  rw [adelicOverlap_standardOverlapTest_eq_ofReal,
    adelicOverlap_standardOverlapTest_eq_ofReal]
  exact congrArg ENNReal.ofReal (Complex.ofReal_inj.1 h)

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

open PositiveDefiniteIntegralLattice

/-- Haar invariance: every full-adelic orthogonal matrix preserves the fixed coordinate Haar
measure.  No hypothesis remains. -/
theorem fullAdelicOrthogonal_measurePreserving_coordinateHaar
    (V : RationalQuadraticSpaceMatrix n) (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) :=
  V.fullAdelicOrthogonal_measurePreserving_of_standardOverlap_transpose
    (adelicOverlap_standardOverlapTest_transpose n) g

end RationalQuadraticSpaceMatrix

end
