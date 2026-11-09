import SMSFormula.RationalAdeleRankOnePolarGaussianLatticeFourierSquare
import SMSFormula.RationalAdeleRealCuspGaussianFactorization
import SMSFormula.RationalAdeleVectorComplexGaussianTheta

noncomputable section

open Matrix MeasureTheory
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {rank : ℕ} (lattice : PositiveDefiniteIntegralLattice rank)

/-- Raw real Fourier transform with the full polar matrix and coordinate Lebesgue Haar. -/
def polarRealRawFourier (weight : (Fin rank → ℝ) → ℂ) (frequency : Fin rank → ℝ) : ℂ :=
  Fourier.fourierIntegral (realCoordinateFourierChar rank) volume weight
    (lattice.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec frequency)

/-- The real raw amplitude is the reciprocal polar determinant scale. -/
def polarRealFourierMass : ℝ := (lattice.polarRealDeterminantScale : ℝ)⁻¹

/-- Operator normalization only; coordinate Lebesgue Haar is not changed. -/
def polarRealNormalizedFourier (weight : (Fin rank → ℝ) → ℂ) (frequency : Fin rank → ℝ) : ℂ :=
  (lattice.polarRealDeterminantScale : ℂ) * lattice.polarRealRawFourier weight frequency

def polarRealNormalizedFourierInverse (weight : (Fin rank → ℝ) → ℂ) (frequency : Fin rank → ℝ) : ℂ :=
  lattice.polarRealNormalizedFourier weight (-frequency)

/-- The raw inverse has the square of the determinant scale, equivalently two inverse masses. -/
def polarRealRawFourierInverse (weight : (Fin rank → ℝ) → ℂ) (frequency : Fin rank → ℝ) : ℂ :=
  (lattice.polarRealDeterminantScale : ℂ) * lattice.polarRealNormalizedFourierInverse weight frequency

def polarRealPhaseOperator (parameter : ℝ) (weight : (Fin rank → ℝ) → ℂ) (vector : Fin rank → ℝ) : ℂ :=
  (Real.fourierChar (parameter * lattice.rationalQuadraticSpaceMatrix.realQuadraticFormValue vector) : ℂ) *
    weight vector

def polarRealHalfRankOperator (parameter : ℝ) (weight : (Fin rank → ℝ) → ℂ) (vector : Fin rank → ℝ) : ℂ :=
  ((‖parameter‖ ^ ((rank : ℝ) / 2) : ℝ) : ℂ) * weight (parameter • vector)

/-- The literal principal-root coefficient already occurring in the Gaussian Fourier formula. -/
def realGaussianFourierCoefficient (dimension : ℕ) (width : ℂ) : ℂ :=
  (1 / width ^ (1 / 2 : ℂ)) ^ dimension

theorem polarRealFourierMass_pos : 0 < lattice.polarRealFourierMass :=
  inv_pos.mpr (by exact_mod_cast lattice.polarRealDeterminantScale_pos)

theorem polarRealRawFourier_const_mul (coefficient : ℂ) (weight : (Fin rank → ℝ) → ℂ) :
    lattice.polarRealRawFourier (fun x ↦ coefficient * weight x) =
      fun x ↦ coefficient * lattice.polarRealRawFourier weight x := by
  funext frequency
  simp only [polarRealRawFourier, Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ ↦ by ring)

theorem polarRealNormalizedFourier_const_mul (coefficient : ℂ) (weight : (Fin rank → ℝ) → ℂ) :
    lattice.polarRealNormalizedFourier (fun x ↦ coefficient * weight x) =
      fun x ↦ coefficient * lattice.polarRealNormalizedFourier weight x := by
  funext frequency
  simp only [polarRealNormalizedFourier, polarRealRawFourier_const_mul]
  ring

theorem polarRealNormalizedFourierInverse_const_mul (coefficient : ℂ) (weight : (Fin rank → ℝ) → ℂ) :
    lattice.polarRealNormalizedFourierInverse (fun x ↦ coefficient * weight x) =
      fun x ↦ coefficient * lattice.polarRealNormalizedFourierInverse weight x := by
  funext frequency
  simp only [polarRealNormalizedFourierInverse, polarRealNormalizedFourier_const_mul]

theorem polarRealGaussian_neg (width : ℂ) (vector : Fin rank → ℝ) :
    polarRealGaussian lattice width (-vector) = polarRealGaussian lattice width vector := by
  simp only [polarRealGaussian, Matrix.mulVec_neg, realCoordinateGaussian, Pi.neg_apply,
    Complex.ofReal_neg, neg_sq]

theorem polarRealRawFourier_gaussian {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealRawFourier (polarRealGaussian lattice width) =
      fun vector ↦ (lattice.polarRealDeterminantScale : ℂ)⁻¹ *
        realGaussianFourierCoefficient rank width * polarRealGaussian lattice width⁻¹ vector := by
  funext vector
  rw [polarRealRawFourier, polarReal_fourierIntegral_gaussian hwidth,
    polarRealGaussianFourierProduct, realCoordinateGaussianFourierProduct_eq_const_mul]
  dsimp only [realGaussianFourierCoefficient, polarRealGaussian]
  ring

theorem polarRealNormalizedFourier_gaussian {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealNormalizedFourier (polarRealGaussian lattice width) =
      fun vector ↦ realGaussianFourierCoefficient rank width * polarRealGaussian lattice width⁻¹ vector := by
  funext vector
  rw [polarRealNormalizedFourier, polarRealRawFourier_gaussian lattice hwidth]
  have hscale : (lattice.polarRealDeterminantScale : ℂ) ≠ 0 := by
    exact_mod_cast lattice.polarRealDeterminantScale_ne_zero
  dsimp only
  field_simp

theorem polarRealNormalizedFourierInverse_gaussian {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealNormalizedFourierInverse (polarRealGaussian lattice width) =
      fun vector ↦ realGaussianFourierCoefficient rank width * polarRealGaussian lattice width⁻¹ vector := by
  funext vector
  simp only [polarRealNormalizedFourierInverse, polarRealNormalizedFourier_gaussian lattice hwidth,
    polarRealGaussian_neg]

theorem realGaussianFourierCoefficient_mul_inv (dimension : ℕ) {width : ℂ} (hwidth : 0 < width.re) :
    realGaussianFourierCoefficient dimension width * realGaussianFourierCoefficient dimension width⁻¹ = 1 := by
  have hwidth0 : width ≠ 0 := by intro h; simp [h] at hwidth
  have harg : width.arg ≠ Real.pi := ((Complex.arg_lt_pi_iff.mpr (Or.inl hwidth.le))).ne
  rw [realGaussianFourierCoefficient, realGaussianFourierCoefficient, Complex.inv_cpow width _ harg]
  simp only [one_div, inv_inv]
  rw [← mul_pow, inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hwidth0)), one_pow]

/-- Actual left inversion on arbitrary complex multiples of the existing Gaussian family. -/
theorem polarRealNormalizedFourierInverse_fourier_gaussian
    (coefficient : ℂ) {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealNormalizedFourierInverse
      (lattice.polarRealNormalizedFourier (fun x ↦ coefficient * polarRealGaussian lattice width x)) =
      fun x ↦ coefficient * polarRealGaussian lattice width x := by
  rw [polarRealNormalizedFourier_const_mul, polarRealNormalizedFourier_gaussian lattice hwidth,
    polarRealNormalizedFourierInverse_const_mul,
    polarRealNormalizedFourierInverse_const_mul,
    polarRealNormalizedFourierInverse_gaussian lattice (inv_re_pos hwidth), inv_inv]
  funext vector
  dsimp only
  calc
    _ = coefficient * ((realGaussianFourierCoefficient rank width *
        realGaussianFourierCoefficient rank width⁻¹) * polarRealGaussian lattice width vector) := by ring
    _ = _ := by rw [realGaussianFourierCoefficient_mul_inv rank hwidth, one_mul]

/-- Actual right inversion on the same family; no unrestricted Fourier inversion is invoked. -/
theorem polarRealNormalizedFourier_fourierInverse_gaussian
    (coefficient : ℂ) {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealNormalizedFourier
      (lattice.polarRealNormalizedFourierInverse (fun x ↦ coefficient * polarRealGaussian lattice width x)) =
      fun x ↦ coefficient * polarRealGaussian lattice width x := by
  rw [polarRealNormalizedFourierInverse_const_mul, polarRealNormalizedFourierInverse_gaussian lattice hwidth,
    polarRealNormalizedFourier_const_mul, polarRealNormalizedFourier_const_mul,
    polarRealNormalizedFourier_gaussian lattice (inv_re_pos hwidth), inv_inv]
  funext vector
  dsimp only
  calc
    _ = coefficient * ((realGaussianFourierCoefficient rank width *
        realGaussianFourierCoefficient rank width⁻¹) * polarRealGaussian lattice width vector) := by ring
    _ = _ := by rw [realGaussianFourierCoefficient_mul_inv rank hwidth, one_mul]

/-- The native positive character shifts the width by minus i times the real phase. -/
theorem polarRealPhaseOperator_gaussian (coefficient : ℂ) (width : ℂ) (parameter : ℝ) :
    lattice.polarRealPhaseOperator parameter (fun x ↦ coefficient * polarRealGaussian lattice width x) =
      fun x ↦ coefficient * polarRealGaussian lattice (width - (parameter : ℂ) * Complex.I) x := by
  funext vector
  unfold polarRealPhaseOperator
  rw [← RationalQuadraticSpaceMatrix.realQuadraticPhase_mul_polarRealGaussian_real]
  ring

theorem polarRealHalfRankOperator_gaussian (coefficient : ℂ) (width : ℂ) (parameter : ℝ) :
    polarRealHalfRankOperator parameter (fun x ↦ coefficient * polarRealGaussian lattice width x) =
      fun x ↦ (((‖parameter‖ ^ ((rank : ℝ) / 2) : ℝ) : ℂ) * coefficient) *
        polarRealGaussian lattice (width * (parameter : ℂ) ^ 2) x := by
  funext vector
  rw [polarRealHalfRankOperator,
    RationalQuadraticSpaceMatrix.polarRealGaussian_real_dilation]
  ring

theorem polarRealRawFourier_eq_mass_normalized (weight : (Fin rank → ℝ) → ℂ) :
    lattice.polarRealRawFourier weight =
      fun x ↦ (lattice.polarRealFourierMass : ℂ) * lattice.polarRealNormalizedFourier weight x := by
  funext x
  have hs : (lattice.polarRealDeterminantScale : ℂ) ≠ 0 := by
    exact_mod_cast lattice.polarRealDeterminantScale_ne_zero
  simp only [polarRealFourierMass, polarRealNormalizedFourier, Complex.ofReal_inv,
    inv_mul_cancel_left₀ hs]

theorem polarRealRawFourierInverse_fourier_gaussian
    (coefficient : ℂ) {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealRawFourierInverse
      (lattice.polarRealRawFourier (fun x ↦ coefficient * polarRealGaussian lattice width x)) =
      fun x ↦ coefficient * polarRealGaussian lattice width x := by
  rw [polarRealRawFourier_eq_mass_normalized]
  funext x
  simp only [polarRealRawFourierInverse, polarRealNormalizedFourierInverse_const_mul,
    polarRealNormalizedFourierInverse_fourier_gaussian lattice coefficient hwidth]
  have hs : (lattice.polarRealDeterminantScale : ℂ) ≠ 0 := by
    exact_mod_cast lattice.polarRealDeterminantScale_ne_zero
  simp only [polarRealFourierMass, Complex.ofReal_inv, mul_inv_cancel_left₀ hs]

theorem polarRealRawFourier_fourierInverse_gaussian
    (coefficient : ℂ) {width : ℂ} (hwidth : 0 < width.re) :
    lattice.polarRealRawFourier
      (lattice.polarRealRawFourierInverse (fun x ↦ coefficient * polarRealGaussian lattice width x)) =
      fun x ↦ coefficient * polarRealGaussian lattice width x := by
  unfold polarRealRawFourierInverse
  rw [polarRealRawFourier_eq_mass_normalized]
  funext x
  simp only [polarRealNormalizedFourier_const_mul,
    polarRealNormalizedFourier_fourierInverse_gaussian lattice coefficient hwidth]
  have hs : (lattice.polarRealDeterminantScale : ℂ) ≠ 0 := by
    exact_mod_cast lattice.polarRealDeterminantScale_ne_zero
  simp only [polarRealFourierMass, Complex.ofReal_inv, inv_mul_cancel_left₀ hs]

/-- The actual analytic family: arbitrary complex multiples of Gaussians, with
strictly positive real width. This predicate asserts no operator relation. -/
def IsPolarRealGaussian (weight : (Fin rank → ℝ) → ℂ) : Prop :=
  ∃ coefficient width : ℂ, 0 < width.re ∧
    weight = fun x ↦ coefficient * polarRealGaussian lattice width x

theorem IsPolarRealGaussian.integrable {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) : Integrable weight volume := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  exact (integrable_polarRealGaussian hwidth lattice).const_mul coefficient

theorem IsPolarRealGaussian.continuous {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) : Continuous weight := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  exact continuous_const.mul ((continuous_realCoordinateGaussian rank width).comp
    (Matrix.toLin' lattice.polarRealSqrtMatrix).continuous_of_finiteDimensional)

/-- Every phase, scalar, Fourier and inverse-width update stays in the right half-plane. -/
theorem realGaussian_operator_widths_positive {width : ℂ} (hwidth : 0 < width.re)
    (parameter : ℝ) (hparameter : parameter ≠ 0) :
    0 < (width - (parameter : ℂ) * Complex.I).re ∧
      0 < (width * (parameter : ℂ) ^ 2).re ∧ 0 < width⁻¹.re := by
  refine ⟨by simpa using hwidth, ?_, inv_re_pos hwidth⟩
  simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using mul_pos hwidth (sq_pos_of_ne_zero hparameter)

theorem IsPolarRealGaussian.const_mul {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) (scalar : ℂ) :
    lattice.IsPolarRealGaussian (fun x ↦ scalar * weight x) := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  exact ⟨scalar * coefficient, width, hwidth, by funext x; ring⟩

theorem IsPolarRealGaussian.normalizedFourier {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) :
    lattice.IsPolarRealGaussian (lattice.polarRealNormalizedFourier weight) := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  rw [polarRealNormalizedFourier_const_mul, polarRealNormalizedFourier_gaussian lattice hwidth]
  exact ⟨coefficient * realGaussianFourierCoefficient rank width, width⁻¹, inv_re_pos hwidth,
    by funext x; ring⟩

theorem IsPolarRealGaussian.normalizedInverse {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) :
    lattice.IsPolarRealGaussian (lattice.polarRealNormalizedFourierInverse weight) := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  rw [polarRealNormalizedFourierInverse_const_mul, polarRealNormalizedFourierInverse_gaussian lattice hwidth]
  exact ⟨coefficient * realGaussianFourierCoefficient rank width, width⁻¹, inv_re_pos hwidth,
    by funext x; ring⟩

theorem IsPolarRealGaussian.rawFourier {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) :
    lattice.IsPolarRealGaussian (lattice.polarRealRawFourier weight) := by
  rw [polarRealRawFourier_eq_mass_normalized]
  exact (hweight.normalizedFourier lattice).const_mul lattice _

theorem IsPolarRealGaussian.rawInverse {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) :
    lattice.IsPolarRealGaussian (lattice.polarRealRawFourierInverse weight) :=
  (hweight.normalizedInverse lattice).const_mul lattice _

theorem IsPolarRealGaussian.phase {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) (parameter : ℝ) :
    lattice.IsPolarRealGaussian (lattice.polarRealPhaseOperator parameter weight) := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  rw [polarRealPhaseOperator_gaussian]
  exact ⟨coefficient, width - (parameter : ℂ) * Complex.I, by simpa using hwidth, rfl⟩

theorem IsPolarRealGaussian.halfRank {weight : (Fin rank → ℝ) → ℂ}
    (hweight : lattice.IsPolarRealGaussian weight) {parameter : ℝ} (hparameter : parameter ≠ 0) :
    lattice.IsPolarRealGaussian (polarRealHalfRankOperator parameter weight) := by
  obtain ⟨coefficient, width, hwidth, rfl⟩ := hweight
  rw [polarRealHalfRankOperator_gaussian]
  exact ⟨_, _, (realGaussian_operator_widths_positive hwidth parameter hparameter).2.1, rfl⟩

end PositiveDefiniteIntegralLattice
