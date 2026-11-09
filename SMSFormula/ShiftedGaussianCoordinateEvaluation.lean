import SMSFormula.AdelicL1Composition
import SMSFormula.ArchimedeanShiftedCentreBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The coordinate Gaussian against a complex linear exponential, evaluated

The archimedean half of `G_b subset L` needs the shifted Gaussian's coefficient identified with an
actual integral, not merely majorised.  Completing the square turns that identification into one
coordinate integral: the standard Gaussian against `exp(sum c_i z_i)` with the linear coefficients
complex, which is the analytic continuation of the Fourier transform to an imaginary frequency.

Mathlib has it, and locating it is the whole difficulty: `integral_cexp_neg_sum_mul_add` evaluates
`int cexp(-sum b_i z_i^2 + sum c_i z_i)` at arbitrary complex `c`, coordinatewise, with only
`0 < (b i).re`.  So no analytic continuation has to be performed here -- it is already done, and the
repository's own `realCoordinateGaussian` is that integrand at `b i = pi w`.

The one conversion is between the two ways of writing the amplitude.  Mathlib produces a product
over coordinates of `(pi / (pi w))^(1/2)`; the repository writes `1 / w^(1/2)` per coordinate.  They
agree because `pi/(pi w) = w^(-1)` and, on a width with positive real part, the inverse commutes with
the principal half power.  That hypothesis is genuinely needed: `arg` at `pi` is exactly where
`Complex.inv_cpow` fails.

Negative scope.  This is the coordinate Gaussian in the standard coordinates -- the polar square-root
change of variables is not performed, no lattice appears, and nothing here is adelic.  The linear
coefficients are arbitrary complex numbers, so this is not about any centre.
-/

noncomputable section

open MeasureTheory Complex

namespace PositiveDefiniteIntegralLattice

/-- The principal half power commutes with inversion on a width of positive real part, which is the
one conversion between mathlib's amplitude and the repository's. -/
theorem inv_cpow_half {w : ℂ} (hw : 0 < w.re) :
    (w⁻¹) ^ ((1 : ℂ) / 2) = (w ^ ((1 : ℂ) / 2))⁻¹ := by
  refine Complex.inv_cpow w _ ?_
  intro harg
  rw [Complex.arg_eq_pi_iff] at harg
  exact absurd harg.1 (not_lt.2 hw.le)

/-- The evaluation.  The repository's coordinate Gaussian against a complex linear exponential is
the coordinatewise product of the reciprocal half power and the completed-square factor.  No
analytic continuation is performed here: mathlib's own coordinatewise Gaussian evaluation already
allows the linear coefficients to be complex. -/
theorem integral_realCoordinateGaussian_mul_linearExp (n : ℕ) {w : ℂ} (hw : 0 < w.re)
    (c : Fin n → ℂ) :
    (∫ z : Fin n → ℝ, realCoordinateGaussian n w z *
        Complex.exp (∑ i, c i * (z i : ℂ)) ∂(volume : Measure (Fin n → ℝ))) =
      ∏ i, (1 / w ^ ((1 : ℂ) / 2)) *
        Complex.exp (c i ^ 2 / (4 * ((Real.pi : ℂ) * w))) := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hb : ∀ _i : Fin n, 0 < (((Real.pi : ℂ)) * w).re := by
    intro _i
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos hw
  have hpoint : ∀ z : Fin n → ℝ,
      realCoordinateGaussian n w z * Complex.exp (∑ i, c i * (z i : ℂ)) =
        Complex.exp (-∑ i, ((Real.pi : ℂ) * w) * ((z i : ℂ)) ^ 2 + ∑ i, c i * (z i : ℂ)) := by
    intro z
    rw [realCoordinateGaussian, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    congr 1
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    GaussianFourier.integral_cexp_neg_sum_mul_add hb c]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  congr 1
  rw [show ((Real.pi : ℂ)) / ((Real.pi : ℂ) * w) = w⁻¹ from by field_simp, inv_cpow_half hw]
  exact (one_div _).symm

/-! ## The shifted archimedean factor, evaluated -/

/-- The square root turns the form into the sum of squares, up to the factor two that separates the
form from its polarization.  This is the only arithmetic input from the lattice. -/
theorem dotProduct_polarRealSqrt_self (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℝ) :
    dotProduct (L.polarRealSqrtMatrix.mulVec x) (L.polarRealSqrtMatrix.mulVec x) =
      2 * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x := by
  rw [L.dotProduct_polarRealSqrtMatrix_mulVec x x,
    RationalQuadraticSpaceMatrix.realPolarMatrix_eq_two_smul_realFormMatrix,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rfl

/-- Completing the square, pointwise and in coordinates.  The quadratic phase times the Gaussian
centred at `v` is the Gaussian of the complex width `b - s i` times a linear exponential and one
constant.  The width is where the phase went; the linear coefficient is where the centre went. -/
theorem phase_mul_realCoordinateGaussian_sub (n : ℕ) (b s : ℝ) (v z : Fin n → ℝ) :
    Complex.exp (((Real.pi * s : ℝ) : ℂ) * Complex.I * ∑ i, ((z i : ℂ)) ^ 2) *
        realCoordinateGaussian n ((b : ℂ)) (z - v) =
      (realCoordinateGaussian n (SMSFormula.ArchimedeanCentre.width b s) z *
          Complex.exp (∑ i, ((2 * Real.pi * b * v i : ℝ) : ℂ) * (z i : ℂ))) *
        Complex.exp (-((Real.pi * b : ℝ) : ℂ) * ∑ i, ((v i : ℂ)) ^ 2) := by
  simp only [realCoordinateGaussian, ← Complex.exp_sum, ← Complex.exp_add, Finset.mul_sum,
    ← Finset.sum_add_distrib, Pi.sub_apply, Complex.ofReal_sub]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [SMSFormula.ArchimedeanCentre.width]
  push_cast
  ring

/-- The evaluation, at last.  The archimedean factor of the rank-one adelic Bruhat coefficient at a
shifted polar Gaussian test is the determinant scale times the repository's `shiftedCoefficient` at
the frequency, with the centre entering only through the value of the quadratic form at it.

This is the first evaluation in this line: `shiftedCoefficient` was defined as the centred power
times the completion factor, and calling it the transform of the shifted Gaussian was a naming
convention until here.  Its uniform majorant `norm_shiftedCoefficient_le` therefore now bounds an
actual integral. -/
theorem integral_fourierChar_polarRealGaussian_sub (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 < b)
    (s : ℝ) (u : Fin n → ℝ) :
    (∫ x : Fin n → ℝ,
        ((Real.fourierChar
            (s * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
          polarRealGaussian L ((b : ℂ)) (x - u) ∂(volume : Measure (Fin n → ℝ))) =
      ((L.polarRealDeterminantScale : ℝ) : ℂ)⁻¹ *
        SMSFormula.ArchimedeanCentre.shiftedCoefficient n b s
          (L.rationalQuadraticSpaceMatrix.realQuadraticFormValue u) := by
  set S := L.polarRealSqrtMatrix with hS
  set v := S.mulVec u with hv
  set w := SMSFormula.ArchimedeanCentre.width b s with hw
  have hwre : 0 < w.re := by
    rw [hw, SMSFormula.ArchimedeanCentre.width_re]; exact hb
  have hwne : w ≠ 0 := SMSFormula.ArchimedeanCentre.width_ne_zero hb s
  set g : (Fin n → ℝ) → ℂ := fun z ↦
    Complex.exp (((Real.pi * s : ℝ) : ℂ) * Complex.I * ∑ i, ((z i : ℂ)) ^ 2) *
      realCoordinateGaussian n ((b : ℂ)) (z - v) with hg
  -- the integrand is `g` after the square root
  have hintegrand :
      (fun x : Fin n → ℝ ↦
        ((Real.fourierChar
            (s * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
          polarRealGaussian L ((b : ℂ)) (x - u)) = fun x ↦ g (S.mulVec x) := by
    funext x
    have hsq : ∑ i, ((S.mulVec x i : ℂ)) ^ 2 =
        ((2 * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x : ℝ) : ℂ) := by
      rw [← L.dotProduct_polarRealSqrt_self x]
      push_cast [dotProduct]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hgauss : polarRealGaussian L ((b : ℂ)) (x - u) =
        realCoordinateGaussian n ((b : ℂ)) (S.mulVec x - v) := by
      rw [polarRealGaussian, hv, ← Matrix.mulVec_sub]
    rw [hgauss, hg]
    simp only [hsq]
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring_nf
  rw [hintegrand]
  -- change of variables
  have hgcont : Continuous g := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact (continuous_realCoordinateGaussian n ((b : ℂ))).comp
        (continuous_id.sub continuous_const)
  have hmeas : AEMeasurable (Matrix.toLin' S) (volume : Measure (Fin n → ℝ)) :=
    (Matrix.toLin' S).continuous_of_finiteDimensional.measurable.aemeasurable
  have hchange :
      (∫ z : Fin n → ℝ, g z
          ∂Measure.map (Matrix.toLin' S) (volume : Measure (Fin n → ℝ))) =
        ∫ x : Fin n → ℝ, g (S.mulVec x) := by
    simpa only [Matrix.toLin'_apply] using integral_map hmeas hgcont.aestronglyMeasurable
  rw [← hchange, hS, L.map_polarRealSqrtMatrix_volume, integral_smul_measure,
    show (ENNReal.ofReal (L.polarRealDeterminantScale : ℝ)⁻¹).toReal =
        (L.polarRealDeterminantScale : ℝ)⁻¹ by
      rw [ENNReal.toReal_ofReal]
      exact le_of_lt (inv_pos.mpr (by exact_mod_cast L.polarRealDeterminantScale_pos)),
    Complex.real_smul, Complex.ofReal_inv]
  congr 1
  -- the coordinate integral
  have hpt : ∀ z : Fin n → ℝ, g z =
      (realCoordinateGaussian n w z *
        Complex.exp (∑ i, ((2 * Real.pi * b * v i : ℝ) : ℂ) * (z i : ℂ))) *
        Complex.exp (-((Real.pi * b : ℝ) : ℂ) * ∑ i, ((v i : ℂ)) ^ 2) := fun z ↦
    phase_mul_realCoordinateGaussian_sub n b s v z
  simp only [hpt]
  rw [MeasureTheory.integral_mul_const,
    integral_realCoordinateGaussian_mul_linearExp n hwre
      (fun i ↦ ((2 * Real.pi * b * v i : ℝ) : ℂ))]
  -- collect the product
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Complex.exp_sum, Finset.card_univ,
    Fintype.card_fin]
  rw [mul_assoc, ← Complex.exp_add]
  rw [SMSFormula.ArchimedeanCentre.shiftedCoefficient]
  congr 1
  · -- the amplitude
    rw [div_pow, one_pow, ← Complex.cpow_nat_mul, one_div, ← Complex.cpow_neg, ← hw]
    congr 1
    push_cast
    ring
  · -- the exponent
    have hvsq : ∑ i, ((v i : ℂ)) ^ 2 =
        ((2 * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue u : ℝ) : ℂ) := by
      rw [hv, ← L.dotProduct_polarRealSqrt_self u]
      push_cast [dotProduct]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hcsq : ∑ i, ((2 * Real.pi * b * v i : ℝ) : ℂ) ^ 2 / (4 * ((Real.pi : ℂ) * w)) =
        (∑ i, ((2 * Real.pi * b * v i : ℝ) : ℂ) ^ 2) / (4 * ((Real.pi : ℂ) * w)) := by
      rw [Finset.sum_div]
    rw [hcsq]
    have hexp : ∑ i, ((2 * Real.pi * b * v i : ℝ) : ℂ) ^ 2 =
        ((2 * Real.pi * b : ℝ) : ℂ) ^ 2 * ∑ i, ((v i : ℂ)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
    rw [hexp, hvsq, SMSFormula.ArchimedeanCentre.shiftExponent, ← hw]
    congr 1
    have hb' : (s : ℂ) * Complex.I = (b : ℂ) - w := by
      rw [hw, SMSFormula.ArchimedeanCentre.width]; ring
    have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hb']
    push_cast
    field_simp
    ring

/-! ## The shifted factor's `lintegral` in the frequency -/

/-- The form is nonnegative on the nose, which is what the centre-uniform majorant needs at the
value `Q u`. -/
theorem realQuadraticFormValue_nonneg (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℝ) :
    0 ≤ L.rationalQuadraticSpaceMatrix.realQuadraticFormValue u := by
  have h : 0 ≤ dotProduct (L.polarRealSqrtMatrix.mulVec u) (L.polarRealSqrtMatrix.mulVec u) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  rw [L.dotProduct_polarRealSqrt_self u] at h
  linarith

/-- The archimedean half at a shifted centre, on the infinite adeles, and now of an actual
integral.  Above rank two the `lintegral` in the frequency of the shifted archimedean factor is
finite, and the bound does not depend on the centre: the evaluation identifies the factor with the
repository's `shiftedCoefficient`, whose majorant is the centred one. -/
theorem lintegral_norm_shiftedArchimedeanFactor_lt_top (L : PositiveDefiniteIntegralLattice n) {b : ℝ}
    (hb : 0 < b) (hn : 2 < n) (u : Fin n → ℝ) :
    ∫⁻ w : RationalInfiniteAdele, ENNReal.ofReal
        ‖∫ x : Fin n → ℝ, ((Real.fourierChar
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) *
                L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
            polarRealGaussian L ((b : ℂ)) (x - u) ∂(volume : Measure (Fin n → ℝ))‖
      ∂rationalInfiniteAdeleAddHaarMeasure < ⊤ := by
  have hscale : (0 : ℝ) < (L.polarRealDeterminantScale : ℝ) := by
    exact_mod_cast L.polarRealDeterminantScale_pos
  have hQ := L.realQuadraticFormValue_nonneg u
  rw [lintegral_infiniteAdele_eq_lintegral_real]
  have hint : Integrable (fun s : ℝ ↦ (L.polarRealDeterminantScale : ℝ)⁻¹ *
      (b ^ 2 + s ^ 2) ^ (-(n : ℝ) / 4)) (volume : Measure ℝ) :=
    (SMSFormula.Archimedean.integrable_shifted_bound hn hb).const_mul _
  have hfin := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun s ↦ ?_) hfin
  rw [show (rationalInfiniteAdeleContinuousAddEquivReal
      (rationalInfiniteAdeleContinuousAddEquivReal.symm s) : ℝ) = s from by simp,
    L.integral_fourierChar_polarRealGaussian_sub hb s u, norm_mul, ← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ (le_abs_self _))
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
  exact mul_le_mul_of_nonneg_left
    (SMSFormula.ArchimedeanCentre.norm_shiftedCoefficient_le n hb s hQ)
    (le_of_lt (inv_pos.mpr hscale))

/-- The bridge to the composition, in the exact shape the local-factor criterion consumes: at a
product test whose archimedean half is the shifted polar Gaussian, the adelic Bruhat coefficient is
the function of the infinite component whose `lintegral` is bounded above, times the finite factor.
So nothing further has to be said about the archimedean half. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_shiftedGaussianTest (L : PositiveDefiniteIntegralLattice n)
    (b : ℝ) (u : Fin n → ℝ) (PhiFin : (Fin n → RationalFiniteAdele) → ℂ) (a : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (fun x ↦ polarRealGaussian L ((b : ℂ)) (rationalAdeleVectorRealPart n x - u) *
          PhiFin (rationalAdeleVectorFinitePart n x)) a =
      (∫ x : Fin n → ℝ, ((Real.fourierChar
              ((rationalInfiniteAdeleContinuousAddEquivReal a.1 : ℝ) *
                L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
            polarRealGaussian L ((b : ℂ)) (x - u) ∂(volume : Measure (Fin n → ℝ))) *
        (∫ x, ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt a.2 x :
              Circle) : ℂ) * PhiFin x ∂(RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure n)) :=
  rationalAdeleRankOneAdelicBruhatCoefficient_productTest L.rationalQuadraticSpaceMatrix a
    (fun x ↦ polarRealGaussian L ((b : ℂ)) (x - u)) PhiFin

end PositiveDefiniteIntegralLattice
