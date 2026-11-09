import SMSFormula.RationalAdeleCompactOpenPoissonWeylForm

/-!
# The width scaling of the real Gaussian Fourier transform

Conversion (b) of the covariance assembly needs the real half of the dual side pushed back from the
transported width `b / N^2` to the original `b`.  The only genuinely new input is the half-power
identity `(b / c^2)^(1/2) = b^(1/2) / c` for a positive real `c`, which is proved here from the
principal branch: both sides square to the same number and both have positive real part, and two
such numbers agree.

Everything else is the existing closed form of the polar Gaussian's real Fourier integral.
-/

noncomputable section

open Complex PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

/-- The principal half power of a number with positive real part again has positive real part. -/
theorem cpow_half_re_pos {b : ℂ} (hb : 0 < b.re) : 0 < (b ^ (1/2 : ℂ)).re := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  rw [Complex.cpow_def_of_ne_zero hb0, Complex.exp_re]
  have harg : |Complex.arg b| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have him : (Complex.log b * (1/2 : ℂ)).im = Complex.arg b / 2 := by
    simp [Complex.log_im, Complex.mul_im]
    ring
  rw [him]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have hpi := Real.pi_pos
    have := (abs_lt.mp harg).1
    linarith
  · have hpi := Real.pi_pos
    have := (abs_lt.mp harg).2
    linarith

/-- Two numbers with positive real part and equal squares are equal. -/
theorem sq_eq_sq_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) (h : z ^ 2 = w ^ 2) :
    z = w := by
  have hfac : (z - w) * (z + w) = 0 := by
    ring_nf
    linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact sub_eq_zero.mp h1
  · exfalso
    have hre : (z + w).re = 0 := by
      rw [h2]
      simp
    rw [Complex.add_re] at hre
    linarith

/-- The half-power identity, on the principal branch, for a positive real denominator. -/
theorem cpow_half_div_sq_ofReal {b : ℂ} (hb : 0 < b.re) {c : ℝ} (hc : 0 < c) :
    (b / ((c : ℂ)) ^ 2) ^ (1/2 : ℂ) = b ^ (1/2 : ℂ) / (c : ℂ) := by
  have hsq : ((c : ℂ)) ^ 2 = (((c ^ 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hquot_re : 0 < (b / ((c : ℂ)) ^ 2).re := by
    rw [hsq, Complex.div_ofReal_re]
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    exact div_pos hb hc2
  have hpow : ∀ x : ℂ, (x ^ (1/2 : ℂ)) ^ (2 : ℕ) = x := by
    intro x
    simpa [one_div] using Complex.cpow_nat_inv_pow x (n := 2) two_ne_zero
  have h1 : ((b / ((c : ℂ)) ^ 2) ^ (1/2 : ℂ)) ^ (2 : ℕ) = b / ((c : ℂ)) ^ 2 := hpow _
  have h2 : (b ^ (1/2 : ℂ) / (c : ℂ)) ^ (2 : ℕ) = b / ((c : ℂ)) ^ 2 := by
    rw [div_pow, hpow]
  refine sq_eq_sq_of_re_pos (cpow_half_re_pos hquot_re) ?_ (h1.trans h2.symm)
  rw [Complex.div_ofReal_re]
  exact div_pos (cpow_half_re_pos hb) hc

/-- The Gaussian Fourier coefficient scales by `c^d` when the width is divided by `c^2`. -/
theorem realGaussianFourierCoefficient_div_sq (d : ℕ) {b : ℂ} (hb : 0 < b.re)
    {c : ℝ} (hc : 0 < c) :
    realGaussianFourierCoefficient d (b / ((c : ℂ)) ^ 2) =
      ((c : ℂ)) ^ d * realGaussianFourierCoefficient d b := by
  have hcne : ((c : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hc
  rw [realGaussianFourierCoefficient, realGaussianFourierCoefficient,
    cpow_half_div_sq_ofReal hb hc, ← mul_pow]
  congr 1
  field_simp

variable {n : ℕ}

/-- The real half of conversion (b): dividing the width by `c^2` is the same as scaling the
frequency by `c`, up to the explicit factor `c^n`. -/
theorem fourierIntegral_polarGaussian_div_sq (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {c : ℝ} (hc : 0 < c) (w : Fin n → ℝ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume
        (polarRealGaussian L (b / ((c : ℂ)) ^ 2)) w =
      ((c : ℂ)) ^ n * Fourier.fourierIntegral (realCoordinateFourierChar n) volume
        (polarRealGaussian L b) (fun i ↦ c * w i) := by
  have hcne : ((c : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hc
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  have hsq : ((c : ℂ)) ^ 2 = (((c ^ 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hquot_re : 0 < (b / ((c : ℂ)) ^ 2).re := by
    rw [hsq, Complex.div_ofReal_re]
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    exact div_pos hb hc2
  rw [fourierIntegral_polarGaussian_eq_inverseMatrix_exp L hquot_re,
    fourierIntegral_polarGaussian_eq_inverseMatrix_exp L hb,
    realGaussianFourierCoefficient_div_sq n hb hc]
  have hquad : ((fun i ↦ c * w i) ⬝ᵥ
      L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.mulVec (fun i ↦ c * w i)) =
      c ^ 2 * (w ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.mulVec w) := by
    have hsmul : (fun i ↦ c * w i) = c • w := by
      funext i
      simp [smul_eq_mul]
    rw [hsmul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hquad]
  have hexp : (b / ((c : ℂ)) ^ 2)⁻¹ = ((c : ℂ)) ^ 2 * b⁻¹ := by
    field_simp
  rw [hexp]
  push_cast
  ring_nf

/-- The finite half of conversion (b): the transform of the scaled carrier is the transform of the
carrier at the scaled frequency, times the exact Haar factor `N^-n`. -/
theorem standardFiniteFourier_scaledCarrier {N : ℕ} (hN : N ≠ 0)
    (K : Set (Fin n → RationalFiniteAdele)) (v : Fin n → RationalFiniteAdele) :
    standardFiniteFourier
        ((scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)) v =
      ((N : ℂ))⁻¹ ^ n *
        standardFiniteFourier (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
          (fun i ↦ (N : RationalFiniteAdele) * v i) := by
  have hq : ((N : ℚ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hN)
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set F : (Fin n → RationalFiniteAdele) → ℂ := fun y ↦
    (rationalFiniteAdeleFourierChar
        (-(dotProduct y (fun i ↦ (N : RationalFiniteAdele) * v i))) : ℂ) *
      K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ) y with hF
  have hcancel : ∀ x : Fin n → RationalFiniteAdele,
      (fun i ↦ (N : RationalFiniteAdele) *
        (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x) i) = x := by
    intro x
    funext i
    show (N : RationalFiniteAdele) *
      (algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * x i) = x i
    rw [← mul_assoc,
      show (N : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((N : ℚ)) from
        (map_natCast (algebraMap ℚ RationalFiniteAdele) N).symm,
      ← map_mul, mul_inv_cancel₀ hNQ, map_one, one_mul]
  have hstep : ∀ x : Fin n → RationalFiniteAdele,
      F (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x) =
        (rationalFiniteAdeleFourierChar (-(dotProduct x v)) : ℂ) *
          (scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ) x := by
    intro x
    have hdot : dotProduct (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x)
        (fun i ↦ (N : RationalFiniteAdele) * v i) = dotProduct x v := by
      have hunit : ∀ i, (N : RationalFiniteAdele) *
          (algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * x i) = x i := by
        intro i
        rw [← mul_assoc,
          show (N : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((N : ℚ)) from
            (map_natCast (algebraMap ℚ RationalFiniteAdele) N).symm,
          ← map_mul, mul_inv_cancel₀ hNQ, map_one, one_mul]
      have hterm : ∀ i, (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x) i *
          ((N : RationalFiniteAdele) * v i) = x i * v i := by
        intro i
        show (algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * x i) *
          ((N : RationalFiniteAdele) * v i) = x i * v i
        calc (algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * x i) *
              ((N : RationalFiniteAdele) * v i)
            = ((N : RationalFiniteAdele) *
                (algebraMap ℚ RationalFiniteAdele ((N : ℚ))⁻¹ * x i)) * v i := by ring
          _ = x i * v i := by rw [hunit i]
      simp only [dotProduct, hterm]
    have hmem : K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
        (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x) =
        (scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ) x := by
      by_cases h : rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x ∈ K
      · have hx : x ∈ scaledCarrier N K := by
          have := (mem_scaledCarrier_iff hN
            (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x)).mp h
          rwa [hcancel x] at this
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hx]
        rfl
      · have hx : x ∉ scaledCarrier N K := by
          intro hmem'
          refine h ((mem_scaledCarrier_iff hN _).mpr ?_)
          rwa [hcancel x]
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hx]
    rw [hF]
    show (rationalFiniteAdeleFourierChar
        (-(dotProduct (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x)
          (fun i ↦ (N : RationalFiniteAdele) * v i))) : ℂ) * _ = _
    rw [hdot, hmem]
  show (∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct x v)) : ℂ) *
      (scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ) x
      ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) = _
  rw [show (fun x : Fin n → RationalFiniteAdele ↦
      (rationalFiniteAdeleFourierChar (-(dotProduct x v)) : ℂ) *
        (scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ) x) =
      fun x ↦ F (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x) from
    funext fun x ↦ (hstep x).symm]
  rw [integral_rationalFiniteAdeleCoordinateScale_inv n hN hq F]
  rfl

/-- The punchline of conversion (b): the two scaling factors cancel.  The dual factor at the
transported width and scaled carrier equals the dual factor at the original width and carrier,
evaluated at the scaled frequency, with no leftover constant -- `N^n` against `N^-n`. -/
theorem dualFactor_scaling_cancel (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    {N : ℕ} (hN : N ≠ 0) (K : Set (Fin n → RationalFiniteAdele))
    (w : Fin n → ℝ) (v : Fin n → RationalFiniteAdele) :
    Fourier.fourierIntegral (realCoordinateFourierChar n) volume
          (polarRealGaussian L (b / (((N : ℕ) : ℝ) : ℂ) ^ 2)) w *
        standardFiniteFourier
          ((scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)) v =
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
          (fun i ↦ ((N : ℕ) : ℝ) * w i) *
        standardFiniteFourier (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
          (fun i ↦ (N : RationalFiniteAdele) * v i) := by
  have hNR : (0 : ℝ) < ((N : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hNC : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [fourierIntegral_polarGaussian_div_sq L hb hNR w,
    standardFiniteFourier_scaledCarrier hN K v]
  have hcast : (((N : ℕ) : ℝ) : ℂ) = ((N : ℂ)) := by
    simp
  rw [hcast]
  have hcancel : ((N : ℂ)) ^ n * (((N : ℂ))⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNC, one_pow]
  set A := Fourier.fourierIntegral (realCoordinateFourierChar n) volume
    (polarRealGaussian L b) (fun i ↦ ((N : ℕ) : ℝ) * w i) with hA
  set B := standardFiniteFourier (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
    (fun i ↦ (N : RationalFiniteAdele) * v i) with hB
  linear_combination (A * B) * hcancel

end RationalQuadraticSpaceMatrix

end
