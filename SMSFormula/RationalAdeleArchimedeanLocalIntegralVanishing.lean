import SMSFormula.RationalAdeleArchimedeanGaussianRegulator

/-!
# The archimedean local integral vanishes at every negative frequency

This closes the single named analytic obstacle.  The classical statement is that
`int_R e(-b t) (c - i t)^{-n/2} dt` vanishes for `b < 0`; the usual proofs go through a
complex-rate Gamma integral or a contour shift, neither of which is available.  The proof
here is elementary: it inserts a Gaussian regulator, uses the existing representation of
the archimedean factor as a Gaussian integral in the nonnegative polar value, and lets the
regulator width go to zero.

The regularized integral equals
`int_{R^n} exp(-pi c P(x)) eps^{-1/2} exp(-pi (t + P(x)/2)^2 / eps) dx`, whose modulus is
at most `eps^{-1/2} exp(-pi t^2 / eps)` times a fixed mass whenever `t > 0`, because
`P(x) >= 0`.  That tends to zero, while the regularized integrals converge to the actual
integral by dominated convergence against the existing integrable modulus.

Negative scope: this evaluates only the archimedean factor, and only at frequencies of one
sign.  The finite local integral is untouched, no Euler product is asserted, and the
positive-frequency value is not computed.  No contour, Gamma identity, inversion theorem,
new measure, chart or Haar normalization is used.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The archimedean Bruhat factor is continuous in the frequency variable. -/
theorem continuous_archimedeanBruhatFactor (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) :
    Continuous fun v : ℝ => (L.polarRealDeterminantScale : ℂ)⁻¹ *
      (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n := by
  have hbase : Continuous fun v : ℝ => (c : ℂ) - (v : ℂ) * Complex.I := by fun_prop
  have hslit : ∀ v : ℝ, ((c : ℂ) - (v : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro v
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simpa using hc
  have hcp : Continuous fun v : ℝ => ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ) := by
    refine continuous_iff_continuousAt.mpr fun v => ?_
    exact ContinuousAt.comp (g := fun z : ℂ => z ^ (1 / 2 : ℂ))
      (f := fun v : ℝ => (c : ℂ) - (v : ℂ) * Complex.I) (x := v)
      (continuousAt_cpow_const (hslit v)) hbase.continuousAt
  have hne : ∀ v : ℝ, ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro v
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨hz, -⟩
    have : ((c : ℂ) - (v : ℂ) * Complex.I).re = c := by simp
    rw [hz] at this
    simp at this
    exact hc.ne' this.symm
  have hEq : (fun v : ℝ => (((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ))⁻¹ ^ n) =
      fun v : ℝ => (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n := by
    funext v
    simp only [one_div]
  exact continuous_const.mul (hEq ▸ ((hcp.inv₀ hne).pow n))

/-- The regulator constant tends to zero along the reciprocal widths. -/
theorem tendsto_gaussianRegulatorConstant {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
        (Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ *
          Real.exp (-Real.pi * t ^ 2 / (1 / ((k : ℝ) + 1))))
      atTop (𝓝 0) := by
  have hpt : (0 : ℝ) < Real.pi * t ^ 2 := by positivity
  have hu : Tendsto (fun k : ℕ => Real.pi * t ^ 2 * ((k : ℝ) + 1)) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hpt ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun k : ℕ =>
      (Real.pi * t ^ 2 * ((k : ℝ) + 1)) ^ 1 *
        Real.exp (-(Real.pi * t ^ 2 * ((k : ℝ) + 1)))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have hg : Tendsto (fun k : ℕ =>
      (Real.pi * t ^ 2)⁻¹ *
        ((Real.pi * t ^ 2 * ((k : ℝ) + 1)) ^ 1 *
          Real.exp (-(Real.pi * t ^ 2 * ((k : ℝ) + 1))))) atTop (𝓝 0) := by
    have h2 := hcomp.const_mul ((Real.pi * t ^ 2)⁻¹)
    rwa [mul_zero] at h2
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) hg
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt (1 / ((k : ℝ) + 1)) = (Real.sqrt ((k : ℝ) + 1))⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  have hsle : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hexpeq : -Real.pi * t ^ 2 / (1 / ((k : ℝ) + 1)) =
      -(Real.pi * t ^ 2 * ((k : ℝ) + 1)) := by
    field_simp
  rw [hsqrt, inv_inv, hexpeq]
  have hEpos : (0 : ℝ) < Real.exp (-(Real.pi * t ^ 2 * ((k : ℝ) + 1))) := Real.exp_pos _
  have : (Real.pi * t ^ 2)⁻¹ *
      ((Real.pi * t ^ 2 * ((k : ℝ) + 1)) ^ 1 *
        Real.exp (-(Real.pi * t ^ 2 * ((k : ℝ) + 1)))) =
      ((k : ℝ) + 1) * Real.exp (-(Real.pi * t ^ 2 * ((k : ℝ) + 1))) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right hsle hEpos.le

/-- The Gaussian-regularized archimedean integrals converge to the actual archimedean
local integral, by dominated convergence against the existing integrable modulus. -/
theorem tendsto_integral_regularizedArchimedean (L : PositiveDefiniteIntegralLattice n) {c t : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) :
    Tendsto (fun k : ℕ => ∫ v : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
          Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) atTop
      (𝓝 (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n))) := by
  have hA := L.continuous_archimedeanBruhatFactor hc
  have hbound_int : Integrable (fun v : ℝ =>
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n) (volume : Measure ℝ) :=
    (integrable_archimedeanBound hc hn).const_mul _
  have hFcont : ∀ k : ℕ, Continuous (fun v : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) :=
    fun _ => Continuous.mul (by fun_prop) hA
  refine tendsto_integral_of_dominated_convergence _
    (fun k => (hFcont k).aestronglyMeasurable) hbound_int ?_ ?_
  · intro k
    filter_upwards with v
    rw [norm_mul, norm_mul, norm_archimedeanBruhatFactor]
    have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hcast : (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) =
        ((-(Real.pi * (1 / ((k : ℝ) + 1))) * v ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have h2 : ‖Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2)‖ ≤ 1 := by
      rw [hcast, Complex.norm_exp, Complex.ofReal_re, Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ Real.pi * (1 / ((k : ℝ) + 1)) := by positivity
      nlinarith [sq_nonneg v]
    rw [h1, one_mul]
    have hX : (0 : ℝ) ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n := by positivity
    nlinarith [norm_nonneg
      (Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2))]
  · filter_upwards with v
    have hzero : Tendsto (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h
      simpa [Function.comp_def] using h2
    have hx : Tendsto (fun k : ℕ =>
        -Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) atTop (𝓝 0) := by
      simpa using (hzero.const_mul (-(Real.pi : ℂ))).mul_const ((v : ℂ) ^ 2)
    have hexp : Tendsto (fun k : ℕ =>
        Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2))
        atTop (𝓝 1) := by
      simpa using (Complex.continuous_exp.tendsto 0).comp hx
    simpa using (tendsto_const_nhds.mul hexp).mul tendsto_const_nhds

set_option maxHeartbeats 1000000 in
/-- The vanishing: the archimedean local integral is zero at every positive frequency
parameter.  Elementary: Gaussian regulator, the nonnegative polar value, and a limit. -/
theorem integral_archimedeanBruhatFactor_eq_zero (L : PositiveDefiniteIntegralLattice n) {c t : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) (ht : 0 < t) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) = 0 := by
  have hlim := L.tendsto_integral_regularizedArchimedean (c := c) (t := t) hc hn
  have hzerolim : Tendsto (fun k : ℕ => ∫ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ =>
        (Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ *
            Real.exp (-Real.pi * t ^ 2 / (1 / ((k : ℝ) + 1))) *
          ∫ x : Fin n → ℝ, Real.exp (-Real.pi * c * L.polarRealValue x))
        atTop (𝓝 0) := by
      have h := (tendsto_gaussianRegulatorConstant ht).mul_const
        (∫ x : Fin n → ℝ, Real.exp (-Real.pi * c * L.polarRealValue x))
      rwa [zero_mul] at h
    refine squeeze_zero_norm (fun k => ?_) hg
    exact L.norm_integral_regularizedArchimedean_le hc (by positivity) ht
  exact tendsto_nhds_unique hlim hzerolim

/-- The archimedean local integral, transported to the literal real line. -/
theorem integral_archimedeanLocal_eq_real (L : PositiveDefiniteIntegralLattice n) (c : ℝ) (t : ℚ) :
    (∫ w : RationalInfiniteAdele,
        ((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele t * w) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) -
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)
        ∂rationalInfiniteAdeleAddHaarMeasure) =
      ∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) := by
  rw [integral_infiniteAdele_eq_integral_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  have hmulgen : ∀ x y : RationalInfiniteAdele,
      rationalInfiniteAdeleContinuousAddEquivReal (x * y) =
        rationalInfiniteAdeleContinuousAddEquivReal x *
          rationalInfiniteAdeleContinuousAddEquivReal y :=
    fun x y => rationalInfiniteAdeleRingEquivReal.map_mul x y
  have hmul : rationalInfiniteAdeleContinuousAddEquivReal
      (algebraMap ℚ RationalInfiniteAdele t *
        rationalInfiniteAdeleContinuousAddEquivReal.symm v) = (t : ℝ) * v := by
    rw [hmulgen, rationalInfiniteAdeleContinuousAddEquivReal_algebraMap,
      rationalInfiniteAdeleContinuousAddEquivReal.apply_symm_apply]
    simp
  rw [rationalInfiniteAdeleFourierChar_apply, hmul,
    rationalInfiniteAdeleContinuousAddEquivReal.apply_symm_apply]
  congr 1
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The archimedean local integral vanishes at every negative rational frequency. -/
theorem integral_archimedeanLocal_eq_zero (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) {b : ℚ} (hb : b < 0) :
    (∫ w : RationalInfiniteAdele,
        ((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele (-b) * w) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) -
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)
        ∂rationalInfiniteAdeleAddHaarMeasure) = 0 := by
  rw [integral_archimedeanLocal_eq_real]
  have ht : (0 : ℝ) < (((-b : ℚ)) : ℝ) := by
    exact_mod_cast neg_pos.mpr hb
  exact L.integral_archimedeanBruhatFactor_eq_zero hc hn ht

end PositiveDefiniteIntegralLattice
