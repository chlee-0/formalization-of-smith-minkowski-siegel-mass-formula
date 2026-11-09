import SMSFormula.RationalAdeleFiniteLocalIntegralVanishing

/-!
# The zero frequency also vanishes

The archimedean local factor is evaluated at every nonzero parameter: zero at a positive
one, an explicit density at a negative one.  This file treats the zero parameter, where the
peak argument gives nothing because the concentration point is the boundary `u = 0`.

The existing regularized value form settles it directly.  At parameter zero the regularized
integral is

```text
(detScale^{-1} kappa_n) * int_{(0,inf)} u^{n/2-1} e^{-pi c u} eps^{-1/2} e^{-pi u^2/(4 eps)} du,
```

and the elementary inequality `x^2 >= x - 1/4` turns the Gaussian factor into an exponential
one, so the existing real Gamma evaluation bounds the whole thing by a constant times
`eps^{(n/2-1)/2}`.  For rank at least three that exponent is positive, so the bound tends to
zero and the existing dominated convergence identifies the limit.  Hence the archimedean
local integral at the zero frequency is zero as well, and with the existing local product

```text
int_{A/Q} psi_0 (ThetaUnip - E) = 0.
```

Scope: this is the zero frequency only.  It says nothing about the positive
integer frequencies, where the difference is the scale-free arithmetic quantity `C_m` whose
vanishing is exactly the single-lattice mass identity.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The existing real Gamma integral, in the exponential-rate form used below. -/
theorem integral_rpow_mul_exp_neg_mul_Ioi_eval {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    (∫ u in Ioi (0 : ℝ), u ^ a * Real.exp (-b * u)) =
      b ^ (-(a + 1)) * Real.Gamma (a + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a) (b := b) one_pos ha hb
  simp only [Real.rpow_one, div_one] at h
  rw [h]
  ring

/-- The elementary inequality turning a Gaussian rate into an exponential one. -/
theorem exp_neg_sq_le (x : ℝ) :
    Real.exp (-Real.pi * x ^ 2) ≤ Real.exp (Real.pi / 4) * Real.exp (-Real.pi * x) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [sq_nonneg (x - 1/2), Real.pi_pos]

/-- The zero-parameter value integral is bounded by a constant times a positive power of
the regulator width. -/
theorem abs_zeroFrequency_valueIntegral_le (hn : 3 ≤ n) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) :
    |∫ u in Ioi (0 : ℝ), u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
        (2 * (2 * Real.sqrt ε)⁻¹ *
          Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * (0 : ℝ) - u)) ^ 2))| ≤
      Real.exp (Real.pi / 4) * (Real.sqrt ε)⁻¹ *
        ((Real.pi / (2 * Real.sqrt ε)) ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2)) := by
  have hn0 : 0 < n := by omega
  have hnr : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha0 : (0 : ℝ) ≤ (n : ℝ) / 2 - 1 := by linarith
  have ha : (-1 : ℝ) < (n : ℝ) / 2 - 1 := by linarith
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hbeta : 0 < Real.pi / (2 * Real.sqrt ε) := by positivity
  have hcontrpow : Continuous fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) :=
    continuous_iff_continuousAt.mpr fun x => Real.continuousAt_rpow_const x _ (Or.inr ha0)
  have hcont : Continuous (fun u : ℝ =>
      u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
        (2 * (2 * Real.sqrt ε)⁻¹ *
          Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * (0 : ℝ) - u)) ^ 2))) :=
    (hcontrpow.mul (by fun_prop)).mul (by fun_prop)
  have hmaj : IntegrableOn
      (fun u : ℝ => (Real.exp (Real.pi / 4) * (Real.sqrt ε)⁻¹) *
        (u ^ ((n : ℝ) / 2 - 1) *
          Real.exp (-(Real.pi / (2 * Real.sqrt ε)) * u))) (Ioi (0 : ℝ)) :=
    (integrableOn_valueProfile hn0 hbeta).const_mul _
  have hnonneg : ∀ u ∈ Ioi (0 : ℝ),
      0 ≤ u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
        (2 * (2 * Real.sqrt ε)⁻¹ *
          Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * (0 : ℝ) - u)) ^ 2)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    positivity
  have hle : ∀ u ∈ Ioi (0 : ℝ),
      u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
        (2 * (2 * Real.sqrt ε)⁻¹ *
          Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * (0 : ℝ) - u)) ^ 2)) ≤
        (Real.exp (Real.pi / 4) * (Real.sqrt ε)⁻¹) *
          (u ^ ((n : ℝ) / 2 - 1) *
            Real.exp (-(Real.pi / (2 * Real.sqrt ε)) * u)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hupow : (0 : ℝ) ≤ u ^ ((n : ℝ) / 2 - 1) := (Real.rpow_pos_of_pos hu0 _).le
    have hcoef : 2 * (2 * Real.sqrt ε)⁻¹ = (Real.sqrt ε)⁻¹ := by field_simp
    have harg : ((2 * Real.sqrt ε)⁻¹ * (-2 * (0 : ℝ) - u)) ^ 2 =
        ((2 * Real.sqrt ε)⁻¹ * u) ^ 2 := by ring
    have hgauss := exp_neg_sq_le ((2 * Real.sqrt ε)⁻¹ * u)
    have hexp1 : Real.exp (-(Real.pi * c) * u) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hpos : 0 < Real.pi * c * u := mul_pos (mul_pos Real.pi_pos hc) hu0
      nlinarith [hpos]
    have hrate : Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * u)) =
        Real.exp (-(Real.pi / (2 * Real.sqrt ε)) * u) := by
      congr 1
      field_simp
    rw [harg, hcoef]
    have hstep : u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
        ((Real.sqrt ε)⁻¹ *
          Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * u) ^ 2)) ≤
        u ^ ((n : ℝ) / 2 - 1) * 1 *
          ((Real.sqrt ε)⁻¹ *
            (Real.exp (Real.pi / 4) *
              Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * u)))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hexp1 hupow)
        (mul_le_mul_of_nonneg_left hgauss (by positivity)) (by positivity) (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [hrate]
    ring
  have hfint : IntegrableOn (fun u : ℝ =>
      u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
        (2 * (2 * Real.sqrt ε)⁻¹ *
          Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * (0 : ℝ) - u)) ^ 2)))
      (Ioi (0 : ℝ)) := by
    refine hmaj.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (hnonneg u hu)]
    exact hle u hu
  rw [abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi hnonneg)]
  refine le_trans (setIntegral_mono_on hfint hmaj measurableSet_Ioi hle) ?_
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi_eval ha hbeta]
  rw [show (n : ℝ) / 2 - 1 + 1 = (n : ℝ) / 2 from by ring, mul_assoc]

/-- The bound tends to zero along the reciprocal widths, for rank at least three. -/
theorem tendsto_zeroFrequencyBound (hn : 3 ≤ n) :
    Tendsto (fun k : ℕ =>
        Real.exp (Real.pi / 4) * (Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ *
          ((Real.pi / (2 * Real.sqrt (1 / ((k : ℝ) + 1)))) ^ (-((n : ℝ) / 2)) *
            Real.Gamma ((n : ℝ) / 2)))
      atTop (𝓝 0) := by
  have hnr : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : (0 : ℝ) < (n : ℝ) / 2 - 1 := by linarith
  have hrw : ∀ ε : ℝ, 0 < ε →
      Real.exp (Real.pi / 4) * (Real.sqrt ε)⁻¹ *
        ((Real.pi / (2 * Real.sqrt ε)) ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2)) =
      (Real.exp (Real.pi / 4) * Real.Gamma ((n : ℝ) / 2) *
        (2 / Real.pi) ^ ((n : ℝ) / 2)) * (Real.sqrt ε) ^ ((n : ℝ) / 2 - 1) := by
    intro ε hε
    have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hbeta : 0 < Real.pi / (2 * Real.sqrt ε) := by positivity
    have h1 : (Real.pi / (2 * Real.sqrt ε)) ^ (-((n : ℝ) / 2)) =
        (2 / Real.pi) ^ ((n : ℝ) / 2) * (Real.sqrt ε) ^ ((n : ℝ) / 2) := by
      rw [Real.rpow_neg hbeta.le, ← Real.inv_rpow hbeta.le]
      rw [show (Real.pi / (2 * Real.sqrt ε))⁻¹ = (2 / Real.pi) * Real.sqrt ε from by
        field_simp]
      exact Real.mul_rpow (by positivity) hsq.le
    have h2 : (Real.sqrt ε)⁻¹ * (Real.sqrt ε) ^ ((n : ℝ) / 2) =
        (Real.sqrt ε) ^ ((n : ℝ) / 2 - 1) := by
      rw [← Real.rpow_neg_one (Real.sqrt ε), ← Real.rpow_add hsq]
      congr 1
      ring
    rw [h1, ← h2]
    ring
  have hsqrtlim : Tendsto (fun k : ℕ => Real.sqrt (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h
    simpa [Function.comp_def] using h2
  have hpow : Tendsto (fun x : ℝ => x ^ ((n : ℝ) / 2 - 1)) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ ((n : ℝ) / 2 - 1)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr ha.le)
    have hzero : (0 : ℝ) ^ ((n : ℝ) / 2 - 1) = 0 := Real.zero_rpow ha.ne'
    have := hcont.tendsto
    rwa [hzero] at this
  have hlim : Tendsto (fun k : ℕ =>
      (Real.exp (Real.pi / 4) * Real.Gamma ((n : ℝ) / 2) *
        (2 / Real.pi) ^ ((n : ℝ) / 2)) *
        (Real.sqrt (1 / ((k : ℝ) + 1))) ^ ((n : ℝ) / 2 - 1)) atTop (𝓝 0) := by
    have h := (hpow.comp hsqrtlim).const_mul
      (Real.exp (Real.pi / 4) * Real.Gamma ((n : ℝ) / 2) * (2 / Real.pi) ^ ((n : ℝ) / 2))
    simpa [Function.comp_def] using h
  refine hlim.congr fun k => ?_
  exact (hrw (1 / ((k : ℝ) + 1)) (by positivity)).symm

set_option maxHeartbeats 1000000 in
/-- The zero-parameter archimedean local integral vanishes for rank at least three. -/
theorem integral_archimedeanBruhatFactor_zero_eq_zero (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((0 : ℝ) : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) = 0 := by
  have hn0 : 0 < n := by omega
  have hlim := L.tendsto_integral_regularizedArchimedean (c := c) (t := (0 : ℝ)) hc hn
  have hzero : Tendsto (fun k : ℕ => ∫ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * ((0 : ℝ) : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ =>
        |(L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n| *
          (Real.exp (Real.pi / 4) * (Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ *
            ((Real.pi / (2 * Real.sqrt (1 / ((k : ℝ) + 1)))) ^ (-((n : ℝ) / 2)) *
              Real.Gamma ((n : ℝ) / 2)))) atTop (𝓝 0) := by
      have h := (tendsto_zeroFrequencyBound (n := n) hn).const_mul
        |(L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n|
      rwa [mul_zero] at h
    refine squeeze_zero_norm (fun k => ?_) hg
    have hεk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [L.integral_regularized_eq_valueIntegral hn0 hc hεk, Complex.real_smul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (abs_zeroFrequency_valueIntegral_le hn hc hεk) (abs_nonneg _)
  exact tendsto_nhds_unique hlim hzero

/-- The adelic archimedean local integral at the zero frequency vanishes. -/
theorem integral_archimedeanLocal_zero_eq_zero (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) :
    (∫ w : RationalInfiniteAdele,
        ((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele (-(0 : ℚ)) * w) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) -
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)
        ∂rationalInfiniteAdeleAddHaarMeasure) = 0 := by
  rw [integral_archimedeanLocal_eq_real L c (-(0 : ℚ))]
  have hcast : (((-(0 : ℚ)) : ℚ) : ℝ) = (0 : ℝ) := by norm_num
  rw [hcast]
  exact L.integral_archimedeanBruhatFactor_zero_eq_zero hc hn

end PositiveDefiniteIntegralLattice
