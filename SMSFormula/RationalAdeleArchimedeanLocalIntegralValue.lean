import SMSFormula.RationalAdeleArchimedeanRadialValue

/-!
# The archimedean local integral at a negative parameter is the classical local density

The archimedean amplitude is already known to be a Gaussian integral in the nonnegative
polar value, and that integral is already reduced to a one-dimensional integral in the
value variable with the explicit constant `pi^(n/2)/Gamma(n/2)`.  This file takes the
regulator width to zero at a negative parameter, where the Gaussian regulator becomes a
peak at the positive value `-2t` instead of dying.

The limit is computed with mathlib's existing peak-function theorem, so nothing new about
approximate identities has to be developed.

Negative scope: only the archimedean factor at a negative parameter is evaluated.  The
finite local integral is untouched, no Euler product is asserted, and no shell comparison
is made.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The Gaussian peak profile -/

theorem integral_gaussianProfile : (∫ v : ℝ, Real.exp (-Real.pi * v ^ 2)) = 1 := by
  rw [integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]

theorem tendsto_gaussianProfile_atTop :
    Tendsto (fun r : ℝ => r * Real.exp (-Real.pi * r ^ 2)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-Real.pi * r)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 Real.pi Real.pi_pos
  refine squeeze_zero' ?_ ?_ (by simpa using hmaj)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr2 : r ≤ r ^ 2 := by nlinarith
    have hle : -Real.pi * r ^ 2 ≤ -Real.pi * r := by nlinarith [Real.pi_pos]
    have hexp := Real.exp_le_exp.mpr hle
    have hr0 : (0 : ℝ) ≤ r := by linarith
    simpa using mul_le_mul_of_nonneg_left hexp hr0

theorem tendsto_gaussianProfile_cobounded :
    Tendsto (fun v : ℝ => ‖v‖ ^ (Module.finrank ℝ ℝ) * Real.exp (-Real.pi * v ^ 2))
      (Bornology.cobounded ℝ) (𝓝 0) := by
  have hnorm : Tendsto (fun v : ℝ => ‖v‖) (Bornology.cobounded ℝ) atTop :=
    tendsto_norm_cobounded_atTop
  have h := tendsto_gaussianProfile_atTop.comp hnorm
  refine h.congr fun v => ?_
  simp only [Function.comp_apply, Module.finrank_self, pow_one]
  congr 2
  rw [Real.norm_eq_abs, sq_abs]

/-! ## The value profile -/

theorem integrableOn_valueProfile (hn : 0 < n) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u)) (Ioi (0 : ℝ)) := by
  have hs : (0 : ℝ) < (n : ℝ) / 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hG := Real.GammaIntegral_convergent hs
  have h2 : IntegrableOn
      (fun u : ℝ => Real.exp (-(b * u)) * (b * u) ^ ((n : ℝ) / 2 - 1)) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((n : ℝ) / 2 - 1)) 0 hb).mpr (by simpa using hG)
    exact h
  have h3 : IntegrableOn
      (fun u : ℝ => b ^ (-((n : ℝ) / 2 - 1)) *
        (Real.exp (-(b * u)) * (b * u) ^ ((n : ℝ) / 2 - 1))) (Ioi (0 : ℝ)) :=
    h2.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun h3 ?_ measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hbpow : b ^ (-((n : ℝ) / 2 - 1)) * b ^ ((n : ℝ) / 2 - 1) = 1 := by
    rw [← Real.rpow_add hb]
    simp
  calc b ^ (-((n : ℝ) / 2 - 1)) * (Real.exp (-(b * u)) * (b * u) ^ ((n : ℝ) / 2 - 1))
      = (b ^ (-((n : ℝ) / 2 - 1)) * b ^ ((n : ℝ) / 2 - 1)) *
          (u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(b * u))) := by
        rw [Real.mul_rpow hb.le hu0.le]
        ring
    _ = u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u) := by
        rw [hbpow, one_mul, neg_mul]

theorem integrable_valueProfileIndicator (hn : 0 < n) {b : ℝ} (hb : 0 < b) :
    Integrable (Set.indicator (Ioi (0 : ℝ))
      (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u))) (volume : Measure ℝ) :=
  (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_valueProfile hn hb)

theorem continuousAt_valueProfileIndicator {b x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (Set.indicator (Ioi (0 : ℝ))
      (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u))) x₀ := by
  have hcont : ContinuousAt (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u)) x₀ := by
    refine ContinuousAt.mul ?_ (by fun_prop)
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hx₀.ne')).comp continuousAt_id
  refine hcont.congr ?_
  filter_upwards [Ioi_mem_nhds hx₀] with u hu
  rw [Set.indicator_of_mem hu]

set_option maxHeartbeats 1000000 in
/-- The peak limit: at a negative parameter the regulator concentrates at the positive
value `-2t`, and mathlib's existing peak-function theorem evaluates the limit. -/
theorem tendsto_valueIntegral_peak (hn : 0 < n) {b t : ℝ} (hb : 0 < b) (ht : t < 0) :
    Tendsto (fun w : ℝ => ∫ u in Ioi (0 : ℝ),
        u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u) *
          (2 * w * Real.exp (-Real.pi * (w * (-2 * t - u)) ^ 2)))
      atTop (𝓝 (2 * ((-2 * t) ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * (-2 * t))))) := by
  have hx₀ : (0 : ℝ) < -2 * t := by linarith
  have hHint := integrable_valueProfileIndicator (n := n) hn hb
  have hHcont := continuousAt_valueProfileIndicator (n := n) (b := b) (x₀ := -2 * t) hx₀
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable'
    (φ := fun v : ℝ => Real.exp (-Real.pi * v ^ 2))
    (fun v => (Real.exp_pos _).le) integral_gaussianProfile
    tendsto_gaussianProfile_cobounded hHint hHcont
  have hval : Set.indicator (Ioi (0 : ℝ))
      (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u)) (-2 * t) =
      (-2 * t) ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * (-2 * t)) :=
    Set.indicator_of_mem (by exact hx₀) _
  rw [hval] at hpeak
  have hEq : ∀ w : ℝ, (∫ u in Ioi (0 : ℝ),
      u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u) *
        (2 * w * Real.exp (-Real.pi * (w * (-2 * t - u)) ^ 2))) =
      2 * ∫ u : ℝ, (w ^ (Module.finrank ℝ ℝ) *
        Real.exp (-Real.pi * (w • (-2 * t - u)) ^ 2)) •
        Set.indicator (Ioi (0 : ℝ))
          (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u)) u := by
    intro w
    have hpt : ∀ u : ℝ, (w ^ (Module.finrank ℝ ℝ) *
        Real.exp (-Real.pi * (w • (-2 * t - u)) ^ 2)) •
        Set.indicator (Ioi (0 : ℝ))
          (fun u : ℝ => u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u)) u =
        Set.indicator (Ioi (0 : ℝ))
          (fun u : ℝ => (w * Real.exp (-Real.pi * (w * (-2 * t - u)) ^ 2)) *
            (u ^ ((n : ℝ) / 2 - 1) * Real.exp (-b * u))) u := by
      intro u
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        simp [Module.finrank_self, smul_eq_mul]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, smul_zero]
    simp_rw [hpt]
    rw [integral_indicator measurableSet_Ioi, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  simp_rw [hEq]
  have h2 := hpeak.const_mul (2 : ℝ)
  exact h2

set_option maxHeartbeats 1000000 in
/-- The Gaussian-regularized archimedean integral, written in the value variable and in the
exact shape of the peak limit. -/
theorem integral_regularized_eq_valueIntegral (L : PositiveDefiniteIntegralLattice n) (hn0 : 0 < n)
    {c ε t : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * (ε : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) : ℝ) •
        (((∫ u in Ioi (0 : ℝ), u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
            (2 * (2 * Real.sqrt ε)⁻¹ *
              Real.exp (-Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * t - u)) ^ 2))) : ℝ) : ℂ) := by
  have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  have hspos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hGcont : Continuous fun u : ℝ =>
      Complex.exp (-Real.pi * (c : ℂ) * (u : ℂ)) *
        ((((Real.sqrt ε)⁻¹ : ℝ) : ℂ) *
          Complex.exp (((-Real.pi * (t + u / 2) ^ 2 / ε : ℝ) : ℂ))) := by
    fun_prop
  have hpt : ∀ x : Fin n → ℝ,
      polarRealGaussian L (c : ℂ) x *
          ((((Real.sqrt ε)⁻¹ : ℝ) : ℂ) *
            Complex.exp
              (((-Real.pi * (t + L.polarRealValue x / 2) ^ 2 / ε : ℝ) : ℂ))) =
        Complex.exp (-Real.pi * (c : ℂ) * ((L.polarRealValue x : ℝ) : ℂ)) *
          ((((Real.sqrt ε)⁻¹ : ℝ) : ℂ) *
            Complex.exp
              (((-Real.pi * (t + L.polarRealValue x / 2) ^ 2 / ε : ℝ) : ℂ))) := fun x => by
    rw [polarRealGaussian_eq_exp_polarRealValue]
  rw [L.integral_regularizedArchimedean_eq hc hε t,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    L.integral_comp_polarRealValue_value hn0 hGcont]
  congr 1
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  have harg : -Real.pi * (t + u / 2) ^ 2 / ε =
      -Real.pi * ((2 * Real.sqrt ε)⁻¹ * (-2 * t - u)) ^ 2 := by
    field_simp
    nlinarith [hsq, hspos]
  have hpref : ((Real.sqrt ε)⁻¹ : ℝ) = 2 * (2 * Real.sqrt ε)⁻¹ := by
    field_simp
  rw [Complex.real_smul, harg, hpref]
  push_cast
  rw [show (-(Real.pi : ℂ) * (c : ℂ) * (u : ℂ)) =
      (-((Real.pi : ℂ) * (c : ℂ)) * (u : ℂ)) by ring]
  ring

theorem tendsto_regulatorScale :
    Tendsto (fun k : ℕ => (2 * Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹) atTop atTop := by
  have h2 : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1)) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (b ^ 2)
    refine ⟨N, fun k hk => ?_⟩
    have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hle : b ^ 2 ≤ (k : ℝ) + 1 := by linarith
    calc b ≤ Real.sqrt (b ^ 2) := by
          rcases le_or_gt 0 b with hb | hb
          · rw [Real.sqrt_sq hb]
          · exact le_trans hb.le (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt hle
  have h3 : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1) / 2) atTop atTop :=
    h2.atTop_div_const (by norm_num)
  refine h3.congr fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [one_div, Real.sqrt_inv]
  have hs : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr hk
  field_simp

set_option maxHeartbeats 1000000 in
/-- The archimedean local density: at every negative parameter the archimedean local
integral equals the classical value, in the raw form produced by the peak limit. -/
theorem integral_archimedeanBruhatFactor_eq_value_raw (L : PositiveDefiniteIntegralLattice n) {c t : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) (ht : t < 0) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) =
      ((((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) *
        (2 * ((-2 * t) ^ ((n : ℝ) / 2 - 1) *
          Real.exp (-(Real.pi * c) * (-2 * t)))) : ℝ) : ℂ) := by
  have hn0 : 0 < n := by omega
  have hlim := L.tendsto_integral_regularizedArchimedean (c := c) (t := t) hc hn
  have hrw : ∀ k : ℕ, (∫ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) : ℝ) •
        (((∫ u in Ioi (0 : ℝ), u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
            (2 * (2 * Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ *
              Real.exp (-Real.pi *
                ((2 * Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ * (-2 * t - u)) ^ 2))) : ℝ) : ℂ) :=
    fun k => L.integral_regularized_eq_valueIntegral hn0 hc (by positivity)
  have hK := (tendsto_valueIntegral_peak (n := n) hn0 (b := Real.pi * c)
    (by positivity) ht).comp tendsto_regulatorScale
  have hcast : Tendsto (fun k : ℕ =>
      (((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) : ℝ) •
        (((∫ u in Ioi (0 : ℝ), u ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * u) *
            (2 * (2 * Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ *
              Real.exp (-Real.pi *
                ((2 * Real.sqrt (1 / ((k : ℝ) + 1)))⁻¹ * (-2 * t - u)) ^ 2))) : ℝ) : ℂ))
      atTop
      (𝓝 ((((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) : ℝ) •
        (((2 * ((-2 * t) ^ ((n : ℝ) / 2 - 1) *
          Real.exp (-(Real.pi * c) * (-2 * t)))) : ℝ) : ℂ))) := by
    have hc1 := (Complex.continuous_ofReal.tendsto
      (2 * ((-2 * t) ^ ((n : ℝ) / 2 - 1) * Real.exp (-(Real.pi * c) * (-2 * t))))).comp hK
    exact hc1.const_smul _
  have hfinal : Tendsto (fun k : ℕ => ∫ v : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-Real.pi * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (v : ℂ) ^ 2) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) atTop
      (𝓝 ((((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) : ℝ) •
        (((2 * ((-2 * t) ^ ((n : ℝ) / 2 - 1) *
          Real.exp (-(Real.pi * c) * (-2 * t)))) : ℝ) : ℂ))) := by
    refine hcast.congr fun k => (hrw k).symm
  rw [tendsto_nhds_unique hlim hfinal, Complex.real_smul, ← Complex.ofReal_mul]

set_option maxHeartbeats 1000000 in
/-- The classical archimedean local density, in closed form:
`detScale^{-1} (2 pi)^{n/2} / Gamma(n/2) * (-t)^{n/2 - 1} * exp(-2 pi c (-t))`. -/
theorem integral_archimedeanBruhatFactor_eq_value (L : PositiveDefiniteIntegralLattice n) {c t : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) (ht : t < 0) :
    (∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n)) =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ *
        ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        (-t) ^ ((n : ℝ) / 2 - 1) *
        Real.exp (-(2 * Real.pi * c) * (-t)) : ℝ) : ℂ) := by
  have hn0 : 0 < n := by omega
  have hΓ : Real.Gamma ((n : ℝ) / 2) ≠ 0 := by
    refine ne_of_gt (Real.Gamma_pos_of_pos ?_)
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    linarith
  have h2 : (2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2 - 1) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hmul : (2 : ℝ) ^ ((n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) =
      (2 * Real.pi) ^ ((n : ℝ) / 2) :=
    (Real.mul_rpow (by norm_num) Real.pi_pos.le).symm
  have hsplit : (-2 * t : ℝ) ^ ((n : ℝ) / 2 - 1) =
      (2 : ℝ) ^ ((n : ℝ) / 2 - 1) * (-t) ^ ((n : ℝ) / 2 - 1) := by
    rw [show (-2 * t : ℝ) = 2 * (-t) by ring,
      Real.mul_rpow (by norm_num) (by linarith)]
  have hexp : Real.exp (-(Real.pi * c) * (-2 * t)) =
      Real.exp (-(2 * Real.pi * c) * (-t)) := by
    congr 1
    ring
  rw [integral_archimedeanBruhatFactor_eq_value_raw L hc hn ht,
    archimedeanValueConstant_eq L hn0]
  congr 1
  rw [hsplit, hexp, ← hmul, ← h2]
  field_simp

/-- The archimedean local integral at a positive rational frequency is the classical
archimedean local density. -/
theorem integral_archimedeanLocal_eq_density (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) {b : ℚ} (hb : 0 < b) :
    (∫ w : RationalInfiniteAdele,
        ((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele (-b) * w) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) -
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)
        ∂rationalInfiniteAdeleAddHaarMeasure) =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ *
        ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        (b : ℝ) ^ ((n : ℝ) / 2 - 1) *
        Real.exp (-(2 * Real.pi * c) * (b : ℝ)) : ℝ) : ℂ) := by
  have ht : (((-b : ℚ) : ℝ)) < 0 := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    push_cast
    linarith
  have hneg : (-(((-b : ℚ) : ℝ))) = (b : ℝ) := by push_cast; ring
  rw [integral_archimedeanLocal_eq_real, L.integral_archimedeanBruhatFactor_eq_value hc hn ht,
    hneg]

end PositiveDefiniteIntegralLattice
