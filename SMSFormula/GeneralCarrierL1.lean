import SMSFormula.CosetCarrierL1

/-!
# The finite half of `G_b subset L` at every carrier scale

The previous file closed the finite half for carriers inside the integral vectors.  A general finite
Schwartz--Bruhat test is carried only at some scale `c` -- it lives in `c^(-1) Zhat^n` -- and the
repository's own `standardScalePullback` normalises that scale to one.  This file transports the
estimate along that pullback, which closes the finite half for every carrier scale.

The transport moves the frequency, and that is the whole difficulty.  Scaling the variable by
`1/c` divides the quadratic value by `c^2`, so the pullback's finite factor is evaluated at `t/c^2`,
not at `t`.  A change of variables in the frequency would need `lintegral_map` and hence
measurability of the parameter integral, which this chain has never had to prove.

SO the bound is transported, not the integral, and it costs nothing.  If `t` has exact conductor `m`
and `t/c^2` clears `M`, then `t = (t/c^2) c^2` clears `M` as well, so `m` divides `M` and in
particular `m <= M`.  The pullback's bound at `M` is therefore already a bound at `m`: the decay
`(M^n)^(-1/2)` is at least as strong as `(m^n)^(-1/2)`.  Hence the general-carrier finite factor
satisfies the same per-stratum bound up to the factor `c^n` the change of variables produces, and
the conductor partition -- extracted in the previous file -- runs on it unchanged.

Negative scope.  Nothing is uniform in the carrier scale: the constant carries `c^n` and the level
becomes `c * d`, so the constant of the previous file is itself evaluated at a larger level.  The
estimate stays an upper bound, the integral model stays a hypothesis, and no archimedean factor is
bounded -- for a general finite Schwartz--Bruhat carrier the two halves still have to be multiplied,
which the block/height route does not do outside the standard test.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory Matrix RationalQuadraticSpaceMatrix
open scoped ENNReal

variable {n : ℕ}

/-! ## Scaling the variable scales the form by the square -/

/-- Scaling the variable scales the form by the square, which is why the frequency moves. -/
theorem dotQuadratic_coordScale (q : ℚ) (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (x : Fin n → RationalFiniteAdele) :
    dotQuadratic C (rationalFiniteAdeleCoordinateScale q x) =
      (algebraMap ℚ RationalFiniteAdele q) ^ 2 * dotQuadratic C x := by
  set a : RationalFiniteAdele := algebraMap ℚ RationalFiniteAdele q with ha
  have hinner : ∀ i : Fin n, (∑ j, C i j * (a * x j)) = a * ∑ j, C i j * x j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  show ∑ i, (a * x i) * (∑ j, C i j * (a * x j)) =
    a ^ 2 * ∑ i, x i * ∑ j, C i j * x j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hinner i]
  ring

/-! ## The change of variables -/

/-- The change of variables: the finite factor of a test at frequency `t` is `c^n` times the finite
factor of its scale pullback at the frequency `t / c^2`.  The `c^n` is the existing finite Haar
scaling and the `c^(-2)` is the square law above. -/
theorem integral_scalePullback_phase (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (t : RationalFiniteAdele) {c : ℕ} (hc : c ≠ 0)
    (g : (Fin n → RationalFiniteAdele) → ℂ) :
    (∫ x, g x * complexFiniteChar (t * dotQuadratic C x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) =
      ((c : ℂ)) ^ n *
        ∫ x, standardScalePullback c g x *
          complexFiniteChar
            ((t * (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2) * dotQuadratic C x)
          ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hq : ((c : ℚ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hc)
  have hcC : ((c : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hkey := integral_rationalFiniteAdeleCoordinateScale_inv n hc hq
    (fun x ↦ g x * complexFiniteChar (t * dotQuadratic C x))
  have hpt : ∀ x : Fin n → RationalFiniteAdele,
      g (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x) *
          complexFiniteChar
            (t * dotQuadratic C (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x)) =
        standardScalePullback c g x *
          complexFiniteChar
            ((t * (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2) * dotQuadratic C x) := by
    intro x
    rw [dotQuadratic_coordScale]
    show _ = _
    rw [show t * ((algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2 * dotQuadratic C x) =
      (t * (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2) * dotQuadratic C x from by ring]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hkey
  rw [hkey, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hcC, one_pow, one_mul]

/-! ## The conductor only grows -/

/-- The conductor only grows under the scaling: whatever `t / c^2` clears, `t` clears too, since
`t = (t / c^2) c^2`.  So the exact conductor of `t` divides every conductor the scaled frequency
clears. -/
theorem hasExactConductor_dvd_of_scale {t : RationalFiniteAdele} {m M c : ℕ}
    (hm : m ≠ 0) (hc : c ≠ 0) (hex : HasExactConductor t m)
    (hMclear : (t * (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2) *
        (M : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    (m : ℤ) ∣ (M : ℤ) := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hcancel : (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2 *
      ((c : RationalFiniteAdele)) ^ 2 = 1 := by
    have hcast : (c : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((c : ℚ)) := by
      norm_num
    rw [hcast, ← mul_pow, ← map_mul, inv_mul_cancel₀ hq, map_one, one_pow]
  have hrewrite : t * (M : RationalFiniteAdele) =
      ((t * (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2) * (M : RationalFiniteAdele)) *
        ((c : RationalFiniteAdele)) ^ 2 := by
    calc t * (M : RationalFiniteAdele)
        = t * 1 * (M : RationalFiniteAdele) := by ring
      _ = t * ((algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2 *
            ((c : RationalFiniteAdele)) ^ 2) * (M : RationalFiniteAdele) := by rw [hcancel]
      _ = _ := by ring
  refine dvd_of_hasExactConductor hm hex ?_
  rw [hrewrite]
  exact Subring.mul_mem _ hMclear (Subring.pow_mem _ (natCast_mem _ c) 2)

/-! ## The payoff -/

/-- The finite half of `G_b subset L` at every carrier scale: for every finite test standard-carried
at any nonzero scale `c` and standard-periodic at any nonzero level `d`, the Bruhat coefficient's
finite factor is integrable over the finite adeles above rank four.

The bound is transported, not the integral: the exact conductor of `t` divides every conductor the
scaled frequency clears, so the pullback's bound at that conductor is already a bound at `t`'s. -/
theorem lintegral_norm_finiteFactor_generalCarrier_lt_top (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0) {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) :
    ∫⁻ t, ENNReal.ofReal
        ‖∫ x, g x * complexFiniteChar
            (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
          ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖
        ∂rationalFiniteAdeleAddHaarMeasure < ⊤ := by
  haveI : NeZero (c * d) := ⟨Nat.mul_ne_zero hc hd⟩
  set r : ℕ := c * d with hrdef
  set gp := standardScalePullback c g with hgp
  have hgpc : IsStandardCarried 1 gp := hcarried.scalePullback hc
  have hgpp : IsStandardPeriodic r gp := hperiodic.scalePullback hc
  set Kp : ℝ := (∑ alpha, ‖standardFamilyQuotientLift gp hgpp alpha‖) * ((r : ℝ))⁻¹ ^ n with hKp
  have hKpnonneg : (0 : ℝ) ≤ Kp := by
    have : (0 : ℝ) ≤ ∑ alpha, ‖standardFamilyQuotientLift gp hgpp alpha‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    rw [hKp]
    positivity
  have hKnonneg : (0 : ℝ) ≤ ((c : ℝ)) ^ n * Kp := by positivity
  refine lintegral_lt_top_of_conductor_bound hn (r ^ (2 * n) * L.polarDeterminant.natAbs) hKnonneg _ ?_
  intro m _ t htm hex
  have hm : m ≠ 0 := NeZero.ne m
  set s : RationalFiniteAdele := t * (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹) ^ 2 with hs
  obtain ⟨M, hM0, hMclear, hMex⟩ := exists_hasExactConductor s
  haveI : NeZero M := ⟨hM0⟩
  have hdvd : (m : ℤ) ∣ (M : ℤ) := hasExactConductor_dvd_of_scale hm hc hex (by rw [← hs]; exact hMclear)
  have hle : m ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) (by exact_mod_cast hdvd)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmono : Real.sqrt ((((M : ℝ)) ^ n)⁻¹ *
        (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) ≤
      Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
        (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) := by
    have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hle
    gcongr
  have hbound := norm_finiteFactor_le L hgpc hgpp M hMclear hMex
  rw [integral_scalePullback_phase (integralModelMatrix L.pairingMatrix) t hc g, norm_mul,
    norm_pow, Complex.norm_natCast]
  calc ((c : ℝ)) ^ n *
        ‖∫ x, gp x * complexFiniteChar (s * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
          ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖
      ≤ ((c : ℝ)) ^ n * (Kp * Real.sqrt ((((M : ℝ)) ^ n)⁻¹ *
          (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n)) := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ ((c : ℝ)) ^ n * (Kp * Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
          (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmono hKpnonneg) (by positivity)
    _ = ((c : ℝ)) ^ n * Kp * Real.sqrt ((((m : ℝ)) ^ n)⁻¹ *
          (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) := by ring

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
