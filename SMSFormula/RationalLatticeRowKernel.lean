import SMSFormula.RationalLatticeBoundaryAnomalyVector
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# The row kernel `h_{s,y}` and its exact zero mode

For `y > 0` and real `s`, the row kernel is

`h_{s,y}(t) = (t + iy)⁻² (t² + y²)^{-s}`   (`rowKernel`),

so that a regularized row term is `(Im γz)^s (cz+d)⁻² = y^s c^{-2-2s} h_{s,y}(x + d/c)`.

* `norm_rowKernel_le`: for `0 ≤ s ≤ 1`, `|h_{s,y}(t)| ≤ (1 + y⁻²)(t² + y²)⁻¹`, uniformly in `s`; hence `h_{s,y}` is
  continuous and integrable.
* The exact zero mode (5.4) `integral_rowKernel`: for `s > 0`,
  `∫ h_{s,y} = -κ(s) y^{-1-2s}` with the `κ(s) = s/(1+s) ∫ (1+u²)^{-1-s}` (`zeroModeKappa`).
  After `t = yu`, the integrand is
  `-(1/(1+s)) F' + (i/(1+s)) G' - (s/(1+s)) (1+u²)^{-1-s}` with `F = u(1+u²)^{-1-s}`, `G = (1+u²)^{-1-s}`,
  and `∫ F' = ∫ G' = 0` (`integral_of_hasDerivAt_of_tendsto`).  No contour and no Gamma function.
Nothing is chosen.
-/

noncomputable section

open Complex MeasureTheory Filter Topology

namespace SMSFormula.RowKernel

/-- The row kernel `h_{s,y}(t) = (t + iy)⁻² (t² + y²)^{-s}`. -/
def rowKernel (s y t : ℝ) : ℂ :=
  (((t : ℂ) + y * I) ^ 2)⁻¹ * (((t ^ 2 + y ^ 2) ^ (-s) : ℝ) : ℂ)

/-! ## Elementary bounds -/

theorem sq_add_sq_pos {y : ℝ} (hy : 0 < y) (t : ℝ) : 0 < t ^ 2 + y ^ 2 := by positivity

theorem add_mul_I_ne_zero {y : ℝ} (hy : 0 < y) (t : ℝ) : (t : ℂ) + y * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy.ne' this

theorem norm_add_mul_I_sq (t y : ℝ) : ‖(t : ℂ) + y * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
  rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]

/-- `a^s ≤ 1 + a` for `a ≥ 0` and `0 ≤ s ≤ 1`. -/
theorem rpow_le_one_add {a s : ℝ} (ha : 0 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : a ^ s ≤ 1 + a := by
  rcases le_total a 1 with h | h
  · have := Real.rpow_le_one ha h hs0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    linarith

/-- The uniform bound `(t² + y²)^{-s} ≤ 1 + y⁻²` for `0 ≤ s ≤ 1`. -/
theorem sq_add_sq_rpow_neg_le {y : ℝ} (hy : 0 < y) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    (t ^ 2 + y ^ 2) ^ (-s) ≤ 1 + (y ^ 2)⁻¹ := by
  have h1 : (t ^ 2 + y ^ 2) ^ (-s) ≤ (y ^ 2) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg t]) (by linarith)
  refine h1.trans ?_
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  exact rpow_le_one_add (by positivity) hs0 hs1

theorem norm_rowKernel (s : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖rowKernel s y t‖ = (t ^ 2 + y ^ 2) ^ (-s) * (t ^ 2 + y ^ 2)⁻¹ := by
  unfold rowKernel
  rw [norm_mul, norm_inv, norm_pow, norm_add_mul_I_sq, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (sq_add_sq_pos hy t).le _), mul_comm]

/-- The uniform majorant: `|h_{s,y}(t)| ≤ (1 + y⁻²)(t² + y²)⁻¹` for `0 ≤ s ≤ 1`. -/
theorem norm_rowKernel_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖rowKernel s y t‖ ≤ (1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_rowKernel s hy t]
  exact mul_le_mul_of_nonneg_right (sq_add_sq_rpow_neg_le hy hs0 hs1 t)
    (inv_nonneg.2 (sq_add_sq_pos hy t).le)

theorem integrable_inv_sq_add_sq {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ ↦ (t ^ 2 + y ^ 2)⁻¹ := by
  have h := (integrable_inv_one_add_sq.comp_div hy.ne').const_mul (y ^ 2)⁻¹
  refine h.congr (Eventually.of_forall fun t ↦ ?_)
  simp only
  field_simp
  ring

theorem continuous_rowKernel (s : ℝ) {y : ℝ} (hy : 0 < y) : Continuous (rowKernel s y) := by
  unfold rowKernel
  refine Continuous.mul ?_ ?_
  · refine Continuous.inv₀ (by fun_prop) fun t ↦ pow_ne_zero 2 (add_mul_I_ne_zero hy t)
  · exact continuous_ofReal.comp
      (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl (sq_add_sq_pos hy t).ne')

theorem integrable_rowKernel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) :
    Integrable (rowKernel s y) :=
  ((integrable_inv_sq_add_sq hy).const_mul (1 + (y ^ 2)⁻¹)).mono'
    (continuous_rowKernel s hy).aestronglyMeasurable
    (Eventually.of_forall (norm_rowKernel_le hs0 hs1 hy))

/-! ## The exact zero mode -/

/-- `F(u) = u (1+u²)^{-1-s}`. -/
def zeroModeF (s u : ℝ) : ℝ := u * (1 + u ^ 2) ^ (-(1 + s))

/-- `G(u) = (1+u²)^{-1-s}`. -/
def zeroModeG (s u : ℝ) : ℝ := (1 + u ^ 2) ^ (-(1 + s))

theorem one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := by positivity

theorem one_add_sq_rpow_sub_one (s u : ℝ) :
    (1 + u ^ 2) ^ (-(1 + s) - 1) = (1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹ := by
  rw [Real.rpow_sub_one (one_add_sq_pos u).ne', div_eq_mul_inv]

theorem hasDerivAt_zeroModeG (s u : ℝ) :
    HasDerivAt (zeroModeG s)
      (-(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹)) u := by
  have h1 : HasDerivAt (fun u : ℝ ↦ 1 + u ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_pow 2 u).const_add 1)
  have h2 := h1.rpow_const (p := -(1 + s)) (Or.inl (one_add_sq_pos u).ne')
  rw [one_add_sq_rpow_sub_one] at h2
  convert h2 using 1
  ring

theorem hasDerivAt_zeroModeF (s u : ℝ) :
    HasDerivAt (zeroModeF s)
      ((1 + u ^ 2) ^ (-(1 + s)) - 2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹)) u := by
  have h := (hasDerivAt_id u).mul (hasDerivAt_zeroModeG s u)
  exact h.congr_deriv (by simp only [id, zeroModeG]; ring)

/-- The pointwise decomposition of the rescaled kernel. -/
theorem rescaled_rowKernel_eq {s : ℝ} (hs : 0 ≤ s) (u : ℝ) :
    (((u : ℂ) + I) ^ 2)⁻¹ * (((1 + u ^ 2) ^ (-s) : ℝ) : ℂ) =
      -(1 / (1 + (s : ℂ))) * (((1 + u ^ 2) ^ (-(1 + s)) -
          2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ) +
        (I / (1 + (s : ℂ))) *
          ((-(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ) -
        ((s : ℂ) / (1 + (s : ℂ))) * (((1 + u ^ 2) ^ (-(1 + s)) : ℝ) : ℂ) := by
  have hρ : (0 : ℝ) < 1 + u ^ 2 := one_add_sq_pos u
  set P : ℝ := (1 + u ^ 2) ^ (-(1 + s)) with hP
  have hPs : (1 + u ^ 2) ^ (-s) = (1 + u ^ 2) * P := by
    rw [hP, show -s = 1 + -(1 + s) by ring, Real.rpow_add hρ, Real.rpow_one]
  rw [hPs]
  have hw1 : (u : ℂ) + I ≠ 0 := by simpa using add_mul_I_ne_zero one_pos u
  have hw : ((u : ℂ) + I) ^ 2 ≠ 0 := pow_ne_zero 2 hw1
  have hρC : (1 + (u : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hρ.ne'
  have hs1 : (1 + (s : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + s := by linarith
    exact_mod_cast this.ne'
  have hkey : ((u : ℂ) + I) ^ 2 * ((u : ℂ) ^ 2 - 1 - 2 * I * u) = (1 + (u : ℂ) ^ 2) ^ 2 := by
    linear_combination (-(3 * (u : ℂ) ^ 2 + 1 + 2 * (u : ℂ) * I)) * I_sq
  have hinv : (((u : ℂ) + I) ^ 2)⁻¹ = ((u : ℂ) ^ 2 - 1 - 2 * I * u) / (1 + (u : ℂ) ^ 2) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hρC), ← hkey]
    field_simp
  rw [hinv]
  push_cast
  field_simp
  ring

/-- `(1+u²)^{-1-s} ≤ (1+u²)⁻¹` for `s ≥ 0`. -/
theorem one_add_sq_rpow_le_inv' {s : ℝ} (hs : 0 ≤ s) (u : ℝ) :
    (1 + u ^ 2) ^ (-(1 + s)) ≤ (1 + u ^ 2)⁻¹ :=
  PositiveDefiniteIntegralLattice.one_add_sq_rpow_le_inv hs u

theorem abs_mul_inv_one_add_sq_le (u : ℝ) : |u| * (1 + u ^ 2)⁻¹ ≤ 1 := by
  rw [mul_inv_le_iff₀ (one_add_sq_pos u)]
  nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]

theorem sq_mul_inv_one_add_sq_le (u : ℝ) : u ^ 2 * (1 + u ^ 2)⁻¹ ≤ 1 := by
  rw [mul_inv_le_iff₀ (one_add_sq_pos u)]
  linarith

theorem integrable_zeroModeF_deriv {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun u : ℝ ↦ (1 + u ^ 2) ^ (-(1 + s)) -
      2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) := by
  refine (integrable_inv_one_add_sq.const_mul (3 + 2 * s)).mono' ?_ (Eventually.of_forall fun u ↦ ?_)
  · exact Continuous.aestronglyMeasurable (by
      have hc : Continuous fun u : ℝ ↦ (1 + u ^ 2) ^ (-(1 + s)) :=
        Continuous.rpow_const (by fun_prop) fun u ↦ Or.inl (one_add_sq_pos u).ne'
      have hi : Continuous fun u : ℝ ↦ (1 + u ^ 2)⁻¹ :=
        Continuous.inv₀ (by fun_prop) fun u ↦ (one_add_sq_pos u).ne'
      fun_prop)
  · have hP := one_add_sq_rpow_le_inv' hs u
    have hP0 : 0 ≤ (1 + u ^ 2) ^ (-(1 + s)) := Real.rpow_nonneg (one_add_sq_pos u).le _
    have hq := sq_mul_inv_one_add_sq_le u
    have hq0 : 0 ≤ u ^ 2 * (1 + u ^ 2)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [mul_nonneg hP0 hq0, mul_le_mul_of_nonneg_left hq hP0]

theorem integrable_zeroModeG_deriv {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun u : ℝ ↦ -(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) := by
  refine (integrable_inv_one_add_sq.const_mul (2 * (1 + s))).mono' ?_ (Eventually.of_forall fun u ↦ ?_)
  · exact Continuous.aestronglyMeasurable (by
      have hc : Continuous fun u : ℝ ↦ (1 + u ^ 2) ^ (-(1 + s)) :=
        Continuous.rpow_const (by fun_prop) fun u ↦ Or.inl (one_add_sq_pos u).ne'
      have hi : Continuous fun u : ℝ ↦ (1 + u ^ 2)⁻¹ :=
        Continuous.inv₀ (by fun_prop) fun u ↦ (one_add_sq_pos u).ne'
      fun_prop)
  · have hP := one_add_sq_rpow_le_inv' hs u
    have hP0 : 0 ≤ (1 + u ^ 2) ^ (-(1 + s)) := Real.rpow_nonneg (one_add_sq_pos u).le _
    have ha := abs_mul_inv_one_add_sq_le u
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + s)),
      abs_of_nonneg (mul_nonneg hP0 (inv_nonneg.2 (one_add_sq_pos u).le))]
    calc 2 * (1 + s) * |u| * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹)
        = 2 * (1 + s) * (1 + u ^ 2) ^ (-(1 + s)) * (|u| * (1 + u ^ 2)⁻¹) := by ring
      _ ≤ 2 * (1 + s) * (1 + u ^ 2) ^ (-(1 + s)) * 1 :=
          mul_le_mul_of_nonneg_left ha (by positivity)
      _ ≤ 2 * (1 + s) * (1 + u ^ 2)⁻¹ := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hP (by linarith)

/-- `|F(u)| ≤ |u|⁻¹` and `|G(u)| ≤ |u|⁻²`, so both vanish at `±∞`. -/
theorem abs_zeroModeF_le {s : ℝ} (hs : 0 ≤ s) {u : ℝ} (hu : u ≠ 0) : ‖zeroModeF s u‖ ≤ ‖u⁻¹‖ := by
  have hP := one_add_sq_rpow_le_inv' hs u
  have hP0 : 0 ≤ (1 + u ^ 2) ^ (-(1 + s)) := Real.rpow_nonneg (one_add_sq_pos u).le _
  have hua : 0 < |u| := abs_pos.2 hu
  rw [zeroModeF, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0, abs_inv]
  calc |u| * (1 + u ^ 2) ^ (-(1 + s)) ≤ |u| * (1 + u ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hP hua.le
    _ ≤ |u|⁻¹ := by
        rw [mul_inv_le_iff₀ (one_add_sq_pos u), ← sq_abs u]
        field_simp
        nlinarith

theorem abs_zeroModeG_le {s : ℝ} (hs : 0 ≤ s) {u : ℝ} (hu : u ≠ 0) : ‖zeroModeG s u‖ ≤ ‖u⁻¹‖ ^ 2 := by
  have hP := one_add_sq_rpow_le_inv' hs u
  have hP0 : 0 ≤ (1 + u ^ 2) ^ (-(1 + s)) := Real.rpow_nonneg (one_add_sq_pos u).le _
  rw [zeroModeG, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hP0, abs_inv, inv_pow, sq_abs]
  refine hP.trans ?_
  exact inv_anti₀ (by positivity) (by linarith)

theorem tendsto_zeroModeF {s : ℝ} (hs : 0 ≤ s) {l : Filter ℝ}
    (hl : Tendsto (fun u : ℝ ↦ u⁻¹) l (𝓝 0)) (hne : ∀ᶠ u in l, u ≠ 0) :
    Tendsto (zeroModeF s) l (𝓝 0) :=
  squeeze_zero_norm' (hne.mono fun u hu ↦ abs_zeroModeF_le hs hu) (by simpa using hl.norm)

theorem tendsto_zeroModeG {s : ℝ} (hs : 0 ≤ s) {l : Filter ℝ}
    (hl : Tendsto (fun u : ℝ ↦ u⁻¹) l (𝓝 0)) (hne : ∀ᶠ u in l, u ≠ 0) :
    Tendsto (zeroModeG s) l (𝓝 0) :=
  squeeze_zero_norm' (hne.mono fun u hu ↦ abs_zeroModeG_le hs hu) (by simpa using (hl.norm.pow 2))

theorem integral_zeroModeF_deriv {s : ℝ} (hs : 0 ≤ s) :
    ∫ u : ℝ, ((1 + u ^ 2) ^ (-(1 + s)) -
      2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹)) = 0 := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_zeroModeF s) (integrable_zeroModeF_deriv hs)
    (tendsto_zeroModeF hs tendsto_inv_atBot_zero (eventually_ne_atBot 0))
    (tendsto_zeroModeF hs tendsto_inv_atTop_zero (eventually_ne_atTop 0))
  rw [h, sub_zero]

theorem integral_zeroModeG_deriv {s : ℝ} (hs : 0 ≤ s) :
    ∫ u : ℝ, (-(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹)) = 0 := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_zeroModeG s) (integrable_zeroModeG_deriv hs)
    (tendsto_zeroModeG hs tendsto_inv_atBot_zero (eventually_ne_atBot 0))
    (tendsto_zeroModeG hs tendsto_inv_atTop_zero (eventually_ne_atTop 0))
  rw [h, sub_zero]

/-- The rescaled zero mode: `∫ (u + i)⁻² (1 + u²)^{-s} du = -κ(s)`. -/
theorem integral_rescaled_rowKernel {s : ℝ} (hs : 0 ≤ s) :
    ∫ u : ℝ, (((u : ℂ) + I) ^ 2)⁻¹ * (((1 + u ^ 2) ^ (-s) : ℝ) : ℂ) =
      -((PositiveDefiniteIntegralLattice.zeroModeKappa s : ℝ) : ℂ) := by
  simp_rw [rescaled_rowKernel_eq hs]
  have h1 : Integrable (fun u : ℝ ↦ (((1 + u ^ 2) ^ (-(1 + s)) -
      2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ)) :=
    (integrable_zeroModeF_deriv hs).ofReal (𝕜 := ℂ)
  have h2 : Integrable (fun u : ℝ ↦
      ((-(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ)) :=
    (integrable_zeroModeG_deriv hs).ofReal (𝕜 := ℂ)
  have h3 : Integrable (fun u : ℝ ↦ (((1 + u ^ 2) ^ (-(1 + s)) : ℝ) : ℂ)) :=
    (PositiveDefiniteIntegralLattice.integrable_one_add_sq_rpow hs).ofReal (𝕜 := ℂ)
  have hA := h1.const_mul (-(1 / (1 + (s : ℂ))))
  have hB := h2.const_mul (I / (1 + (s : ℂ)))
  have hC := h3.const_mul ((s : ℂ) / (1 + (s : ℂ)))
  have hAB : Integrable (fun u : ℝ ↦ -(1 / (1 + (s : ℂ))) * (((1 + u ^ 2) ^ (-(1 + s)) -
      2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ) +
      I / (1 + (s : ℂ)) * ((-(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ)) :=
    hA.add hB
  refine (integral_sub hAB hC).trans ?_
  have eAB := integral_add hA hB
  have eA : ∫ u : ℝ, -(1 / (1 + (s : ℂ))) * (((1 + u ^ 2) ^ (-(1 + s)) -
      2 * (1 + s) * u ^ 2 * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ) = 0 := by
    rw [integral_const_mul, integral_complex_ofReal, integral_zeroModeF_deriv hs]; simp
  have eB : ∫ u : ℝ, I / (1 + (s : ℂ)) *
      ((-(2 * (1 + s)) * u * ((1 + u ^ 2) ^ (-(1 + s)) * (1 + u ^ 2)⁻¹) : ℝ) : ℂ) = 0 := by
    rw [integral_const_mul, integral_complex_ofReal, integral_zeroModeG_deriv hs]; simp
  have eC : ∫ u : ℝ, (s : ℂ) / (1 + (s : ℂ)) * (((1 + u ^ 2) ^ (-(1 + s)) : ℝ) : ℂ) =
      ((PositiveDefiniteIntegralLattice.zeroModeKappa s : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal, PositiveDefiniteIntegralLattice.zeroModeKappa]; push_cast; ring
  rw [eAB, eA, eB, eC]
  ring

theorem rowKernel_mul (s : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    rowKernel s y (y * u) = (((y ^ 2)⁻¹ * (y ^ 2) ^ (-s) : ℝ) : ℂ) *
      ((((u : ℂ) + I) ^ 2)⁻¹ * (((1 + u ^ 2) ^ (-s) : ℝ) : ℂ)) := by
  unfold rowKernel
  have hsq : (y * u) ^ 2 + y ^ 2 = y ^ 2 * (1 + u ^ 2) := by ring
  rw [hsq, Real.mul_rpow (by positivity) (by positivity)]
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hw : (u : ℂ) + I ≠ 0 := by simpa using add_mul_I_ne_zero one_pos u
  push_cast
  rw [show ((y : ℂ) * u + y * I) = y * (u + I) by ring, mul_pow]
  field_simp

/-- The exact zero mode (5.4): `∫ h_{s,y} = -κ(s) y^{-1-2s}`. -/
theorem integral_rowKernel {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, rowKernel s y t =
      -((PositiveDefiniteIntegralLattice.zeroModeKappa s : ℝ) : ℂ) * ((y ^ (-1 - 2 * s) : ℝ) : ℂ) := by
  have hscale := Measure.integral_comp_mul_left (rowKernel s y) y
  simp_rw [rowKernel_mul s hy] at hscale
  rw [integral_const_mul, integral_rescaled_rowKernel hs, abs_inv, abs_of_pos hy] at hscale
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hint : ∫ t : ℝ, rowKernel s y t = (y : ℂ) * ((((y ^ 2)⁻¹ * (y ^ 2) ^ (-s) : ℝ) : ℂ) *
      -((PositiveDefiniteIntegralLattice.zeroModeKappa s : ℝ) : ℂ)) := by
    rw [hscale, Complex.real_smul]
    push_cast
    field_simp
  rw [hint]
  have hpow : y ^ (-1 - 2 * s) = y⁻¹ * (y ^ 2) ^ (-s) := by
    rw [show -1 - 2 * s = -1 + (2 : ℕ) * (-s) by push_cast; ring, Real.rpow_add hy,
      Real.rpow_natCast_mul hy.le, Real.rpow_neg_one]
  rw [hpow]
  push_cast
  field_simp

/-! ## Two derivatives and the uniform Fourier decay -/

/-- `A(t) = (t + iy)⁻²` and its derivatives. -/
def kerA (y t : ℝ) : ℂ := (((t : ℂ) + y * I) ^ 2)⁻¹
def kerA1 (y t : ℝ) : ℂ := -2 * (((t : ℂ) + y * I) ^ 3)⁻¹
def kerA2 (y t : ℝ) : ℂ := 6 * (((t : ℂ) + y * I) ^ 4)⁻¹

/-- `B(t) = (t² + y²)^{-s}` and its derivatives (real). -/
def kerB (s y t : ℝ) : ℝ := (t ^ 2 + y ^ 2) ^ (-s)
def kerB1 (s y t : ℝ) : ℝ := -2 * s * t * ((t ^ 2 + y ^ 2) ^ (-s) * (t ^ 2 + y ^ 2)⁻¹)
def kerB2 (s y t : ℝ) : ℝ :=
  -2 * s * ((t ^ 2 + y ^ 2) ^ (-s) * (t ^ 2 + y ^ 2)⁻¹) +
    4 * s * (s + 1) * t ^ 2 * ((t ^ 2 + y ^ 2) ^ (-s) * (t ^ 2 + y ^ 2)⁻¹ * (t ^ 2 + y ^ 2)⁻¹)

/-- `h' = A'B + AB'`. -/
def rowKernel1 (s y t : ℝ) : ℂ := kerA1 y t * (kerB s y t : ℂ) + kerA y t * (kerB1 s y t : ℂ)

/-- `h'' = A''B + 2A'B' + AB''`. -/
def rowKernel2 (s y t : ℝ) : ℂ :=
  kerA2 y t * (kerB s y t : ℂ) + 2 * (kerA1 y t * (kerB1 s y t : ℂ)) + kerA y t * (kerB2 s y t : ℂ)

theorem hasDerivAt_add_mul_I (y t : ℝ) : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * I) 1 t := by
  simpa using ((hasDerivAt_id t).ofReal_comp).add_const ((y : ℂ) * I)

theorem hasDerivAt_kerA {y : ℝ} (hy : 0 < y) (t : ℝ) : HasDerivAt (kerA y) (kerA1 y t) t := by
  have hw := add_mul_I_ne_zero hy t
  have h2 : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + y * I) ^ 2) (2 * ((t : ℂ) + y * I) ^ 1 * 1) t :=
    (hasDerivAt_add_mul_I y t).pow 2
  have h := (hasDerivAt_inv (pow_ne_zero 2 hw)).comp t h2
  refine h.congr_deriv ?_
  unfold kerA1
  field_simp

theorem hasDerivAt_kerA1 {y : ℝ} (hy : 0 < y) (t : ℝ) : HasDerivAt (kerA1 y) (kerA2 y t) t := by
  have hw := add_mul_I_ne_zero hy t
  have h3 : HasDerivAt (fun t : ℝ ↦ ((t : ℂ) + y * I) ^ 3) (3 * ((t : ℂ) + y * I) ^ 2 * 1) t :=
    (hasDerivAt_add_mul_I y t).pow 3
  have h := ((hasDerivAt_inv (pow_ne_zero 3 hw)).comp t h3).const_mul (-2 : ℂ)
  refine h.congr_deriv ?_
  unfold kerA2
  field_simp
  ring

theorem hasDerivAt_sq_add_sq (y t : ℝ) : HasDerivAt (fun t : ℝ ↦ t ^ 2 + y ^ 2) (2 * t) t := by
  simpa using (hasDerivAt_pow 2 t).add_const (y ^ 2)

theorem hasDerivAt_kerB (s : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (kerB s y) (kerB1 s y t) t := by
  have hρ := sq_add_sq_pos hy t
  have h := (hasDerivAt_sq_add_sq y t).rpow_const (p := -s) (Or.inl hρ.ne')
  rw [Real.rpow_sub_one hρ.ne'] at h
  convert h using 1
  unfold kerB1
  rw [div_eq_mul_inv]
  ring

theorem hasDerivAt_kerB1 (s : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (kerB1 s y) (kerB2 s y t) t := by
  have hρ := sq_add_sq_pos hy t
  have hB := hasDerivAt_kerB s hy t
  have hinv : HasDerivAt (fun t : ℝ ↦ (t ^ 2 + y ^ 2)⁻¹) (-(2 * t) / (t ^ 2 + y ^ 2) ^ 2) t :=
    (hasDerivAt_sq_add_sq y t).inv hρ.ne'
  have h := ((hasDerivAt_id t).const_mul (-2 * s)).mul (hB.mul hinv)
  refine h.congr_deriv ?_
  unfold kerB2 kerB1 kerB
  simp only [id, Pi.mul_apply]
  field_simp
  ring

theorem hasDerivAt_rowKernel (s : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (rowKernel s y) (rowKernel1 s y t) t := by
  have h := (hasDerivAt_kerA hy t).mul ((hasDerivAt_kerB s hy t).ofReal_comp)
  refine h.congr_deriv ?_
  unfold rowKernel1; ring

theorem hasDerivAt_rowKernel1 (s : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (rowKernel1 s y) (rowKernel2 s y t) t := by
  have h := ((hasDerivAt_kerA1 hy t).mul ((hasDerivAt_kerB s hy t).ofReal_comp)).add
    ((hasDerivAt_kerA hy t).mul ((hasDerivAt_kerB1 s hy t).ofReal_comp))
  refine h.congr_deriv ?_
  unfold rowKernel2; ring

theorem deriv_rowKernel (s : ℝ) {y : ℝ} (hy : 0 < y) : deriv (rowKernel s y) = rowKernel1 s y :=
  funext fun t ↦ (hasDerivAt_rowKernel s hy t).deriv

theorem deriv_rowKernel1 (s : ℝ) {y : ℝ} (hy : 0 < y) : deriv (rowKernel1 s y) = rowKernel2 s y :=
  funext fun t ↦ (hasDerivAt_rowKernel1 s hy t).deriv

/-! ### Pointwise bounds, uniform in `0 ≤ s ≤ 1` -/

section Bounds

variable {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) (t : ℝ)
include hs0 hs1 hy

theorem kerBounds :
    let r := ‖(t : ℂ) + y * I‖
    ‖kerA y t‖ = (r ^ 2)⁻¹ ∧ ‖kerA1 y t‖ = 2 * (r ^ 3)⁻¹ ∧ ‖kerA2 y t‖ = 6 * (r ^ 4)⁻¹ ∧
      0 ≤ kerB s y t ∧ kerB s y t ≤ 1 + (y ^ 2)⁻¹ ∧
      |kerB1 s y t| ≤ 2 * (1 + (y ^ 2)⁻¹) * r⁻¹ ∧
      |kerB2 s y t| ≤ 10 * (1 + (y ^ 2)⁻¹) * (r ^ 2)⁻¹ := by
  intro r
  have hρ := sq_add_sq_pos hy t
  have hr2 : r ^ 2 = t ^ 2 + y ^ 2 := norm_add_mul_I_sq t y
  have hr0 : 0 < r := by
    have : 0 < r ^ 2 := by rw [hr2]; exact hρ
    exact lt_of_le_of_ne (norm_nonneg _) (fun h ↦ by rw [← h] at this; simp at this)
  have ht : |t| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hr0.le, hr2]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have ht2 : t ^ 2 ≤ r ^ 2 := by rw [hr2]; nlinarith [sq_nonneg y]
  set Cy := 1 + (y ^ 2)⁻¹ with hCy
  have hβ0 : 0 ≤ kerB s y t := Real.rpow_nonneg hρ.le _
  have hβ : kerB s y t ≤ Cy := sq_add_sq_rpow_neg_le hy hs0 hs1 t
  have hρinv : (t ^ 2 + y ^ 2)⁻¹ = (r ^ 2)⁻¹ := by rw [hr2]
  refine ⟨?_, ?_, ?_, hβ0, hβ, ?_, ?_⟩
  · simp [kerA, r, norm_inv, norm_pow]
  · simp [kerA1, r, norm_inv, norm_pow]
  · simp [kerA2, r, norm_inv, norm_pow]
  · unfold kerB1
    change |-2 * s * t * (kerB s y t * (t ^ 2 + y ^ 2)⁻¹)| ≤ _
    rw [hρinv, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hs0, abs_of_nonneg (mul_nonneg hβ0 (by positivity))]
    have h1 : 2 * s * |t| ≤ 2 * r := by nlinarith [abs_nonneg t]
    calc 2 * s * |t| * (kerB s y t * (r ^ 2)⁻¹) ≤ 2 * r * (Cy * (r ^ 2)⁻¹) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right hβ (by positivity)) (by positivity) (by positivity)
      _ = 2 * Cy * r⁻¹ := by field_simp
  · unfold kerB2
    change |-2 * s * (kerB s y t * (t ^ 2 + y ^ 2)⁻¹) +
      4 * s * (s + 1) * t ^ 2 * (kerB s y t * (t ^ 2 + y ^ 2)⁻¹ * (t ^ 2 + y ^ 2)⁻¹)| ≤ _
    rw [hρinv]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hs0,
      abs_of_nonneg (mul_nonneg hβ0 (by positivity)), abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * s * (s + 1) * t ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ kerB s y t * (r ^ 2)⁻¹ * (r ^ 2)⁻¹)]
    have hq : t ^ 2 * (r ^ 2)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by positivity)]; linarith
    have hB' : kerB s y t * (r ^ 2)⁻¹ ≤ Cy * (r ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hβ (by positivity)
    have hB'0 : 0 ≤ kerB s y t * (r ^ 2)⁻¹ := by positivity
    have hss : s * (s + 1) ≤ 2 := by nlinarith
    calc 2 * s * (kerB s y t * (r ^ 2)⁻¹) + 4 * s * (s + 1) * t ^ 2 * (kerB s y t * (r ^ 2)⁻¹ * (r ^ 2)⁻¹)
        = 2 * s * (kerB s y t * (r ^ 2)⁻¹) +
            4 * (s * (s + 1)) * (t ^ 2 * (r ^ 2)⁻¹) * (kerB s y t * (r ^ 2)⁻¹) := by ring
      _ ≤ 2 * 1 * (Cy * (r ^ 2)⁻¹) + 4 * 2 * 1 * (Cy * (r ^ 2)⁻¹) := by
          gcongr
      _ = 10 * Cy * (r ^ 2)⁻¹ := by ring

/-- `‖h'(t)‖ ≤ 4 (1 + y⁻²) r⁻³`, `r = |t + iy|`. -/
theorem norm_rowKernel1_le :
    ‖rowKernel1 s y t‖ ≤ 4 * (1 + (y ^ 2)⁻¹) * (‖(t : ℂ) + y * I‖ ^ 3)⁻¹ := by
  obtain ⟨nA, nA1, -, hβ0, hβ, hB1, -⟩ := kerBounds hs0 hs1 hy t
  set r := ‖(t : ℂ) + y * I‖
  have hr0 : 0 < r := norm_pos_iff.2 (add_mul_I_ne_zero hy t)
  unfold rowKernel1
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hβ0, nA, nA1]
  calc 2 * (r ^ 3)⁻¹ * kerB s y t + (r ^ 2)⁻¹ * |kerB1 s y t|
      ≤ 2 * (r ^ 3)⁻¹ * (1 + (y ^ 2)⁻¹) + (r ^ 2)⁻¹ * (2 * (1 + (y ^ 2)⁻¹) * r⁻¹) := by
        gcongr
    _ = 4 * (1 + (y ^ 2)⁻¹) * (r ^ 3)⁻¹ := by field_simp; ring

/-- `‖h''(t)‖ ≤ 24 (1 + y⁻²) r⁻⁴`, `r = |t + iy|`. -/
theorem norm_rowKernel2_le :
    ‖rowKernel2 s y t‖ ≤ 24 * (1 + (y ^ 2)⁻¹) * (‖(t : ℂ) + y * I‖ ^ 4)⁻¹ := by
  obtain ⟨nA, nA1, nA2, hβ0, hβ, hB1, hB2⟩ := kerBounds hs0 hs1 hy t
  set r := ‖(t : ℂ) + y * I‖
  have hr0 : 0 < r := norm_pos_iff.2 (add_mul_I_ne_zero hy t)
  unfold rowKernel2
  refine norm_add₃_le.trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0,
    nA, nA1, nA2, show ‖(2 : ℂ)‖ = 2 by simp]
  calc 6 * (r ^ 4)⁻¹ * kerB s y t + 2 * (2 * (r ^ 3)⁻¹ * |kerB1 s y t|) + (r ^ 2)⁻¹ * |kerB2 s y t|
      ≤ 6 * (r ^ 4)⁻¹ * (1 + (y ^ 2)⁻¹) + 2 * (2 * (r ^ 3)⁻¹ * (2 * (1 + (y ^ 2)⁻¹) * r⁻¹)) +
          (r ^ 2)⁻¹ * (10 * (1 + (y ^ 2)⁻¹) * (r ^ 2)⁻¹) := by
        gcongr
    _ = 24 * (1 + (y ^ 2)⁻¹) * (r ^ 4)⁻¹ := by field_simp; ring

omit hs0 hs1 in
theorem inv_pow_three_le :
    (‖(t : ℂ) + y * I‖ ^ 3)⁻¹ ≤ y⁻¹ * (t ^ 2 + y ^ 2)⁻¹ := by
  set r := ‖(t : ℂ) + y * I‖
  have hr2 : r ^ 2 = t ^ 2 + y ^ 2 := norm_add_mul_I_sq t y
  have hr0 : 0 < r := norm_pos_iff.2 (add_mul_I_ne_zero hy t)
  have hry : y ≤ r := by nlinarith [sq_nonneg t]
  rw [← hr2, show r ^ 3 = r * r ^ 2 by ring, mul_inv]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hy hry) (by positivity)

omit hs0 hs1 in
theorem inv_pow_four_le :
    (‖(t : ℂ) + y * I‖ ^ 4)⁻¹ ≤ (y ^ 2)⁻¹ * (t ^ 2 + y ^ 2)⁻¹ := by
  set r := ‖(t : ℂ) + y * I‖
  have hr2 : r ^ 2 = t ^ 2 + y ^ 2 := norm_add_mul_I_sq t y
  have hr0 : 0 < r := norm_pos_iff.2 (add_mul_I_ne_zero hy t)
  rw [← hr2, show r ^ 4 = r ^ 2 * r ^ 2 by ring, mul_inv]
  refine mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) ?_) (by positivity)
  rw [hr2]; nlinarith [sq_nonneg t]

end Bounds

theorem norm_rowKernel1_le' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖rowKernel1 s y t‖ ≤ 4 * (1 + (y ^ 2)⁻¹) * y⁻¹ * (t ^ 2 + y ^ 2)⁻¹ := by
  refine (norm_rowKernel1_le hs0 hs1 hy t).trans ?_
  rw [mul_assoc (4 * (1 + (y ^ 2)⁻¹))]
  exact mul_le_mul_of_nonneg_left (inv_pow_three_le hy t) (by positivity)

theorem norm_rowKernel2_le' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖rowKernel2 s y t‖ ≤ 24 * (1 + (y ^ 2)⁻¹) * (y ^ 2)⁻¹ * (t ^ 2 + y ^ 2)⁻¹ := by
  refine (norm_rowKernel2_le hs0 hs1 hy t).trans ?_
  rw [mul_assoc (24 * (1 + (y ^ 2)⁻¹))]
  exact mul_le_mul_of_nonneg_left (inv_pow_four_le hy t) (by positivity)

theorem differentiable_rowKernel (s : ℝ) {y : ℝ} (hy : 0 < y) : Differentiable ℝ (rowKernel s y) :=
  fun t ↦ (hasDerivAt_rowKernel s hy t).differentiableAt

theorem differentiable_rowKernel1 (s : ℝ) {y : ℝ} (hy : 0 < y) : Differentiable ℝ (rowKernel1 s y) :=
  fun t ↦ (hasDerivAt_rowKernel1 s hy t).differentiableAt

theorem integrable_rowKernel1 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) :
    Integrable (rowKernel1 s y) :=
  ((integrable_inv_sq_add_sq hy).const_mul (4 * (1 + (y ^ 2)⁻¹) * y⁻¹)).mono'
    (differentiable_rowKernel1 s hy).continuous.aestronglyMeasurable
    (Eventually.of_forall (norm_rowKernel1_le' hs0 hs1 hy))

theorem integrable_rowKernel2 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) :
    Integrable (rowKernel2 s y) := by
  have hmeas : AEStronglyMeasurable (rowKernel2 s y) := by
    rw [← deriv_rowKernel1 s hy]
    exact (measurable_deriv _).aestronglyMeasurable
  exact ((integrable_inv_sq_add_sq hy).const_mul (24 * (1 + (y ^ 2)⁻¹) * (y ^ 2)⁻¹)).mono' hmeas
    (Eventually.of_forall (norm_rowKernel2_le' hs0 hs1 hy))

open scoped FourierTransform in
theorem norm_fourier_le_integral_norm (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ t, ‖f t‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [Circle.norm_smul]

/-- The decay constant `K_y = 24 (1 + y⁻²) y⁻² ∫ (t² + y²)⁻¹`. -/
def rowKernelDecay (y : ℝ) : ℝ := 24 * (1 + (y ^ 2)⁻¹) * (y ^ 2)⁻¹ * ∫ t : ℝ, (t ^ 2 + y ^ 2)⁻¹

open scoped FourierTransform in
/-- Two integrations by parts: `𝓕 h'' (ξ) = (2πiξ)² 𝓕 h (ξ)`. -/
theorem fourier_rowKernel2 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (rowKernel2 s y) ξ = (2 * Real.pi * I * ξ) ^ 2 * 𝓕 (rowKernel s y) ξ := by
  have h1 := Real.fourier_deriv (integrable_rowKernel hs0 hs1 hy) (differentiable_rowKernel s hy)
    (by rw [deriv_rowKernel s hy]; exact integrable_rowKernel1 hs0 hs1 hy)
  have h2 := Real.fourier_deriv (integrable_rowKernel1 hs0 hs1 hy) (differentiable_rowKernel1 s hy)
    (by rw [deriv_rowKernel1 s hy]; exact integrable_rowKernel2 hs0 hs1 hy)
  rw [deriv_rowKernel s hy] at h1
  rw [deriv_rowKernel1 s hy] at h2
  rw [h2, h1]
  simp only [smul_eq_mul]
  ring

open scoped FourierTransform in
/-- The uniform Fourier decay (5.3): `‖ĥ_{s,y}(ξ)‖ · 4π²ξ² ≤ K_y` for `0 ≤ s ≤ 1`. -/
theorem norm_fourier_rowKernel_mul_sq_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y)
    (ξ : ℝ) : ‖𝓕 (rowKernel s y) ξ‖ * (4 * Real.pi ^ 2 * ξ ^ 2) ≤ rowKernelDecay y := by
  have heq : ‖𝓕 (rowKernel s y) ξ‖ * (4 * Real.pi ^ 2 * ξ ^ 2) = ‖𝓕 (rowKernel2 s y) ξ‖ := by
    rw [fourier_rowKernel2 hs0 hs1 hy ξ, norm_mul, norm_pow]
    have hn : ‖(2 * (Real.pi : ℂ) * I * (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp
    rw [hn, mul_pow, mul_pow, sq_abs]
    ring
  rw [heq]
  refine (norm_fourier_le_integral_norm _ ξ).trans ?_
  unfold rowKernelDecay
  rw [← integral_const_mul]
  exact integral_mono (integrable_rowKernel2 hs0 hs1 hy).norm
    ((integrable_inv_sq_add_sq hy).const_mul _) (norm_rowKernel2_le' hs0 hs1 hy)

/-! ## The limit `s → 0` of the Fourier transform -/

open scoped FourierTransform in
/-- `ĥ_{s,y}(ξ) → ĥ_{0,y}(ξ)` as `s → 0⁺` (dominated convergence with the uniform majorant). -/
theorem tendsto_fourier_rowKernel {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    Tendsto (fun s ↦ 𝓕 (rowKernel s y) ξ) (𝓝[>] 0) (𝓝 (𝓕 (rowKernel 0 y) ξ)) := by
  simp_rw [Real.fourier_real_eq]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t ↦ (1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2)⁻¹) ?_ ?_
    ((integrable_inv_sq_add_sq hy).const_mul _) ?_
  · refine Eventually.of_forall fun s ↦ ?_
    exact ((Real.continuous_fourierChar.comp (by fun_prop : Continuous fun t : ℝ ↦ -(t * ξ))).smul
      (continuous_rowKernel s hy)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
    exact Eventually.of_forall fun t ↦ by
      rw [Circle.norm_smul]; exact norm_rowKernel_le hs.1.le hs.2.le hy t
  · refine Eventually.of_forall fun t ↦ ?_
    have hρ := sq_add_sq_pos hy t
    have hc : Tendsto (fun s : ℝ ↦ (t ^ 2 + y ^ 2) ^ (-s)) (𝓝[>] 0) (𝓝 ((t ^ 2 + y ^ 2) ^ (-(0 : ℝ)))) :=
      (((Real.continuousAt_const_rpow hρ.ne').comp (continuous_neg.continuousAt)).tendsto).mono_left
        nhdsWithin_le_nhds
    have hc' := ((Complex.continuous_ofReal.tendsto _).comp hc).const_mul
      ((((t : ℂ) + y * I) ^ 2)⁻¹)
    exact hc'.const_smul _

/-! ## The twisted Poisson identity (5.5) -/

open scoped FourierTransform in
theorem fourier_rowKernel_mul_exp (s y r ξ : ℝ) :
    𝓕 (fun t ↦ rowKernel s y t * exp (-(2 * Real.pi * I * r * t))) ξ = 𝓕 (rowKernel s y) (ξ + r) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, mul_comm (rowKernel s y t), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

open scoped FourierTransform in
theorem norm_fourier_rowKernel_le_of_ne {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (rowKernel s y) ξ‖ ≤ rowKernelDecay y / (4 * Real.pi ^ 2) * (1 / |ξ| ^ (2 : ℝ)) := by
  have h := norm_fourier_rowKernel_mul_sq_le hs0 hs1 hy ξ
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  rw [Real.rpow_two, sq_abs, ← div_eq_mul_one_div, div_div, le_div_iff₀ (by positivity)]
  linarith

/-- The shifted Fourier coefficients are absolutely summable. -/
theorem summable_norm_fourier_rowKernel_add {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y)
    (r : ℝ) : Summable fun k : ℤ ↦ ‖FourierTransform.fourier (rowKernel s y) (k + r)‖ := by
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℤ ↦ rowKernelDecay y / (4 * Real.pi ^ 2) * (1 / |(n : ℝ) + r| ^ (2 : ℝ)))
    (((Real.summable_one_div_int_add_rpow r 2).2 (by norm_num)).mul_left _) ?_
  have hfin : Set.Finite {n : ℤ | (n : ℝ) + r = 0} := by
    refine Set.Subsingleton.finite fun a ha b hb ↦ ?_
    have : (a : ℝ) = b := by
      have h1 : (a : ℝ) + r = 0 := ha
      have h2 : (b : ℝ) + r = 0 := hb
      linarith
    exact_mod_cast this
  filter_upwards [hfin.compl_mem_cofinite] with n hn
  rw [norm_norm]
  exact norm_fourier_rowKernel_le_of_ne hs0 hs1 hy hn

/-- The twisted Poisson identity (5.5):
`Σ_ℓ e(-ℓ r) h(x + ℓ) = Σ_k ĥ(k + r) e((k + r) x)`. -/
theorem tsum_twisted_rowKernel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : ℝ} (hy : 0 < y) (r x : ℝ) :
    ∑' ℓ : ℤ, exp (-(2 * Real.pi * I * r * ℓ)) * rowKernel s y (x + ℓ) =
      ∑' k : ℤ, FourierTransform.fourier (rowKernel s y) (k + r) *
        exp (2 * Real.pi * I * (k + r) * x) := by
  set g : ℝ → ℂ := fun t ↦ rowKernel s y t * exp (-(2 * Real.pi * I * r * t)) with hg
  have hgc : Continuous g := (continuous_rowKernel s hy).mul (by fun_prop)
  have hnormg : ∀ t, ‖g t‖ = ‖rowKernel s y t‖ := by
    intro t
    rw [hg, norm_mul, show -(2 * (Real.pi : ℂ) * I * r * t) = ((-(2 * Real.pi * r * t) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hdecay : g =O[cocompact ℝ] (|·| ^ (-(2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound (1 + (y ^ 2)⁻¹) ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with t ht
    have ht0 : t ≠ 0 := ht
    rw [hnormg, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _),
      Real.rpow_two, sq_abs]
    refine (norm_rowKernel_le hs0 hs1 hy t).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg y])
  have hFg : ∀ n : ℤ, FourierTransform.fourier g n = FourierTransform.fourier (rowKernel s y) (n + r) :=
    fun n ↦ fourier_rowKernel_mul_exp s y r n
  have hsum : Summable fun n : ℤ ↦ FourierTransform.fourier g n := by
    simp_rw [hFg]
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℤ ↦ rowKernelDecay y / (4 * Real.pi ^ 2) * (1 / |(n : ℝ) + r| ^ (2 : ℝ)))
      (((Real.summable_one_div_int_add_rpow r 2).2 (by norm_num)).mul_left _) ?_
    have hfin : Set.Finite {n : ℤ | (n : ℝ) + r = 0} := by
      refine Set.Subsingleton.finite fun a ha b hb ↦ ?_
      have : (a : ℝ) = b := by
        have h1 : (a : ℝ) + r = 0 := ha
        have h2 : (b : ℝ) + r = 0 := hb
        linarith
      exact_mod_cast this
    filter_upwards [hfin.compl_mem_cofinite] with n hn
    exact norm_fourier_rowKernel_le_of_ne hs0 hs1 hy hn
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hgc (by norm_num : (1 : ℝ) < 2)
    hdecay hsum x
  simp_rw [hFg, fourier_coe_apply, Complex.ofReal_one, div_one] at hP
  have hL : ∀ ℓ : ℤ, g (x + ℓ) =
      exp (-(2 * Real.pi * I * r * x)) * (exp (-(2 * Real.pi * I * r * ℓ)) * rowKernel s y (x + ℓ)) := by
    intro ℓ
    rw [hg]
    simp only
    rw [mul_comm (rowKernel s y (x + ℓ)), ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hL, tsum_mul_left] at hP
  have hR : ∀ k : ℤ, FourierTransform.fourier (rowKernel s y) (k + r) *
      exp (2 * Real.pi * I * (k + r) * x) =
      exp (2 * Real.pi * I * r * x) * (FourierTransform.fourier (rowKernel s y) (k + r) *
        exp (2 * Real.pi * I * k * x)) := by
    intro k
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hR, tsum_mul_left]
  rw [← hP, ← mul_assoc, ← Complex.exp_add]
  simp

end SMSFormula.RowKernel
