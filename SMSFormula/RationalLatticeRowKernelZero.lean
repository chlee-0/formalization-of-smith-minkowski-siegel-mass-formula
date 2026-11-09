import SMSFormula.RationalLatticeRowKernel
import SMSFormula.RationalAdeleRankOneEisensteinPoisson

/-!
# The unregularized row kernel is the archimedean factor

At `s = 0` the row kernel is `h_{0,y}(t) = (t + iy)⁻² = -(y - it)⁻²`, i.e. `-|det|^{1/2}` times the rank-four
archimedean Bruhat factor `(y - it)^{-2}` (`rowKernel_zero_eq_polarArchimedeanBruhatFactor`).  Hence the
closed-form Fourier transform gives

`ĥ_{0,y}(ξ) = -4π² ξ e^{-2πyξ}` for `ξ > 0`, and `ĥ_{0,y}(ξ) = 0` for `ξ ≤ 0`,

and in particular `ĥ_{0,y}(m) e(mx) = -4π² m e(mz)` for `m > 0` (`fourier_rowKernel_zero_mul_exp_of_pos`), the
holomorphic q-expansion term.  The determinant factor cancels exactly; nothing is chosen.
-/

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

open SMSFormula.RowKernel

variable (L : PositiveDefiniteIntegralLattice 4)

theorem rowKernel_zero_eq_polarArchimedeanBruhatFactor {y : ℝ} (hy : 0 < y) (v : ℝ) :
    rowKernel 0 y v = -(L.polarRealDeterminantScale : ℂ) * L.polarArchimedeanBruhatFactor y v := by
  unfold rowKernel polarArchimedeanBruhatFactor
  rw [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one, div_pow, one_pow, cpow_half_pow_four]
  have hdet : (L.polarRealDeterminantScale : ℂ) ≠ 0 := by
    exact_mod_cast L.polarRealDeterminantScale_pos.ne'
  have hw : (y : ℂ) - v * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hy.ne' this
  have hsq : ((v : ℂ) + y * I) ^ 2 = -((y : ℂ) - v * I) ^ 2 := by
    linear_combination ((v : ℂ) ^ 2 + (y : ℂ) ^ 2) * I_sq
  rw [hsq]
  field_simp

theorem rowKernel_zero_eq_smul {y : ℝ} (hy : 0 < y) :
    rowKernel 0 y = fun v ↦ (-(L.polarRealDeterminantScale : ℂ)) • L.polarArchimedeanBruhatFactor y v := by
  funext v
  rw [smul_eq_mul, L.rowKernel_zero_eq_polarArchimedeanBruhatFactor hy v]

theorem fourier_rowKernel_zero_eq {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (rowKernel 0 y) ξ =
      -(L.polarRealDeterminantScale : ℂ) * 𝓕 (L.polarArchimedeanBruhatFactor y) ξ := by
  rw [L.rowKernel_zero_eq_smul hy, Real.fourier_real_eq, Real.fourier_real_eq, ← smul_eq_mul,
    ← integral_smul]
  congr 1
  funext v
  rw [smul_comm]

include L in
/-- `ĥ_{0,y}(ξ) = -4π² ξ e^{-2πyξ}` for `ξ > 0`. -/
theorem fourier_rowKernel_zero_of_pos {y : ℝ} (hy : 0 < y) {ξ : ℝ} (hξ : 0 < ξ) :
    𝓕 (rowKernel 0 y) ξ = -((4 * Real.pi ^ 2 * ξ * Real.exp (-(2 * Real.pi * y) * ξ) : ℝ) : ℂ) := by
  rw [L.fourier_rowKernel_zero_eq hy, L.fourier_polarArchimedeanBruhatFactor_of_pos hy (by norm_num) hξ,
    neg_mul, ← Complex.ofReal_mul]
  have hdet : (L.polarRealDeterminantScale : ℝ) ≠ 0 := by
    exact_mod_cast L.polarRealDeterminantScale_pos.ne'
  congr 2
  have h2 : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
  rw [h2, Real.Gamma_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
  field_simp
  ring

include L in
/-- `ĥ_{0,y}(ξ) = 0` for `ξ ≤ 0`. -/
theorem fourier_rowKernel_zero_of_nonpos {y : ℝ} (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≤ 0) :
    𝓕 (rowKernel 0 y) ξ = 0 := by
  rw [L.fourier_rowKernel_zero_eq hy, L.fourier_polarArchimedeanBruhatFactor_of_nonpos hy (by norm_num) hξ,
    mul_zero]

include L in
/-- The holomorphic q-expansion term: `ĥ_{0,y}(m) e(mx) = -4π² m e(m(x + iy))` for `m > 0`. -/
theorem fourier_rowKernel_zero_mul_exp_of_pos {y : ℝ} (hy : 0 < y) {m : ℝ} (hm : 0 < m) (x : ℝ) :
    𝓕 (rowKernel 0 y) m * exp (2 * Real.pi * I * m * x) =
      -(4 * Real.pi ^ 2 * m : ℂ) * exp (2 * Real.pi * I * m * ((x : ℂ) + y * I)) := by
  rw [L.fourier_rowKernel_zero_of_pos hy hm]
  push_cast
  calc -(4 * (Real.pi : ℂ) ^ 2 * m * exp (-(2 * Real.pi * y) * m)) * exp (2 * Real.pi * I * m * x)
      = -(4 * (Real.pi : ℂ) ^ 2 * m) * (exp (-(2 * Real.pi * y) * m) * exp (2 * Real.pi * I * m * x)) := by
        ring
    _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        linear_combination (-(2 * (Real.pi : ℂ) * m * y)) * I_sq

end PositiveDefiniteIntegralLattice
