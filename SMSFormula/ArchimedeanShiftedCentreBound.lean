import SMSFormula.ArchimedeanShiftedGaussianBound
import SMSFormula.ShellFixedWidthGaussian
import SMSFormula.PolarGaussianQuadraticIdentification

/-!
# The shifted centre costs nothing at the real place

`ArchimedeanShiftedGaussianBound` bounds the archimedean factor of the centred real Gaussian: at
width `b > 0` and frequency `t` it is a real power of `b - i t`, of modulus `(b^2 + t^2)^(-n/4)`,
integrable in the frequency for rank above two.  The route's determining family is indexed by
centres, so what the analytic admissibility `G_b subset L` actually needs is that bound at every
centre.  This file proves the real-place shape of that bound.

The centre enters through one factor, and that factor never exceeds one.  Completing the square in
the exponent `-b Q(x - u) + i t Q(x)` moves the centre to the complex ratio `b / (b - i t)` and
leaves behind exactly one scalar, `b Q(u) * (i t) / (b - i t)`.  Its real part is
`- b Q(u) t^2 / (b^2 + t^2)`, which is at most zero as soon as the form is nonnegative at the
centre -- so the extra factor has modulus at most one and the centred majorant dominates every
centre, with no dependence on the centre at all.

What that buys.  A single integrable majorant `(b^2 + t^2)^(-n/4)` for the whole fixed-width family
at a fixed width, which is the shape a dominated-convergence or class-membership argument consumes.

Negative scope, and it is wide.  No Gaussian integral is evaluated here: the coefficient is
defined as the centred power times the completion factor, which is the shape the completion identity
predicts, and calling it the transform of the shifted Gaussian stays a naming convention until an
actual evaluation is supplied -- exactly the qualification already recorded for the triangular
cutoff.  Nothing is adelic: this is the real place alone, no finite-adelic factor appears, and the
good-prime estimate `|I_p(t)| = |t|_p^(-n/2)` with its finitely many exceptional primes is
untouched.  The uniformity is in the centre at a fixed width, never across widths.
-/

namespace SMSFormula.ArchimedeanCentre

open MeasureTheory Complex QuadraticMap SMSFormula.ShiftedGaussian

/-! ## Completing the square -/

/-- The complex width at frequency `t`.  A positive real width keeps it off the origin. -/
noncomputable def width (b t : ℝ) : ℂ := (b : ℂ) - (t : ℂ) * Complex.I

theorem width_re (b t : ℝ) : (width b t).re = b := by simp [width]

theorem width_im (b t : ℝ) : (width b t).im = -t := by simp [width]

theorem width_ne_zero {b : ℝ} (hb : 0 < b) (t : ℝ) : width b t ≠ 0 := by
  intro h
  have := width_re b t
  rw [h] at this
  simp at this
  exact hb.ne this

/-- Completing the square, purely algebraically and with no reference to `I`.  For a nonzero
complex `w` the quadratic-plus-linear expression `-w q + b β - b c` is `-w` times the shifted
quadratic at the ratio `b / w`, plus one leftover scalar `b c (b - w) / w`.  With `w = b - i t` the
leftover is `b c (i t) / (b - i t)`, which is the centre's whole contribution. -/
theorem completion_scalar {w : ℂ} (hw : w ≠ 0) (b q β c : ℂ) :
    -w * q + b * β - b * c =
      -w * (q - (b / w) * β + (b / w) ^ 2 * c) + b * c * ((b - w) / w) := by
  field_simp
  ring

/-- The leftover at the actual width: `b - (b - i t) = i t`, so the completion identity reads with
the imaginary displacement written out. -/
theorem completion_width {b : ℝ} (hb : 0 < b) (t : ℝ) (q β c : ℂ) :
    -(width b t) * q + (b : ℂ) * β - (b : ℂ) * c =
      -(width b t) * (q - ((b : ℂ) / width b t) * β + ((b : ℂ) / width b t) ^ 2 * c) +
        (b : ℂ) * c * ((t : ℂ) * Complex.I / width b t) := by
  have h := completion_scalar (width_ne_zero hb t) (b : ℂ) q β c
  have hdisp : (b : ℂ) - width b t = (t : ℂ) * Complex.I := by simp [width]
  rw [hdisp] at h
  exact h

/-- Why the shifted quadratic is the form's own shape.  At a real ratio the expression the
completion produces is literally the quadratic form at the translated point, so the three scalars
`Q x`, `polar Q x u` and `Q u` are all the centre contributes. -/
theorem quadratic_sub_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (Q : QuadraticForm ℝ E)
    (x u : E) (r : ℝ) : Q (x - r • u) = Q x - r * polar Q x u + r ^ 2 * Q u := by
  have h : Q (x - r • u) = Q x + Q (r • u) - polar Q x (r • u) := quadratic_map_sub Q _ _
  rw [h, Q.map_smul, polar_smul_right]
  simp only [smul_eq_mul]
  ring

/-! ## The shift factor and its modulus -/

/-- The shift exponent: the leftover scalar of the completion, with the archimedean `2 pi` in
place.  The centre enters only through the value `c` of the form at it. -/
noncomputable def shiftExponent (b t c : ℝ) : ℂ :=
  ((2 * Real.pi * b * c : ℝ) : ℂ) * ((t : ℂ) * Complex.I / width b t)

/-- The real part is a closed formula, and it is where the sign lives. -/
theorem re_shiftExponent {b : ℝ} (hb : 0 < b) (t c : ℝ) :
    (shiftExponent b t c).re = -(2 * Real.pi * b * c * t ^ 2 / (b ^ 2 + t ^ 2)) := by
  have hpos : (0 : ℝ) < b ^ 2 + t ^ 2 := by positivity
  have hnormSq : Complex.normSq (width b t) = b ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply, width_re, width_im]
    ring
  have hquot : ((t : ℂ) * Complex.I / width b t).re = -(t ^ 2 / (b ^ 2 + t ^ 2)) := by
    rw [Complex.div_re, hnormSq, width_re, width_im]
    simp
    field_simp
  rw [shiftExponent, Complex.re_ofReal_mul, hquot]
  field_simp

/-- The modulus of the shift factor, exactly. -/
theorem norm_shiftFactor {b : ℝ} (hb : 0 < b) (t c : ℝ) :
    ‖Complex.exp (shiftExponent b t c)‖ =
      Real.exp (-(2 * Real.pi * b * c * t ^ 2 / (b ^ 2 + t ^ 2))) := by
  rw [Complex.norm_exp, re_shiftExponent hb]

/-- The decisive bound: at a nonnegative form value the shift factor never exceeds one, so the
centred majorant already dominates every centre. -/
theorem norm_shiftFactor_le_one {b : ℝ} (hb : 0 < b) (t : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ‖Complex.exp (shiftExponent b t c)‖ ≤ 1 := by
  rw [norm_shiftFactor hb]
  rw [Real.exp_le_one_iff]
  have hpos : (0 : ℝ) < b ^ 2 + t ^ 2 := by positivity
  have : 0 ≤ 2 * Real.pi * b * c * t ^ 2 / (b ^ 2 + t ^ 2) := by
    apply div_nonneg _ hpos.le
    have : 0 ≤ 2 * Real.pi * b * c := by positivity
    positivity
  linarith

/-- At the zero frequency the factor is exactly one, so the bound is attained and the centre is
invisible there. -/
theorem norm_shiftFactor_zero_frequency {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ‖Complex.exp (shiftExponent b 0 c)‖ = 1 := by
  rw [norm_shiftFactor hb]
  simp

/-- Away from the zero frequency and at a positive form value the bound is strict, so the shift
factor is a genuine gain and not an identity. -/
theorem norm_shiftFactor_lt_one {b : ℝ} (hb : 0 < b) {t c : ℝ} (ht : t ≠ 0) (hc : 0 < c) :
    ‖Complex.exp (shiftExponent b t c)‖ < 1 := by
  rw [norm_shiftFactor hb, Real.exp_lt_one_iff]
  have hpos : (0 : ℝ) < b ^ 2 + t ^ 2 := by positivity
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have : 0 < 2 * Real.pi * b * c * t ^ 2 / (b ^ 2 + t ^ 2) := by
    apply div_pos _ hpos
    have : 0 < 2 * Real.pi * b * c := by positivity
    positivity
  linarith

/-! ## The shifted coefficient and its uniform majorant -/

/-- The archimedean coefficient at a shifted centre, in the shape the completion predicts: the
centred power times the shift factor.  This is a definition of that shape, not an evaluated
Gaussian integral. -/
noncomputable def shiftedCoefficient (n : ℕ) (b t c : ℝ) : ℂ :=
  width b t ^ ((-(n : ℝ) / 2 : ℝ) : ℂ) * Complex.exp (shiftExponent b t c)

/-- The centred case is recovered: at form value zero the coefficient is the centred power. -/
theorem shiftedCoefficient_zero (n : ℕ) (b t : ℝ) :
    shiftedCoefficient n b t 0 = width b t ^ ((-(n : ℝ) / 2 : ℝ) : ℂ) := by
  simp [shiftedCoefficient, shiftExponent]

/-- The uniform majorant.  At a nonnegative form value the modulus of the shifted coefficient is at
most `(b^2 + t^2)^(-n/4)` -- the centred bound, with no dependence on the centre. -/
theorem norm_shiftedCoefficient_le (n : ℕ) {b : ℝ} (hb : 0 < b) (t : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ‖shiftedCoefficient n b t c‖ ≤ (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4) := by
  rw [shiftedCoefficient, norm_mul]
  have hpow : ‖width b t ^ ((-(n : ℝ) / 2 : ℝ) : ℂ)‖ = (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4) := by
    rw [width, SMSFormula.Archimedean.norm_cpow_shifted b t hb]
    congr 1
    ring
  rw [hpow]
  have hnn : (0 : ℝ) ≤ (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4) := by positivity
  calc (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4) * ‖Complex.exp (shiftExponent b t c)‖
      ≤ (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4) * 1 :=
        mul_le_mul_of_nonneg_left (norm_shiftFactor_le_one hb t hc) hnn
    _ = (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4) := mul_one _

/-- The payoff, stated as the domination it is: for rank above two one integrable function of the
frequency dominates the shifted coefficient at every centre whose form value is nonnegative. -/
theorem exists_uniform_integrable_majorant {n : ℕ} (hn : 2 < n) {b : ℝ} (hb : 0 < b) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ c : ℝ, 0 ≤ c → ∀ t : ℝ, ‖shiftedCoefficient n b t c‖ ≤ g t := by
  refine ⟨fun t ↦ (b ^ 2 + t ^ 2) ^ (-(n : ℝ) / 4),
    SMSFormula.Archimedean.integrable_shifted_bound hn hb, fun c hc t ↦ ?_⟩
  exact norm_shiftedCoefficient_le n hb t hc

/-! ## Every centre, for a positive definite form -/

end SMSFormula.ArchimedeanCentre
