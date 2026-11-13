import SMSFormula.QuadraticOrbitDeterminantElementary
import SMSFormula.AdelicGaussianRationalShellFactorProductFormula
import Mathlib.Data.Rat.Star

/-!
# The rational shell identity `r · q_a = ± det E`

For the supplied anisotropic-complement presentation of `V` at `x` (block-to-ambient rational matrix
`E`, `Eᵀ F_V E = F_B`), the rational orbit gauge ratio `r = J / ((−1)^m / (2a))` and the rational
archimedean shell factor `q_a = e_W / (e_B · 2 · det E · det F_V)` satisfy

`|r · q_a| = |det E|`,  i.e.  `r · q_a = ± det E`.

It uses `|J| = |e_B| · |det F_W| / |e_W|` (`abs_lastOrbitDeterminant_eq`) and
`a · det F_W = det F_B = (det E)² · det F_V`.  Consequently every local factor `‖r q_a‖_v` of the
shell weight is `‖det E‖_v`.  Nothing is chosen.
-/

noncomputable section

open scoped ENNReal

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- `(det E)² · det F_V = det F_W · a`. -/
theorem blockToAmbientRationalMatrix_det_sq_mul (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRationalMatrix hx).det ^ 2 * V.pairingMatrix.det =
      P.lowerSpace.pairingMatrix.det * V.nativeRationalQuadraticForm x := by
  have hcong := congrArg Matrix.det (P.blockToAmbientRationalMatrix_form_congruence hx)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hcong
  have hB : ((P.blockSpace hx).pairingMatrix.det : ℚ) =
      P.lowerSpace.pairingMatrix.det * V.nativeRationalQuadraticForm x :=
    nonisotropicLastBlockMatrix_det _ _
  rw [← hB, ← hcong]
  ring

/-- The rational shell identity: `|r · q_a| = |det E|`. -/
theorem abs_lastOrbitGaugeRatio_mul_rationalShellFactor (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    |P.lowerSpace.lastOrbitGaugeRatio (V.nativeRationalQuadraticForm x) hx ℚ *
        P.rationalShellFactor hx| = |(P.blockToAmbientRationalMatrix hx).det| := by
  have hJ := P.lowerSpace.abs_lastOrbitDeterminant_eq (V.nativeRationalQuadraticForm x) hx
  have hsq := P.blockToAmbientRationalMatrix_det_sq_mul hx
  have heB := Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero (P.blockSpace hx).pairingMatrix
    (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero
  have heW := Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero P.lowerSpace.pairingMatrix
    P.lowerSpace.form_symm P.lowerSpace.form_det_ne_zero
  have hE := P.blockToAmbientRationalMatrix_det_ne_zero hx
  have hV := V.form_det_ne_zero
  unfold lastOrbitGaugeRatio rationalShellFactor
  rw [abs_mul, abs_div, abs_div, hJ, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul, abs_mul,
    abs_mul, abs_mul, abs_two]
  have habs : |(P.blockToAmbientRationalMatrix hx).det| ^ 2 * |V.pairingMatrix.det| =
      |P.lowerSpace.pairingMatrix.det| * |V.nativeRationalQuadraticForm x| := by
    rw [← abs_pow, ← abs_mul, hsq, abs_mul]
  have hEa : 0 < |(P.blockToAmbientRationalMatrix hx).det| := abs_pos.mpr hE
  have hVa : 0 < |V.pairingMatrix.det| := abs_pos.mpr hV
  have heBa : 0 < |Matrix.skewAdjointFixedFormElementaryDetScalar (P.blockSpace hx).pairingMatrix
    (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero| := abs_pos.mpr heB
  have heWa : 0 < |Matrix.skewAdjointFixedFormElementaryDetScalar P.lowerSpace.pairingMatrix
    P.lowerSpace.form_symm P.lowerSpace.form_det_ne_zero| := abs_pos.mpr heW
  field_simp
  linear_combination (norm := ring_nf) (-1 : ℚ) * habs <;>
    (trace_state; simp only [eq_ratCast, Rat.cast_id] <;> ring)

/-- `r · q_a = det E` or `r · q_a = − det E`. -/
theorem lastOrbitGaugeRatio_mul_rationalShellFactor_eq_or (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.lowerSpace.lastOrbitGaugeRatio (V.nativeRationalQuadraticForm x) hx ℚ *
        P.rationalShellFactor hx = (P.blockToAmbientRationalMatrix hx).det ∨
      P.lowerSpace.lastOrbitGaugeRatio (V.nativeRationalQuadraticForm x) hx ℚ *
        P.rationalShellFactor hx = -(P.blockToAmbientRationalMatrix hx).det :=
  abs_eq_abs.mp (P.abs_lastOrbitGaugeRatio_mul_rationalShellFactor hx)

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

namespace Rat

theorem padicNormPrimeSupport_neg (c : ℚ) : padicNormPrimeSupport (-c) = padicNormPrimeSupport c := by
  simp [padicNormPrimeSupport]

theorem padicNormENNRealAtPrime_neg (c : ℚ) (q : {p : ℕ // Nat.Prime p}) :
    padicNormENNRealAtPrime (-c) q = padicNormENNRealAtPrime c q := by
  simp [padicNormENNRealAtPrime]

theorem padicNormPrimeSupport_eq_of_abs_eq {c d : ℚ} (h : |c| = |d|) :
    padicNormPrimeSupport c = padicNormPrimeSupport d := by
  rcases abs_eq_abs.mp h with h | h <;> simp [h, padicNormPrimeSupport_neg]

theorem padicNormENNRealAtPrime_eq_of_abs_eq {c d : ℚ} (h : |c| = |d|)
    (q : {p : ℕ // Nat.Prime p}) : padicNormENNRealAtPrime c q = padicNormENNRealAtPrime d q := by
  rcases abs_eq_abs.mp h with h | h <;> simp [h, padicNormENNRealAtPrime_neg]

end Rat

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation
