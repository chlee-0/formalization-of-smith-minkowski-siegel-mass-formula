import SMSFormula.AdelicGaussianOneShellWeightRational

/-!
# The rational archimedean shell factor through the product formula

The archimedean factor of the explicit one-shell weight is `|q_a|_∞` with the nonzero rational
`q_a = e_W / (e_B · 2 · det E · det F_L)` (`AdelicGaussianOneShellWeightRational`).  By the
rational product formula it equals `(∏_{p ∈ T} ‖q_a‖_p)⁻¹` for every finite prime set `T` containing
the prime support of `q_a`, so it can be distributed over any sufficiently large common finite set
of primes.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace Rat

/-- The product formula over any finite prime set containing the support. -/
theorem ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one_of_subset
    {c : ℚ} (hc : c ≠ 0) {T : Finset {p : ℕ // Nat.Prime p}}
    (hT : padicNormPrimeSupport c ⊆ T) :
    ENNReal.ofReal |(c : ℝ)| * ∏ q ∈ T, padicNormENNRealAtPrime c q = 1 := by
  rw [← Finset.prod_subset hT]
  · exact ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one c hc
  · intro q _ hq
    simp only [padicNormENNRealAtPrime]
    rw [nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport hc q hq, ENNReal.coe_one]

/-- `|c|_∞ = (∏_{p ∈ T} ‖c‖_p)⁻¹` for any finite `T` containing the support. -/
theorem ofReal_abs_eq_inv_prod_padicNormENNRealAtPrime
    {c : ℚ} (hc : c ≠ 0) {T : Finset {p : ℕ // Nat.Prime p}}
    (hT : padicNormPrimeSupport c ⊆ T) :
    ENNReal.ofReal |(c : ℝ)| = (∏ q ∈ T, padicNormENNRealAtPrime c q)⁻¹ :=
  (ENNReal.eq_inv_of_mul_eq_one_left
    (ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one_of_subset hc hT))

end Rat

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The rational number whose real absolute value is the archimedean shell factor:
`q = e_W / (e_B · 2 · det E · det F_V)`. -/
def rationalShellFactor (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℚ :=
  Matrix.skewAdjointFixedFormElementaryDetScalar P.lowerSpace.pairingMatrix P.lowerSpace.form_symm
      P.lowerSpace.form_det_ne_zero /
    (Matrix.skewAdjointFixedFormElementaryDetScalar (P.blockSpace hx).pairingMatrix
        (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero * 2 *
      (P.blockToAmbientRationalMatrix hx).det * V.pairingMatrix.det)

theorem blockToAmbientRationalMatrix_det_ne_zero (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRationalMatrix hx).det ≠ 0 := by
  have h := congrArg Matrix.det
    (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem rationalShellFactor_ne_zero (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.rationalShellFactor hx ≠ 0 := by
  unfold rationalShellFactor
  refine div_ne_zero (Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _) ?_
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _) two_ne_zero)
    (P.blockToAmbientRationalMatrix_det_ne_zero hx)) V.form_det_ne_zero

/-- The real expression in `exists_representedNormTheta_mul_rationalWeight_eq` is `|q|_∞`, given
`det F_V > 0`. -/
theorem abs_rationalShellFactor_eq (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hdF : (0 : ℝ) < ((V.pairingMatrix.det : ℚ) : ℝ)) :
    |((P.rationalShellFactor hx : ℚ) : ℝ)| =
      |(Matrix.skewAdjointFixedFormElementaryDetScalar
          P.lowerSpace.pairingMatrix P.lowerSpace.form_symm P.lowerSpace.form_det_ne_zero : ℝ)| /
        (|(Matrix.skewAdjointFixedFormElementaryDetScalar
          (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
          (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 *
          |(((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ)| *
          ((V.pairingMatrix.det : ℚ) : ℝ)) := by
  unfold rationalShellFactor
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, abs_div, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hdF]

/-- The archimedean shell factor as a finite p-ADIC product: for any finite prime set `T`
containing the support of `q`, `|q|_∞ = (∏_{p ∈ T} ‖q‖_p)⁻¹`. -/
theorem ofReal_archimedeanShellFactor_eq_inv_prod (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hdF : (0 : ℝ) < ((V.pairingMatrix.det : ℚ) : ℝ)) {T : Finset {p : ℕ // Nat.Prime p}}
    (hT : Rat.padicNormPrimeSupport (P.rationalShellFactor hx) ⊆ T) :
    ENNReal.ofReal
        (|(Matrix.skewAdjointFixedFormElementaryDetScalar
            P.lowerSpace.pairingMatrix P.lowerSpace.form_symm P.lowerSpace.form_det_ne_zero : ℝ)| /
          (|(Matrix.skewAdjointFixedFormElementaryDetScalar
            (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
            (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 *
            |(((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ)| *
            ((V.pairingMatrix.det : ℚ) : ℝ))) =
      (∏ q ∈ T, Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx) q)⁻¹ := by
  rw [← P.abs_rationalShellFactor_eq hx hdF]
  exact Rat.ofReal_abs_eq_inv_prod_padicNormENNRealAtPrime (P.rationalShellFactor_ne_zero hx) hT

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation
