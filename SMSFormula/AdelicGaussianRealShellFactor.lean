import SMSFormula.AdelicGaussianRealOrbitDensity
import SMSFormula.RationalSpecialOrthogonalRealMassRatio
import SMSFormula.RationalAdeleNormalizedWordSplit
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarModulus

/-!
# The archimedean factor of the explicit shell weight is Γ- and π-free

In the explicit one-shell weight the archimedean data enter as `Re d_∞(a) · μ_W(SO_W(ℝ)) /
μ_B(SO_B(ℝ))`, with `B = W ⊕ ⟨a⟩` of rank `N = m + 1`.  Combining the closed form
`Re d_∞ = √polarDeterminant(L)⁻¹ (2π)^{N/2}/Γ(N/2) a^{N/2−1}` with the real masses of `W` and `B`,

`Re d_∞ · μ_W · (|e_B| · 2 · √a · √|det W| · √polarDeterminant L) = μ_B · (|e_W| · √2^N)`.

All Γ-values and powers of `π` cancel; what remains is algebraic (the basis-comparison
determinants `e_W, e_B`, `√a`, `√|det W|`, `√polarDeterminant L`, `√2^N`).

For the supplied anisotropic-complement presentation of `L` at `x` (`Q(x) = a`), with
block-to-ambient rational matrix `E` (`Eᵀ F_L E = F_B`, `det F_B = a · det W`) and
`polarDeterminant L = det(2 F_L)`, all square roots disappear too:

`Re d_∞ · μ_W · (|e_B| · 2 · |det E| · det F_L) = μ_B · |e_W|`,

so the archimedean factor of the shell weight is `|e_W| / (2 |e_B| |det E| det F_L)`, the
real absolute value of a nonzero rational number.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped Real

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {m : ℕ}

private theorem realShellFactor_sqrt_two_pow (m : ℕ) :
    (2 : ℝ) ^ (((m + 1 : ℕ) : ℝ) / 2) = Real.sqrt 2 ^ (m + 1) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

private theorem realShellFactor_rpow_mul_sqrt {a : ℝ} (ha : 0 < a) (m : ℕ) :
    a ^ (((m + 1 : ℕ) : ℝ) / 2 - 1) * Real.sqrt a = Real.sqrt a ^ m := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (a ^ (1 / 2 : ℝ)), ← Real.rpow_mul ha.le,
    ← Real.rpow_add ha]
  congr 1
  push_cast
  ring

/-- The archimedean shell factor:
`Re d_∞(a) · μ_W · (|e_B|·2·√a·√|det W|·√polarDeterminant L) = μ_{W⊕⟨a⟩} · (|e_W|·√2^{m+1})`. -/
theorem ofReal_re_realLocalValueDensity_mul_realMass_eq (L : PositiveDefiniteIntegralLattice (m + 1)) {b : ℝ}
    (hb : 0 < b) (hm : 2 ≤ m) (W : RationalQuadraticSpaceMatrix m) [NeZero m]
    (hW : (W.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) {a : ℚ} (ha : a ≠ 0) (ha0 : 0 < a) :
    ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L b (algebraMap ℚ RationalAdele a))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele a))).re) *
        W.realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_symm
              (W.nonisotropicLastExtension a ha).form_det_ne_zero : ℝ)| *
          2 * Real.sqrt (a : ℝ) * Real.sqrt |((W.pairingMatrix.det : ℚ) : ℝ)| *
          (L.polarRealDeterminantScale : ℝ)) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              W.pairingMatrix W.form_symm W.form_det_ne_zero : ℝ)| * Real.sqrt 2 ^ (m + 1)) := by
  have hmass := W.realInvariantDifferentialGroupMeasure_nonisotropicLastExtension_mul_eq hW ha ha0
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha0
  have hreal : 0 < rationalAdeleRealScalar (algebraMap ℚ RationalAdele a) := by
    rw [rationalAdeleRealScalar_diagonal]; exact ha'
  have hRe := re_realLocalValueDensity_gaussianOrbitTestRealFactor L hb (by omega) _ hreal
  generalize (L.rationalQuadraticSpaceMatrix.realLocalValueDensity
      (gaussianOrbitTestRealFactor L b (algebraMap ℚ RationalAdele a))
      (rationalAdeleRealScalar (algebraMap ℚ RationalAdele a))).re = R at hRe ⊢
  rw [rationalAdeleRealScalar_diagonal] at hRe
  set eW := (Matrix.skewAdjointFixedFormElementaryDetScalar W.pairingMatrix W.form_symm
    W.form_det_ne_zero : ℝ)
  set eB := (Matrix.skewAdjointFixedFormElementaryDetScalar
    (W.nonisotropicLastExtension a ha).pairingMatrix (W.nonisotropicLastExtension a ha).form_symm
    (W.nonisotropicLastExtension a ha).form_det_ne_zero : ℝ)
  set dW : ℝ := ((W.pairingMatrix.det : ℚ) : ℝ)
  set D : ℝ := (L.polarRealDeterminantScale : ℝ)
  set Γ := Real.Gamma (((m : ℝ) + 1) / 2)
  have hΓN : Real.Gamma (((m + 1 : ℕ) : ℝ) / 2) = Γ := by push_cast; rfl
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos (by positivity)
  have hD : 0 < D := by
    change 0 < Real.sqrt _
    exact Real.sqrt_pos.mpr L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
  have heW : 0 < |eW| := abs_pos.mpr
    (Rat.cast_ne_zero.mpr (Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _))
  have hπN : Real.pi ^ (((m + 1 : ℕ) : ℝ) / 2) = Real.pi ^ (((m : ℝ) + 1) / 2) := by
    push_cast; rfl
  have hc0 : ENNReal.ofReal (|eW| * Γ) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hR0 : 0 ≤ R := by rw [hRe]; positivity
  refine (ENNReal.mul_left_inj hc0 ENNReal.ofReal_ne_top).mp ?_
  calc _ = W.realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (R * (|eB| * 2 * Real.sqrt (a : ℝ) * Real.sqrt |dW| * D) * (|eW| * Γ)) := by
        rw [ENNReal.ofReal_mul' (p := R * _) (by positivity), ENNReal.ofReal_mul' (p := R) (by positivity)]
        ring
    _ = W.realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal ((|eB| * 2 * Real.sqrt (a : ℝ) ^ m * Real.sqrt |dW| *
          Real.pi ^ (((m : ℝ) + 1) / 2)) * (|eW| * Real.sqrt 2 ^ (m + 1))) := by
        congr 2
        rw [hRe, hΓN, Real.mul_rpow (by norm_num) Real.pi_pos.le, realShellFactor_sqrt_two_pow, hπN,
          ← realShellFactor_rpow_mul_sqrt ha' m]
        field_simp
    _ = _ := by
        rw [ENNReal.ofReal_mul' (by positivity), ← mul_assoc, ← hmass]
        ring

/-- The archimedean shell factor is rational: for the supplied presentation `P` of `L` at `x`,
`Re d_∞(Q x) · μ_W · (|e_B| · 2 · |det E| · det F_L) = μ_B · |e_W|`. -/
theorem ofReal_re_realLocalValueDensity_mul_realMass_eq_presentation
    (L : PositiveDefiniteIntegralLattice (m + 1)) {b : ℝ} (hb : 0 < b) (hm : 2 ≤ m) [NeZero m]
    {x : Fin (m + 1) → ℚ}
    (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
    (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
    (hW : (P.lowerSpace.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef)
    (ha0 : 0 < L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) :
    ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L b (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).re) *
        P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
              (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 *
          |(((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ)| *
          ((L.rationalQuadraticSpaceMatrix.pairingMatrix.det : ℚ) : ℝ)) =
      (P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal |(Matrix.skewAdjointFixedFormElementaryDetScalar
              P.lowerSpace.pairingMatrix P.lowerSpace.form_symm P.lowerSpace.form_det_ne_zero : ℝ)| := by
  set a := L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x
  have h := ofReal_re_realLocalValueDensity_mul_realMass_eq L hb hm P.lowerSpace hW hx ha0
  set dF : ℝ := ((L.rationalQuadraticSpaceMatrix.pairingMatrix.det : ℚ) : ℝ)
  set dE : ℝ := (((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ)
  set dW : ℝ := ((P.lowerSpace.pairingMatrix.det : ℚ) : ℝ)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha0
  -- `polarDeterminant L = det (2 F_L) = 2^(m+1) det F_L`
  have hpolar : L.rationalQuadraticSpaceMatrix.realPolarMatrix.det = 2 ^ (m + 1) * dF := by
    rw [realPolarMatrix_det, polarMatrix, Matrix.det_smul, Fintype.card_fin, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  have hdF : 0 < dF := by
    have := L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
    rw [hpolar] at this
    exact pos_of_mul_pos_right this (by positivity)
  have hsqrt2 : Real.sqrt (2 ^ (m + 1)) = Real.sqrt 2 ^ (m + 1) := by
    rw [show (2 : ℝ) ^ (m + 1) = (Real.sqrt 2 ^ (m + 1)) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
    exact Real.sqrt_sq (by positivity)
  have hD : (L.polarRealDeterminantScale : ℝ) = Real.sqrt 2 ^ (m + 1) * Real.sqrt dF := by
    change Real.sqrt _ = _
    rw [hpolar, Real.sqrt_mul (by positivity), hsqrt2]
  -- `a · det W = det F_B = (det E)² det F_L`
  have hcong := congrArg Matrix.det (P.blockToAmbientRationalMatrix_form_congruence hx)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hcong
  have hB : ((P.blockSpace hx).pairingMatrix.det : ℚ) = P.lowerSpace.pairingMatrix.det * a :=
    nonisotropicLastBlockMatrix_det _ _
  have hdet : dW * (a : ℝ) = dE ^ 2 * dF := by
    have : P.lowerSpace.pairingMatrix.det * a =
        (P.blockToAmbientRationalMatrix hx).det ^ 2 * L.rationalQuadraticSpaceMatrix.pairingMatrix.det := by
      rw [← hB, ← hcong]; ring
    have := congrArg (fun q : ℚ => (q : ℝ)) this
    simpa [dW, dE, dF] using this
  have hdW : 0 ≤ dW := by
    have : 0 ≤ dW * (a : ℝ) := by rw [hdet]; positivity
    exact nonneg_of_mul_nonneg_left this ha'
  have hroot : Real.sqrt (a : ℝ) * Real.sqrt |dW| = |dE| * Real.sqrt dF := by
    rw [abs_of_nonneg hdW, ← Real.sqrt_mul ha'.le, mul_comm, hdet,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  have hY : |(Matrix.skewAdjointFixedFormElementaryDetScalar (P.blockSpace hx).pairingMatrix
        (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 *
        Real.sqrt (a : ℝ) * Real.sqrt |dW| * (L.polarRealDeterminantScale : ℝ) =
      (|(Matrix.skewAdjointFixedFormElementaryDetScalar (P.blockSpace hx).pairingMatrix
        (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 * |dE| * dF) *
        Real.sqrt 2 ^ (m + 1) := by
    rw [hD, mul_assoc _ (Real.sqrt (a : ℝ)), hroot]
    have := Real.mul_self_sqrt hdF.le
    linear_combination (|(Matrix.skewAdjointFixedFormElementaryDetScalar
      (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
      (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 * |dE| * Real.sqrt 2 ^ (m + 1)) * this
  have hc : 0 < Real.sqrt 2 ^ (m + 1) := by positivity
  change _ * _ * ENNReal.ofReal (_ * 2 * Real.sqrt (a : ℝ) * Real.sqrt |dW| * _) = _ at h
  rw [hY, ENNReal.ofReal_mul' hc.le, ENNReal.ofReal_mul' hc.le, ← mul_assoc, ← mul_assoc] at h
  exact (ENNReal.mul_left_inj (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).mp h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
