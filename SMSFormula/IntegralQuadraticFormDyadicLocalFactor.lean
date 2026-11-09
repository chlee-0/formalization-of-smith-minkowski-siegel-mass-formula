import SMSFormula.IntegralQuadraticFormDyadicDepthShift
import SMSFormula.PadicCayleyTangentNorm

/-!
# Direct local factor of the integral quadratic form at the dyadic prime

This file combines the certified one-step quotient-count shift with the
source normalization and the polar-Gram determinant factor.  Every power of
two is retained explicitly until the rational depth correction cancels the
dyadic determinant correction.
-/

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-- The tangent-dimension exponent added by one density depth. -/
def dyadicTangentExponent (n : ℕ) : ℕ := n * (n - 1) / 2

/-- The local-density denominator exponent increases by the tangent
dimension at the next depth. -/
theorem localDensityDenominatorExponent_succ (n k : ℕ) :
    PositiveDefiniteIntegralLattice.localDensityDenominatorExponent n (k + 1) =
      PositiveDefiniteIntegralLattice.localDensityDenominatorExponent n k +
        dyadicTangentExponent n := by
  unfold PositiveDefiniteIntegralLattice.localDensityDenominatorExponent
    dyadicTangentExponent
  rw [Nat.add_mul]
  simp

/-- The direct finite dyadic density before the polar determinant factor.
The source `|2|_2^{-n}` normalization remains visible. -/
noncomputable def dyadicDirectFixedKDensityFactor (k : ℕ) : ℚ :=
  (1 / 2 : ℚ) *
    PositiveDefiniteIntegralLattice.twoPadicNormInvPow 2 n *
    ((2 : ℚ) ^
      PositiveDefiniteIntegralLattice.localDensityDenominatorExponent n k)⁻¹ *
    (H.polarDualQuotientCount 2 k : ℚ)

/-- The direct rational factor at depth `k` is the integral model rational factor at
depth `k+1` times exactly the tangent power of two. -/
theorem dyadicDirectFixedKDensityFactor_eq_two_pow_mul_latticeOfPolarForm_succ
    (k : ℕ)
    (hk : PositiveDefiniteIntegralLattice.IsLocalDensityHenselExponent
      H.latticeOfPolarForm 2 (k + 1)) :
    H.dyadicDirectFixedKDensityFactor k =
      (2 : ℚ) ^ dyadicTangentExponent n *
        PositiveDefiniteIntegralLattice.fixedKDensityFactor
          H.latticeOfPolarForm 2 (k + 1) := by
  unfold dyadicDirectFixedKDensityFactor
  rw [PositiveDefiniteIntegralLattice.fixedKDensityFactor_eq_associatedBilinearDualQuotientCount
    H.latticeOfPolarForm 2 (k + 1) hk]
  rw [← H.polarDualQuotientCount_eq_latticeOfPolarForm_associated_succ_dyadic k]
  rw [PositiveDefiniteIntegralLattice.twoPadicNormInvPow_eq_two_pow]
  rw [localDensityDenominatorExponent_succ n k, pow_add]
  field_simp
  ring

/-- The dyadic norm of the integral model polar discriminant is the norm of `det(A)`
divided by `2^n`. -/
theorem latticeOfPolarForm_polarDeterminant_padicNorm_dyadic :
    ‖(H.latticeOfPolarForm.polarDeterminant : ℤ_[2])‖ =
      ((2 : ℝ) ^ n)⁻¹ * ‖(H.polarDeterminant : ℤ_[2])‖ := by
  rw [H.latticeOfPolarForm_polarDeterminant_eq_two_pow_mul_polarDeterminant]
  push_cast
  have hnormTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    exact @PadicInt.norm_p 2 inferInstance
  rw [norm_mul, norm_pow, hnormTwo]
  rw [inv_pow]

/-- Natural tangent dimension as the corresponding real half-product. -/
theorem dyadicTangentExponent_cast (n : ℕ) :
    (dyadicTangentExponent n : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  by_cases hn : n = 0
  · simp [hn, dyadicTangentExponent]
  have hn_one : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  have hhalf :
      dyadicTangentExponent n + dyadicTangentExponent n = n * (n - 1) := by
    have h := Nat.div_two_mul_two_of_even heven
    unfold dyadicTangentExponent
    omega
  have hhalf_real := congrArg (fun m : ℕ => (m : ℝ)) hhalf
  push_cast at hhalf_real
  rw [Nat.cast_sub hn_one] at hhalf_real
  norm_num at hhalf_real ⊢
  nlinarith

/-- The determinant scaling contributes precisely the same tangent power that
appears in the rational depth shift. -/
theorem latticeOfPolarForm_gramDetFactor_eq_two_pow_mul_polarGramDetFactor :
    PositiveDefiniteIntegralLattice.gramDetPadicNormFactor
        H.latticeOfPolarForm 2 =
      (2 : ℝ) ^ dyadicTangentExponent n *
        H.polarGramDetPadicNormFactor 2 := by
  unfold PositiveDefiniteIntegralLattice.gramDetPadicNormFactor
    polarGramDetPadicNormFactor
  rw [H.latticeOfPolarForm_polarDeterminant_padicNorm_dyadic]
  rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hcoeff :
      (((2 : ℝ) ^ n)⁻¹) ^ (((1 : ℝ) - (n : ℝ)) / 2) =
        (2 : ℝ) ^ dyadicTangentExponent n := by
    rw [Real.inv_rpow (by positivity)]
    rw [← Real.rpow_neg (by positivity)]
    rw [← Real.rpow_natCast (2 : ℝ) n]
    rw [← Real.rpow_mul (by positivity)]
    rw [← Real.rpow_natCast (2 : ℝ) (dyadicTangentExponent n)]
    congr 1
    rw [dyadicTangentExponent_cast]
    ring
  rw [hcoeff]

/-- The complete direct dyadic factor, including the norm of the integral
polar Gram determinant `det(A)`. -/
noncomputable def dyadicDirectFixedKDensityWithPolarDetFactor (k : ℕ) : ℝ :=
  (H.dyadicDirectFixedKDensityFactor k : ℝ) *
    H.polarGramDetPadicNormFactor 2

/-- After separately accounting for the depth shift and determinant norm, the
complete direct dyadic factor is literally the integral model factor at depth `k+1`.
-/
theorem dyadicDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm_succ
    (k : ℕ)
    (hk : PositiveDefiniteIntegralLattice.IsLocalDensityHenselExponent
      H.latticeOfPolarForm 2 (k + 1)) :
    H.dyadicDirectFixedKDensityWithPolarDetFactor k =
      PositiveDefiniteIntegralLattice.fixedKDensityWithGramDetFactor
        H.latticeOfPolarForm 2 (k + 1) := by
  rw [dyadicDirectFixedKDensityWithPolarDetFactor,
    PositiveDefiniteIntegralLattice.fixedKDensityWithGramDetFactor,
    H.dyadicDirectFixedKDensityFactor_eq_two_pow_mul_latticeOfPolarForm_succ k hk,
    H.latticeOfPolarForm_gramDetFactor_eq_two_pow_mul_polarGramDetFactor]
  push_cast
  ring

/-- At every direct depth whose shifted integral model depth is in the quantitative
Hensel range, the intrinsic `Q_H`/`A`-dual dyadic factor equals the established
stable integral model alpha.  The direct side remains its finite-count definition. -/
theorem dyadicDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm_alpha
    (k : ℕ)
    (hk : PositiveDefiniteIntegralLattice.IsLocalDensityHenselExponent
      H.latticeOfPolarForm 2 (k + 1)) :
    H.dyadicDirectFixedKDensityWithPolarDetFactor k =
      PositiveDefiniteIntegralLattice.normalizedLocalDensity H.latticeOfPolarForm 2 := by
  calc
    H.dyadicDirectFixedKDensityWithPolarDetFactor k =
        PositiveDefiniteIntegralLattice.fixedKDensityWithGramDetFactor
          H.latticeOfPolarForm 2 (k + 1) :=
      H.dyadicDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm_succ k hk
    _ = PositiveDefiniteIntegralLattice.normalizedLocalDensityAtExponent
          H.latticeOfPolarForm 2 (k + 1) hk.admissible := rfl
    _ = PositiveDefiniteIntegralLattice.normalizedLocalDensity H.latticeOfPolarForm 2 :=
      (PositiveDefiniteIntegralLattice.normalizedLocalDensity_eq_fixedK
        H.latticeOfPolarForm 2 (k + 1) hk).symm

/-! ## Canonical direct dyadic alpha -/

/-- A canonical direct depth, one below the scaled integral model's preferred source
depth, as dictated by the proved dyadic shift. -/
def dyadicDirectHenselExponent : ℕ :=
  PositiveDefiniteIntegralLattice.localDensityHenselExponent H.latticeOfPolarForm 2 - 1

theorem dyadicDirectHenselExponent_succ :
    H.dyadicDirectHenselExponent + 1 =
      PositiveDefiniteIntegralLattice.localDensityHenselExponent H.latticeOfPolarForm 2 := by
  unfold dyadicDirectHenselExponent PositiveDefiniteIntegralLattice.localDensityHenselExponent
  omega

/-- The intrinsic dyadic local density, defined from the direct `Q_H`
solution-family count at the canonical shifted depth and from `det(A)`. -/
noncomputable def dyadicNormalizedLocalDensity : ℝ :=
  H.dyadicDirectFixedKDensityWithPolarDetFactor H.dyadicDirectHenselExponent

/-- The canonical direct dyadic alpha equals the scaled-integral model alpha only
after the finite depth, norm, and power-of-two comparisons above. -/
theorem dyadicNormalizedLocalDensity_eq_latticeOfPolarForm :
    H.dyadicNormalizedLocalDensity =
      PositiveDefiniteIntegralLattice.normalizedLocalDensity H.latticeOfPolarForm 2 := by
  unfold dyadicNormalizedLocalDensity
  apply H.dyadicDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm_alpha
  rw [H.dyadicDirectHenselExponent_succ]
  exact PositiveDefiniteIntegralLattice.isLocalDensityHenselExponent_preferred
    H.latticeOfPolarForm 2

theorem dyadicNormalizedLocalDensity_pos : 0 < H.dyadicNormalizedLocalDensity := by
  rw [H.dyadicNormalizedLocalDensity_eq_latticeOfPolarForm]
  exact PositiveDefiniteIntegralLattice.normalizedLocalDensity_pos H.latticeOfPolarForm 2

end PositiveDefiniteIntegralQuadraticForm

end
