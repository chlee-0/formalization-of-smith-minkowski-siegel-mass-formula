import SMSFormula.PadicSpecialOrthogonalDifferentialLocalCorrectionProductFormula
import SMSFormula.SpecialOrthogonalRealLatticeDifferentialMass
import SMSFormula.Product

/-!
# Real Gamma and archimedean normalization

This module combines the elementary real special-orthogonal Gamma factor with
the Schulze--Pillot archimedean factor.  It then inserts the closed tangent
determinant composition into the lattice real differential mass and reduces
the remaining global normalization statement to a literal bad-prime identity.

No bad-prime identity, quotient source, reference Haar comparison, or
Tamagawa value is proved here.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The elementary real special-orthogonal Gamma factor in matrix rank `n`. -/
def specialOrthogonalRealGammaFactor (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n - 1) *
      Real.pi ^
        (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) + 3) / 4) /
    (∏ k ∈ Finset.range (n - 1),
      Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))

/-- The elementary Gamma factor is positive. -/
theorem specialOrthogonalRealGammaFactor_pos (n : ℕ) :
    0 < specialOrthogonalRealGammaFactor n := by
  unfold specialOrthogonalRealGammaFactor
  positivity

/-- The elementary real Gamma factor and the Schulze--Pillot archimedean
factor cancel to the exact power `2^n`. -/
theorem specialOrthogonalRealGammaFactor_mul_archimedeanMassFactor
    (n : ℕ) [NeZero n] :
    specialOrthogonalRealGammaFactor n *
        archimedeanMassFactor n = (2 : ℝ) ^ n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      unfold specialOrthogonalRealGammaFactor
      unfold archimedeanMassFactor
      simp only [Nat.succ_sub_one]
      rw [Finset.prod_range_succ']
      simp only [Nat.zero_add, Nat.cast_one, one_div]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      rw [Real.Gamma_one_half_eq]
      have hprod :
          (∏ k ∈ Finset.range m,
              Real.Gamma (((k + 1 + 1 : ℕ) : ℝ) / 2)) =
            ∏ k ∈ Finset.range m,
              Real.Gamma (((k + 2 : ℕ) : ℝ) / 2) := by
        apply Finset.prod_congr rfl
        intro k hk
        congr 3
      rw [hprod]
      let G : ℝ := ∏ k ∈ Finset.range m,
        Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)
      have hG_pos : 0 < G := by
        dsimp only [G]
        positivity
      have hpi :
          Real.pi ^ ((m : ℝ) * ((m : ℝ) + 3) / 4) *
              Real.pi.rpow
                (-(((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
              Real.sqrt Real.pi = 1 := by
        rw [Real.sqrt_eq_rpow]
        change
          Real.pi.rpow ((m : ℝ) * ((m : ℝ) + 3) / 4) *
                Real.pi.rpow
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
              Real.pi.rpow (1 / 2) = 1
        have hexp :
            (m : ℝ) * ((m : ℝ) + 3) / 4 +
                (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ)) = 0 := by
          push_cast
          ring
        have hbc :
            Real.pi.rpow
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
                Real.pi.rpow (1 / 2) =
              Real.pi.rpow
                (-(((m + 1 : ℕ) : ℝ) *
                  (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ)) := by
          change
            Real.pi ^
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
                Real.pi ^ (1 / 2 : ℝ) =
              Real.pi ^
                (-(((m + 1 : ℕ) : ℝ) *
                  (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ))
          exact (Real.rpow_add Real.pi_pos _ _).symm
        have habc :
            Real.pi.rpow ((m : ℝ) * ((m : ℝ) + 3) / 4) *
                Real.pi.rpow
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ)) =
              Real.pi.rpow
                ((m : ℝ) * ((m : ℝ) + 3) / 4 +
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ))) := by
          change
            Real.pi ^ ((m : ℝ) * ((m : ℝ) + 3) / 4) *
                Real.pi ^
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ)) =
              Real.pi ^
                ((m : ℝ) * ((m : ℝ) + 3) / 4 +
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ)))
          exact (Real.rpow_add Real.pi_pos _ _).symm
        calc
          Real.pi.rpow ((m : ℝ) * ((m : ℝ) + 3) / 4) *
                Real.pi.rpow
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
              Real.pi.rpow (1 / 2) =
              Real.pi.rpow ((m : ℝ) * ((m : ℝ) + 3) / 4) *
              Real.pi.rpow
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ)) := by
                    rw [mul_assoc]
                    exact congrArg
                      (fun x : ℝ =>
                        Real.pi.rpow ((m : ℝ) * ((m : ℝ) + 3) / 4) * x) hbc
          _ =
              Real.pi.rpow
                ((m : ℝ) * ((m : ℝ) + 3) / 4 +
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4) + (1 / 2 : ℝ))) := by
                    exact habc
          _ = 1 := by
            rw [hexp]
            change Real.pi ^ (0 : ℝ) = 1
            exact Real.rpow_zero Real.pi
      change
        ((2 : ℝ) ^ m *
              Real.pi ^ ((m : ℝ) * ((m : ℝ) + 3) / 4) / G) *
            (2 * Real.pi.rpow
                (-(((m + 1 : ℕ) : ℝ) *
                  (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
              (G * Real.sqrt Real.pi)) =
          (2 : ℝ) ^ (m + 1)
      calc
        ((2 : ℝ) ^ m *
              Real.pi ^ ((m : ℝ) * ((m : ℝ) + 3) / 4) / G) *
            (2 * Real.pi.rpow
                (-(((m + 1 : ℕ) : ℝ) *
                  (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
              (G * Real.sqrt Real.pi)) =
            ((2 : ℝ) ^ m * 2) *
              (Real.pi ^ ((m : ℝ) * ((m : ℝ) + 3) / 4) *
                Real.pi.rpow
                  (-(((m + 1 : ℕ) : ℝ) *
                    (((m + 1 : ℕ) : ℝ) + 1) / 4)) *
                Real.sqrt Real.pi) := by
                  field_simp [ne_of_gt hG_pos]
        _ = (2 : ℝ) ^ (m + 1) := by
          rw [hpi, mul_one, pow_succ]

/-- The closed tangent determinant composition converts the three real
determinant scales, the elementary Gamma factor, and the archimedean factor
into the rational comparison determinant and the form determinant. -/
theorem skewAdjointRealDeterminantGammaArchimedeanFactor_closed
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : Matrix.skewAdjointCongruenceForm F W = Matrix.diagonal d)
    [NeZero n] :
    (|Matrix.skewAdjointRealCongruenceDetScalar F W|⁻¹ *
        (|positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ *
          (|(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
            specialOrthogonalRealGammaFactor n))) *
        archimedeanMassFactor n =
      |(Matrix.skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)| *
        ((2 : ℝ) ^ n *
          (Real.sqrt |((F.det : ℚ) : ℝ)|) ^ (n - 1)) := by
  let A : ℝ := |Matrix.skewAdjointRealCongruenceDetScalar F W|
  let B : ℝ := |positiveDiagonalSkewAdjointDetScalar d hd|
  let C : ℝ := |(Matrix.skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)|
  let I : ℝ := |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)|
  let s : ℝ := Real.sqrt |((F.det : ℚ) : ℝ)|
  have hA : A ≠ 0 := by
    exact abs_ne_zero.mpr (Matrix.skewAdjointRealCongruenceDetScalar_ne_zero F W)
  have hB : B ≠ 0 := by
    exact abs_ne_zero.mpr (positiveDiagonalSkewAdjointDetScalar_ne_zero d hd)
  have hC : C ≠ 0 := by
    exact abs_ne_zero.mpr (by
      exact_mod_cast Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet)
  have hI : I ≠ 0 := by
    exact abs_ne_zero.mpr (by
      exact_mod_cast identitySpecialOrthogonalFixedElementaryDetScalar_ne_zero n)
  have hs : s ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact abs_pos.mpr (by exact_mod_cast hdet)
  have hclosed : A * (B * C) = I * s⁻¹ ^ (n - 1) := by
    exact Matrix.skewAdjointRealCongruence_positiveDiagonal_abs_det_composition_closed
      F hF hdet W d hd hdiag
  have hratio : I / (A * B) = C * s ^ (n - 1) := by
    apply (div_eq_iff (mul_ne_zero hA hB)).2
    calc
      I = I * (s⁻¹ ^ (n - 1) * s ^ (n - 1)) := by
        rw [← mul_pow, inv_mul_cancel₀ hs, one_pow, mul_one]
      _ = (I * s⁻¹ ^ (n - 1)) * s ^ (n - 1) := by ring
      _ = (A * (B * C)) * s ^ (n - 1) := by rw [hclosed]
      _ = (C * s ^ (n - 1)) * (A * B) := by ring
  have hgamma :=
    specialOrthogonalRealGammaFactor_mul_archimedeanMassFactor n
  change (A⁻¹ * (B⁻¹ * (I * specialOrthogonalRealGammaFactor n))) *
      archimedeanMassFactor n = C * ((2 : ℝ) ^ n * s ^ (n - 1))
  calc
    (A⁻¹ * (B⁻¹ * (I * specialOrthogonalRealGammaFactor n))) *
          archimedeanMassFactor n =
        (I / (A * B)) *
          (specialOrthogonalRealGammaFactor n *
            archimedeanMassFactor n) := by
              field_simp [hA, hB]
    _ = C * ((2 : ℝ) ^ n * s ^ (n - 1)) := by rw [hratio, hgamma]; ring

/-- Multiplying the lattice real differential mass by the archimedean factor
gives the rational comparison determinant, the power of two, and the form
determinant, with the whole expression still inside `ENNReal.ofReal`. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_univ_mul_archimedeanFactor
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        ENNReal.ofReal (archimedeanMassFactor n) =
      ENNReal.ofReal
        (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              L.rationalFormMatrix (L.form_symm.map _)
                L.rationalFormMatrix_det_ne_zero : ℝ)| *
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1))) := by
  obtain ⟨d, W, hd, hdiag, hmass⟩ :=
    L.exists_concreteRealSpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma
  rw [hmass]
  have hcong :
      (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar
            L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) =
        ENNReal.ofReal
          |Matrix.skewAdjointRealCongruenceDetScalar
            L.rationalFormMatrix W|⁻¹ := by
    simp only [ENNReal.ofReal]
    congr
    rw [Real.toNNReal_inv]
  have hdiagScale :
      (↑((Real.toNNReal |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) :
          ℝ≥0∞) =
        ENNReal.ofReal |positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ := by
    simp only [ENNReal.ofReal]
    congr
    rw [Real.toNNReal_inv]
  rw [hcong, hdiagScale]
  change
    (ENNReal.ofReal
        |Matrix.skewAdjointRealCongruenceDetScalar L.rationalFormMatrix W|⁻¹ *
      (ENNReal.ofReal |positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ *
        (ENNReal.ofReal
            |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
          ENNReal.ofReal (specialOrthogonalRealGammaFactor n)))) *
        ENNReal.ofReal (archimedeanMassFactor n) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg
    (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ))]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr
    (abs_nonneg (positiveDiagonalSkewAdjointDetScalar d hd)))]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr
    (abs_nonneg (Matrix.skewAdjointRealCongruenceDetScalar
      L.rationalFormMatrix W)))]
  have hreal_nonneg :
      0 ≤ |Matrix.skewAdjointRealCongruenceDetScalar L.rationalFormMatrix W|⁻¹ *
        (|positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ *
          (|(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
            specialOrthogonalRealGammaFactor n)) := by
    exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
        (mul_nonneg (abs_nonneg _)
          (le_of_lt (specialOrthogonalRealGammaFactor_pos n))))
  rw [← ENNReal.ofReal_mul hreal_nonneg]
  exact congrArg ENNReal.ofReal
    (skewAdjointRealDeterminantGammaArchimedeanFactor_closed
      L.rationalFormMatrix (L.form_symm.map _) L.rationalFormMatrix_det_ne_zero
      W d hd hdiag)

/-- After the real Gamma cancellation and the rational norm product formula,
the global differential normalization has only the form-determinant factor
and the literal bad-prime correction/norm ratio left. -/
theorem
    realDifferentialMass_mul_archimedean_mul_localCorrection_eq_formFactor_mul_badPrimeRatio
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (ENNReal.ofReal (archimedeanMassFactor n) *
          L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) =
      ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        (L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
          L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹) := by
  rw [← mul_assoc]
  rw [L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_mul_archimedeanFactor]
  rw [ENNReal.ofReal_mul (abs_nonneg
    ((Matrix.skewAdjointFixedFormElementaryDetScalar
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero : ℚ) : ℝ))]
  calc
    _ = ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        (ENNReal.ofReal
            |((Matrix.skewAdjointFixedFormElementaryDetScalar
              L.rationalFormMatrix (L.form_symm.map _)
                L.rationalFormMatrix_det_ne_zero : ℚ) : ℝ)| *
          L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) := by
            ac_rfl
    _ = _ := by
      rw [L.ofReal_abs_skewAdjointFixedFormElementaryDetScalar_mul_localCorrectionFiniteProduct_eq_badPrimeCorrection_mul_inv_badComparisonNorm]

/-- The desired global differential normalization is exactly equivalent to
the remaining explicit bad-prime identity. -/
theorem globalDifferentialNormalization_iff_badPrimeIdentity
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] (P : ℝ) :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
          (ENNReal.ofReal (archimedeanMassFactor n) *
            L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P ↔
      ENNReal.ofReal
            ((2 : ℝ) ^ n *
              (Real.sqrt
                |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
          (L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
            L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹) =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  rw [L.realDifferentialMass_mul_archimedean_mul_localCorrection_eq_formFactor_mul_badPrimeRatio]

end PositiveDefiniteIntegralLattice
