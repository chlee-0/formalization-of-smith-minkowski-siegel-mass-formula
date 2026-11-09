import SMSFormula.Genus
import SMSFormula.Applications.Unimodular.PadicLifting.CompactLift
import SMSFormula.Applications.Unimodular.PadicLifting.IntegralIteration

noncomputable section

namespace UnimodularPadicLift
open scoped BigOperators

variable {p n : ℕ} [Fact p.Prime]

theorem natCast_mul_matrix (coefficient : ℕ) (matrix : Mat p n) :
    (coefficient : Mat p n) * matrix = (coefficient : ℤ_[p]) • matrix := by
  ext row col
  simp [Matrix.mul_apply, Matrix.natCast_apply]

theorem powDiv_iff_smul (precision : ℕ) (matrix : Mat p n) :
    PowDiv precision matrix ↔ ∃ factor : Mat p n, matrix = (p : ℤ_[p]) ^ precision • factor := by
  constructor
  · intro hmatrix
    choose factor hfactor using hmatrix
    exact ⟨factor, by ext row col; exact hfactor row col⟩
  · rintro ⟨factor, rfl⟩ row col
    exact ⟨factor row col, rfl⟩

theorem powDiv_mul_left {precision : ℕ} {matrix : Mat p n}
    (left : Mat p n) (hmatrix : PowDiv precision matrix) :
    PowDiv precision (left * matrix) := by
  obtain ⟨factor, rfl⟩ := (powDiv_iff_smul _ _).mp hmatrix
  exact (powDiv_iff_smul _ _).mpr ⟨left * factor, by rw [Matrix.mul_smul]⟩

theorem powDiv_mul_right {precision : ℕ} {matrix : Mat p n}
    (right : Mat p n) (hmatrix : PowDiv precision matrix) :
    PowDiv precision (matrix * right) := by
  obtain ⟨factor, rfl⟩ := (powDiv_iff_smul _ _).mp hmatrix
  exact (powDiv_iff_smul _ _).mpr ⟨factor * right, by rw [Matrix.smul_mul]⟩

theorem powDiv_smul {precision : ℕ} {matrix : Mat p n}
    (coefficient : ℤ_[p]) (hmatrix : PowDiv precision matrix) :
    PowDiv precision (coefficient • matrix) := by
  obtain ⟨factor, rfl⟩ := (powDiv_iff_smul _ _).mp hmatrix
  exact (powDiv_iff_smul _ _).mpr ⟨coefficient • factor, by
    simp only [smul_smul, mul_comm]⟩

theorem powDiv_of_natCast_factor {precision : ℕ} {matrix factor : Mat p n}
    (hfactor : matrix = (p : Mat p n) ^ precision * factor) : PowDiv precision matrix := by
  apply (powDiv_iff_smul _ _).mpr
  refine ⟨factor, ?_⟩
  simpa only [← Nat.cast_pow, natCast_mul_matrix] using hfactor

theorem integralIterate_selfAdjoint (gram coefficient : Mat p n)
    (hcoefficient : coefficient.transpose * gram = gram * coefficient) (step : ℕ) :
    (integralIterate p coefficient step).transpose * gram =
      gram * integralIterate p coefficient step := by
  induction step with
  | zero => simp [integralIterate]
  | succ step ih =>
    rw [integralIterate, natCast_mul_matrix]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hcoefficient]
    congr 1
    rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

def integralCorrection (step : ℕ) (coefficient : Mat p n) : Mat p n :=
  1 + (2 * (p : ℤ_[p])) • integralIterate p coefficient step

def integralCorrectionInverse (step : ℕ) (coefficient : Mat p n) : Mat p n :=
  geometricInverse (-(2 * (p : ℤ_[p])) • integralIterate p coefficient step) (step + 1)

theorem correction_gram_defect (gram target coefficient iterate : Mat p n)
    (hself : iterate.transpose * gram = gram * iterate)
    (htarget : target = gram + (4 * (p : ℤ_[p])) • (gram * coefficient)) :
    (1 + (2 * (p : ℤ_[p])) • iterate).transpose * gram *
        (1 + (2 * (p : ℤ_[p])) • iterate) - target =
      (4 * (p : ℤ_[p])) •
        (gram * (iterate + (p : ℤ_[p]) • (iterate * iterate) - coefficient)) := by
  rw [htarget]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hself, Matrix.mul_sub, Matrix.mul_assoc]
  module

theorem integralCorrection_gram_powDiv (gram target coefficient : Mat p n)
    (hself : coefficient.transpose * gram = gram * coefficient)
    (htarget : target = gram + (4 * (p : ℤ_[p])) • (gram * coefficient)) (step : ℕ) :
    PowDiv step ((integralCorrection step coefficient).transpose * gram *
      integralCorrection step coefficient - target) := by
  rw [integralCorrection, correction_gram_defect gram target coefficient _
    (integralIterate_selfAdjoint gram coefficient hself step) htarget]
  apply powDiv_smul
  apply powDiv_mul_left
  obtain ⟨factor, hfactor⟩ := integralIterate_defect_factor p coefficient step
  apply powDiv_of_natCast_factor (factor := factor)
  simpa only [natCast_mul_matrix] using hfactor

theorem powDiv_geometric_error (iterate : Mat p n) (step : ℕ) :
    PowDiv step ((-(2 * (p : ℤ_[p])) • iterate) ^ (step + 1)) := by
  have hfactor : -(2 * (p : ℤ_[p])) • iterate =
      (p : Mat p n) * ((-2 : ℤ_[p]) • iterate) := by
    rw [natCast_mul_matrix, smul_smul]
    congr 1
    ring
  rw [hfactor, (Nat.cast_commute p ((-2 : ℤ_[p]) • iterate)).mul_pow]
  exact powDiv_mono (Nat.le_succ step) (powDiv_of_natCast_factor rfl)

theorem integralCorrection_inverse_powDiv (step : ℕ) (coefficient : Mat p n) :
    PowDiv step (integralCorrection step coefficient *
      integralCorrectionInverse step coefficient - 1) ∧
    PowDiv step (integralCorrectionInverse step coefficient *
      integralCorrection step coefficient - 1) := by
  have hchange : integralCorrection step coefficient =
      1 - (-(2 * (p : ℤ_[p])) • integralIterate p coefficient step) := by
    simp [integralCorrection]
  constructor
  · rw [hchange, integralCorrectionInverse, geometricInverse_left]
    have heq : 1 - (-(2 * (p : ℤ_[p])) • integralIterate p coefficient step) ^
        (step + 1) - 1 =
        (-1 : ℤ_[p]) •
          ((-(2 * (p : ℤ_[p])) • integralIterate p coefficient step) ^ (step + 1)) := by
      simp
    rw [heq]
    exact powDiv_smul _ (powDiv_geometric_error _ step)
  · rw [hchange, integralCorrectionInverse, geometricInverse_right]
    have heq : 1 - (-(2 * (p : ℤ_[p])) • integralIterate p coefficient step) ^
        (step + 1) - 1 =
        (-1 : ℤ_[p]) •
          ((-(2 * (p : ℤ_[p])) • integralIterate p coefficient step) ^ (step + 1)) := by
      simp
    rw [heq]
    exact powDiv_smul _ (powDiv_geometric_error _ step)

theorem exists_unit_isometry_of_selfAdjoint_factor (gram target coefficient : Mat p n)
    (hself : coefficient.transpose * gram = gram * coefficient)
    (htarget : target = gram + (4 * (p : ℤ_[p])) • (gram * coefficient)) :
    ∃ change : Mat p n, IsUnit change ∧ change.transpose * gram * change = target := by
  apply exists_unit_gram_isometry_of_all_precisions
  intro step
  refine ⟨integralCorrection step coefficient, integralCorrectionInverse step coefficient,
    integralCorrection_gram_powDiv gram target coefficient hself htarget step, ?_⟩
  exact integralCorrection_inverse_powDiv step coefficient

theorem exists_unit_isometry_of_four_prime_dvd (gram target : Mat p n)
    (hgramSymm : gram.IsSymm) (htargetSymm : target.IsSymm) (hgram : IsUnit gram)
    (herror : ∀ row col, 4 * (p : ℤ_[p]) ∣ (target - gram) row col) :
    ∃ change : Mat p n, IsUnit change ∧ change.transpose * gram * change = target := by
  choose factor hfactor using herror
  change Mat p n at factor
  have hmatrix : target - gram = (4 * (p : ℤ_[p])) • factor := by
    ext row col
    exact hfactor row col
  have hnonzero : (4 * (p : ℤ_[p])) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hfactorSymm : factor.IsSymm := by
    have htranspose := congrArg Matrix.transpose hmatrix
    simp only [Matrix.transpose_sub, Matrix.transpose_smul,
      hgramSymm.eq, htargetSymm.eq] at htranspose
    have heq := htranspose.symm.trans hmatrix
    change factor.transpose = factor
    ext row col
    exact mul_left_cancel₀ hnonzero (congrFun (congrFun heq row) col)
  have hdet : IsUnit gram.det := (Matrix.isUnit_iff_isUnit_det gram).mp hgram
  apply exists_unit_isometry_of_selfAdjoint_factor gram target (gram⁻¹ * factor)
  · calc
      (gram⁻¹ * factor).transpose * gram = factor * (gram⁻¹ * gram) := by
        rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hgramSymm.eq,
          hfactorSymm.eq, Matrix.mul_assoc]
      _ = factor := by rw [Matrix.nonsing_inv_mul gram hdet, Matrix.mul_one]
      _ = gram * (gram⁻¹ * factor) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv gram hdet, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv gram hdet, Matrix.one_mul]
    have heq := sub_eq_iff_eq_add.mp hmatrix
    simpa only [add_comm] using heq

#assert_standard_axioms integralIterate_selfAdjoint
#assert_standard_axioms integralCorrection_gram_powDiv
#assert_standard_axioms integralCorrection_inverse_powDiv
#assert_standard_axioms exists_unit_isometry_of_selfAdjoint_factor
#assert_standard_axioms exists_unit_isometry_of_four_prime_dvd

end UnimodularPadicLift
