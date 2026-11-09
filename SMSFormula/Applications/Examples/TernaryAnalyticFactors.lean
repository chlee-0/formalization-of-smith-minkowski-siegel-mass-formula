import SMSFormula.Applications.Examples.BinaryInstantiation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! Concrete special values for the product computations of the ternary example. -/

noncomputable section

namespace PositiveDefiniteIntegralLattice

theorem archimedeanMassFactor_three : archimedeanMassFactor 3 = (Real.pi ^ 2)⁻¹ := by
  have hg : Real.Gamma (3 / 2) = (1 / 2) * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num), Real.Gamma_one_half_eq]
  unfold archimedeanMassFactor
  norm_num [Finset.prod_range_succ, Real.Gamma_one, Real.Gamma_one_half_eq, hg,
    Real.rpow_neg, Real.rpow_natCast]
  field_simp [Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

theorem archimedeanMassFactor_four : archimedeanMassFactor 4 = (Real.pi ^ 4)⁻¹ := by
  have hg : Real.Gamma (3 / 2) = (1 / 2) * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num), Real.Gamma_one_half_eq]
  unfold archimedeanMassFactor
  norm_num [Finset.prod_range_succ, Real.Gamma_one, Real.Gamma_two,
    Real.Gamma_one_half_eq, hg, Real.rpow_neg, Real.rpow_natCast]
  field_simp [Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

end PositiveDefiniteIntegralLattice

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice

theorem zeta_two_real_value : (riemannZeta 2).re = Real.pi ^ 2 / 6 := by
  rw [riemannZeta_two]
  norm_num [pow_two, Complex.mul_re]

theorem ternary_badPrimes : massBadPrimeSet ternaryLattice =
    {⟨2, Nat.prime_two⟩, ⟨11, by decide⟩} := by
  ext p
  rw [mem_massBadPrimeSet_iff, ternaryLattice_polarDeterminant]
  change (p.val = 2 ∨ p.val ∣ 176) ↔ _
  have hd : p.val ∣ 176 ↔ p.val = 2 ∨ p.val = 11 := by
    have h176 : 176 = 2 * 2 * 2 * 2 * (11 : ℕ) := by norm_num
    rw [h176, p.prop.dvd_mul, p.prop.dvd_mul, p.prop.dvd_mul, p.prop.dvd_mul]
    have h2 : p.val ∣ 2 ↔ p.val = 2 :=
      Nat.dvd_prime Nat.prime_two |>.trans (by simp [p.prop.ne_one])
    have h11 : p.val ∣ 11 ↔ p.val = 11 :=
      Nat.dvd_prime (by decide : Nat.Prime 11) |>.trans (by simp [p.prop.ne_one])
    rw [h2, h11]
    tauto
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, hd]
  tauto

theorem primesBelow_twelve : (12 : ℕ).primesBelow = {2, 3, 5, 7, 11} := by decide

theorem coreEulerProduct_cutoff_eleven :
    goodPrimeEulerCoreInverseProduct (rationalPrimesUpTo 11) 1 = (29645 / 18432 : ℝ) := by
  rw [goodPrimeEulerCoreInverseProduct_eq_primesBelow]
  norm_num only [Nat.reduceAdd]
  rw [primesBelow_twelve]
  norm_num [Real.rpow_neg_natCast]

theorem ternary_zetaTail_eleven :
    goodPrimeEulerCoreZetaTailFactor 11 1 = (3072 / 29645 : ℝ) * Real.pi ^ 2 := by
  unfold goodPrimeEulerCoreZetaTailFactor
  norm_num only [Nat.reduceMul, Nat.cast_ofNat, Complex.ofReal_ofNat]
  rw [zeta_two_real_value, coreEulerProduct_cutoff_eleven]
  ring

end MassFormulaReleaseExamples
