import SMSFormula.Applications.Examples.Inputs
import SMSFormula.LocalDensity
import SMSFormula.StandardAxiomsGuard

/-! Native depths and coordinate denominators for the determinant-22 example. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

theorem ternary_pairingDeterminant_val_two :
    padicValInt 2 ternaryLattice.pairingDeterminant = 1 := by
  have hself : padicValInt 2 (2 : ℤ) = 1 := padicValInt_self
  rw [ternaryLattice_pairingDeterminant,
    show (22 : ℤ) = 2 * 11 by norm_num,
    padicValInt.mul (by norm_num : (2 : ℤ) ≠ 0) (by norm_num : (11 : ℤ) ≠ 0),
    hself, padicValInt.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℤ) ∣ 11)]

theorem ternary_dyadic_hensel_four : IsLocalDensityHenselExponent ternaryLattice 2 4 := by
  have h2 := ternaryLattice.isHenselQuadraticDepth_of_pairingDeterminant_val_lt 2 2
    (by rw [ternary_pairingDeterminant_val_two]; decide)
  exact
    { admissible := isLocalDensityAdmissibleExponent_of_one_le _ _ _ (by decide)
      lattice_depth := ternaryLattice.isHenselLatticeDepth_of_pairingDeterminant_val_lt 2 4
        (by rw [ternary_pairingDeterminant_val_two]; decide)
      quadratic_depth := ternaryLattice.isHenselQuadraticDepth_of_pairingDeterminant_val_lt 2 4
        (by rw [ternary_pairingDeterminant_val_two]; decide)
      associated_bilinear_quadratic_depth := h2.associatedBilinear_add_two_dyadic _ 2 }

theorem ternary_associated_denominator_two_four :
    ternaryLattice.associatedBilinearDualPadicDenominatorIntegralPreimage 2 4 =
      diagonalPrimePowCoordinateSubmodule (n := 3) 2 4 ![1, 2, 1] := by
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker]
  have hmatrix : ternaryLattice.polarGramMatrix =
      Matrix.diagonal (fun i : Fin 3 => (![1, 1, 11] i : ℤ) * (2 ^ (![1, 2, 1] i) : ℤ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ternaryLattice, polarGramMatrix, Matrix.diagonal_apply]
  rw [hmatrix]
  apply matrixModLinearMap_ker_eq_diagonal_units_prime_pows_of_lt
  · intro i
    fin_cases i <;> norm_num
  · intro i hi
    fin_cases i
    · norm_num [primePowModulus]
    · norm_num [primePowModulus]
    · change IsUnit (11 : ZMod 16)
      exact ⟨⟨11, 3, by decide, by decide⟩, rfl⟩

theorem ternary_polarDeterminant_val_eleven :
    padicValInt 11 ternaryLattice.polarDeterminant = 1 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hself : padicValInt 11 (11 : ℤ) = 1 := padicValInt_self
  rw [ternaryLattice_polarDeterminant,
    show (176 : ℤ) = 16 * 11 by norm_num,
    padicValInt.mul (by norm_num : (16 : ℤ) ≠ 0) (by norm_num : (11 : ℤ) ≠ 0),
    hself, padicValInt.eq_zero_of_not_dvd (by norm_num : ¬ (11 : ℤ) ∣ 16)]

theorem ternary_eleven_hensel_two :
    letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    IsLocalDensityHenselExponent ternaryLattice 11 2 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply isLocalDensityHenselExponent_of_polarDeterminant_val_lt_of_ne_two
  · rw [ternary_polarDeterminant_val_eleven]
    decide
  · decide

theorem ternary_associated_denominator_eleven_two :
    letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    ternaryLattice.associatedBilinearDualPadicDenominatorIntegralPreimage 11 2 =
      diagonalPrimePowCoordinateSubmodule (n := 3) 11 2 ![0, 0, 1] := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker]
  have hmatrix : ternaryLattice.polarGramMatrix =
      Matrix.diagonal (fun i : Fin 3 => (![2, 4, 2] i : ℤ) * (11 ^ (![0, 0, 1] i) : ℤ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ternaryLattice, polarGramMatrix, Matrix.diagonal_apply]
  rw [hmatrix]
  apply matrixModLinearMap_ker_eq_diagonal_units_prime_pows_of_lt
  · intro i
    fin_cases i <;> norm_num
  · intro i hi
    fin_cases i
    · change IsUnit (2 : ZMod 121)
      exact ⟨⟨2, 61, by decide, by decide⟩, rfl⟩
    · change IsUnit (4 : ZMod 121)
      exact ⟨⟨4, 91, by decide, by decide⟩, rfl⟩
    · change IsUnit (2 : ZMod 121)
      exact ⟨⟨2, 61, by decide, by decide⟩, rfl⟩

theorem ternary_polarDeterminant_val_two :
    padicValInt 2 ternaryLattice.polarDeterminant = 4 := by
  have h16 : padicValInt 2 (16 : ℤ) = 4 := by
    change padicValInt 2 ((2 ^ 4 : ℕ) : ℤ) = 4
    rw [padicValInt.of_nat, padicValNat.prime_pow]
  rw [ternaryLattice_polarDeterminant,
    show (176 : ℤ) = 16 * 11 by norm_num,
    padicValInt.mul (by norm_num : (16 : ℤ) ≠ 0) (by norm_num : (11 : ℤ) ≠ 0),
    h16, padicValInt.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℤ) ∣ 11)]

/-- The remaining dyadic problem is exactly the native count 128. -/
theorem ternary_density_two_eq_native_count :
    normalizedLocalDensity ternaryLattice 2 =
      (associatedBilinearDualQuotientCount ternaryLattice 2 4 : ℝ) / 64 := by
  rw [normalizedLocalDensity_eq_associatedBilinearDualQuotientCount
    ternaryLattice 2 4 ternary_dyadic_hensel_four]
  have hfactor : gramDetPadicNormFactor ternaryLattice 2 = 16 := by
    rw [gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq ternaryLattice 2 4
      (by rw [polarDeterminant_padic_norm_eq_padicValInt, ternary_polarDeterminant_val_two])]
    norm_num [gramDetPadicValuationFactor]
  rw [hfactor]
  norm_num [twoPadicNormInvPow, localDensityDenominatorExponent]
  ring

/-- The remaining odd-prime problem is exactly the native count 53240. -/
theorem ternary_density_eleven_eq_native_count :
    letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    normalizedLocalDensity ternaryLattice 11 =
      (associatedBilinearDualQuotientCount ternaryLattice 11 2 : ℝ) / 322102 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [normalizedLocalDensity_eq_associatedBilinearDualQuotientCount
    ternaryLattice 11 2 ternary_eleven_hensel_two]
  have hfactor : gramDetPadicNormFactor ternaryLattice 11 = 11 := by
    rw [gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq ternaryLattice 11 1
      (by rw [polarDeterminant_padic_norm_eq_padicValInt, ternary_polarDeterminant_val_eleven])]
    norm_num [gramDetPadicValuationFactor]
  rw [hfactor]
  norm_num [twoPadicNormInvPow, localDensityDenominatorExponent]
  ring

end MassFormulaReleaseExamples
