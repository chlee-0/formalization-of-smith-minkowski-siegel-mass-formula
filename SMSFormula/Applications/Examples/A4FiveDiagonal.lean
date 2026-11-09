import SMSFormula.Applications.Examples.A4FiveSetup

/-! An actual local isometry to the diagonal A4 coordinate model at five. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance a4FiveDiagonalPrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def a4FiveDiagonalLattice : PositiveDefiniteIntegralLattice 4 where
  pairingMatrix := Matrix.diagonal ![2,6,12,20]
  form_symm := Matrix.isSymm_diagonal _
  form_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]
    · intro x hx
      have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 := by
        by_contra h
        push Not at h
        apply hx
        ext i
        fin_cases i <;> simp_all
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.diagonal_apply]
      rcases hn with h|h|h|h <;>
        nlinarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),sq_nonneg (x 3),
          sq_pos_of_ne_zero h]

theorem a4FiveBasis_unit_padic : IsUnit (a4FiveBasis.map (Int.cast : ℤ → ℤ_[5])) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit ((a4FiveBasis.map (Int.castRingHom ℤ_[5])).det)
  have hd : (a4FiveBasis.map (Int.castRingHom ℤ_[5])).det = (a4FiveBasis.det : ℤ_[5]) :=
    ((Int.castRingHom ℤ_[5]).map_det _).symm
  rw [hd,a4FiveBasis_det]
  rw [PadicInt.isUnit_iff]
  exact (PadicInt.norm_natCast_eq_one_iff (p := 5)).2 (by decide)

theorem a4FiveDiagonal_local_isometry :
    a4FiveDiagonalLattice.IsLocallyIsometricAt a4.latticeOfPolarForm 5 := by
  refine ⟨a4FiveBasis.map (Int.castRingHom ℤ_[5]),a4FiveBasis_unit_padic,?_⟩
  change (a4FiveBasis.map (Int.castRingHom ℤ_[5])).transpose *
    (a4Polar.map (Int.castRingHom ℤ_[5])) * a4FiveBasis.map (Int.castRingHom ℤ_[5]) =
      (Matrix.diagonal (![2,6,12,20] : Fin 4 → ℤ)).map (Int.castRingHom ℤ_[5])
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, a4FiveBasis_gram]

theorem a4FiveDiagonal_polarDeterminant : a4FiveDiagonalLattice.polarDeterminant = 46080 := by
  decide

theorem a4FiveDiagonal_polarDeterminant_val :
    padicValInt 5 a4FiveDiagonalLattice.polarDeterminant = 1 := by
  have hself : padicValInt 5 (5 : ℤ) = 1 := padicValInt_self
  rw [a4FiveDiagonal_polarDeterminant, show (46080 : ℤ) = 9216*5 by norm_num,
    padicValInt.mul (by norm_num : (9216 : ℤ) ≠ 0) (by norm_num : (5 : ℤ) ≠ 0),
    padicValInt.eq_zero_of_not_dvd (by norm_num : ¬ (5 : ℤ) ∣ 9216),hself]

theorem a4FiveDiagonal_hensel_two : IsLocalDensityHenselExponent a4FiveDiagonalLattice 5 2 := by
  apply isLocalDensityHenselExponent_of_polarDeterminant_val_lt_of_ne_two
  · rw [a4FiveDiagonal_polarDeterminant_val]
    decide
  · decide

theorem a4_density_five_eq_diagonal :
    normalizedLocalDensity a4.latticeOfPolarForm 5 =
      normalizedLocalDensity a4FiveDiagonalLattice 5 :=
  (normalizedLocalDensity_eq_of_isLocallyIsometricAt 5 2 a4FiveDiagonal_local_isometry
    a4FiveDiagonal_hensel_two a4_five_hensel_two).symm

theorem a4FiveDiagonal_associated_denominator :
    a4FiveDiagonalLattice.associatedBilinearDualPadicDenominatorIntegralPreimage 5 2 =
      diagonalPrimePowCoordinateSubmodule (n := 4) 5 2 ![0,0,0,1] := by
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage_eq_polarGramMatrixModLinearMap_ker]
  have hm : a4FiveDiagonalLattice.polarGramMatrix = Matrix.diagonal
      (fun i : Fin 4 => (![4,12,24,8] i : ℤ)*(5^(![0,0,0,1] i) : ℤ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [a4FiveDiagonalLattice,polarGramMatrix,Matrix.diagonal_apply]
  rw [hm]
  apply matrixModLinearMap_ker_eq_diagonal_units_prime_pows_of_lt
  · intro i
    fin_cases i <;> norm_num
  · intro i hi
    fin_cases i
    · change IsUnit (4 : ZMod 25)
      exact ⟨⟨4,19,by decide,by decide⟩,rfl⟩
    · change IsUnit (12 : ZMod 25)
      exact ⟨⟨12,23,by decide,by decide⟩,rfl⟩
    · change IsUnit (24 : ZMod 25)
      exact ⟨⟨24,24,by decide,by decide⟩,rfl⟩
    · change IsUnit (8 : ZMod 25)
      exact ⟨⟨8,22,by decide,by decide⟩,rfl⟩

theorem a4FiveDiagonal_density_eq_native_count :
    normalizedLocalDensity a4FiveDiagonalLattice 5 =
      (associatedBilinearDualQuotientCount a4FiveDiagonalLattice 5 2 : ℝ)*
        Real.sqrt 5 / 97656250 := by
  rw [normalizedLocalDensity_eq_associatedBilinearDualQuotientCount
    a4FiveDiagonalLattice 5 2 a4FiveDiagonal_hensel_two]
  have hfactor : gramDetPadicNormFactor a4FiveDiagonalLattice 5 = 5*Real.sqrt 5 := by
    rw [gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq a4FiveDiagonalLattice 5 1
      (by rw [polarDeterminant_padic_norm_eq_padicValInt,a4FiveDiagonal_polarDeterminant_val])]
    norm_num only [gramDetPadicValuationFactor,Nat.cast_ofNat,Nat.cast_one,one_mul]
    rw [show (3 : ℝ)/2 = 1+1/2 by norm_num,
      Real.rpow_add (by norm_num),Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hfactor]
  norm_num [twoPadicNormInvPow,localDensityDenominatorExponent]
  ring

end MassFormulaReleaseExamples
