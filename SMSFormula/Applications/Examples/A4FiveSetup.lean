import SMSFormula.Applications.Examples.A4LocalDepth

/-! Actual native depth and a unit change of coordinates for A4 at five. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance a4FivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def a4FiveBasis : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,1,1,1; 0,2,2,2; 0,0,3,3; 0,0,0,4]

theorem a4FiveBasis_det : a4FiveBasis.det = 24 := by decide

theorem a4FiveBasis_gram : a4FiveBasis.transpose * a4Polar * a4FiveBasis =
    Matrix.diagonal ![2,6,12,20] := by decide

theorem a4FiveBasis_unit_twentyFive :
    IsUnit (a4FiveBasis.map (Int.cast : ℤ → ZMod 25)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hd : (a4FiveBasis.map (Int.cast : ℤ → ZMod 25)).det = 24 := by decide
  rw [hd]
  exact ⟨⟨24,24,by decide,by decide⟩,rfl⟩

theorem a4FiveBasis_unit_five :
    IsUnit (a4FiveBasis.map (Int.cast : ℤ → ZMod 5)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hd : (a4FiveBasis.map (Int.cast : ℤ → ZMod 5)).det = 4 := by decide
  rw [hd]
  exact ⟨⟨4,4,by decide,by decide⟩,rfl⟩

theorem a4_latticeOfPolarForm_polarDeterminant_val_five :
    padicValInt 5 a4.latticeOfPolarForm.polarDeterminant = 1 := by
  have hself : padicValInt 5 (5 : ℤ) = 1 := padicValInt_self
  rw [a4_local_polarDeterminant, show (80 : ℤ) = 16 * 5 by norm_num,
    padicValInt.mul (by norm_num : (16 : ℤ) ≠ 0) (by norm_num : (5 : ℤ) ≠ 0),
    padicValInt.eq_zero_of_not_dvd (by norm_num : ¬ (5 : ℤ) ∣ 16),hself]

theorem a4_five_hensel_two : IsLocalDensityHenselExponent a4.latticeOfPolarForm 5 2 := by
  apply isLocalDensityHenselExponent_of_polarDeterminant_val_lt_of_ne_two
  · rw [a4_latticeOfPolarForm_polarDeterminant_val_five]
    decide
  · decide

theorem a4_density_five_eq_native_count :
    normalizedLocalDensity a4.latticeOfPolarForm 5 =
      (associatedBilinearDualQuotientCount a4.latticeOfPolarForm 5 2 : ℝ) *
        Real.sqrt 5 / 97656250 := by
  rw [normalizedLocalDensity_eq_associatedBilinearDualQuotientCount
    a4.latticeOfPolarForm 5 2 a4_five_hensel_two]
  have hfactor : gramDetPadicNormFactor a4.latticeOfPolarForm 5 = 5 * Real.sqrt 5 := by
    rw [gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq a4.latticeOfPolarForm 5 1
      (by rw [polarDeterminant_padic_norm_eq_padicValInt, a4_latticeOfPolarForm_polarDeterminant_val_five])]
    norm_num only [gramDetPadicValuationFactor, Nat.cast_ofNat, Nat.cast_one, one_mul]
    rw [show (3 : ℝ)/2 = 1+1/2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hfactor]
  norm_num [twoPadicNormInvPow, localDensityDenominatorExponent]
  ring

end MassFormulaReleaseExamples
