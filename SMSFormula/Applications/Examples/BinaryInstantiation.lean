import SMSFormula.Applications.Examples.Inputs
import SMSFormula.BinaryMassFormula

/-!
# Actual binary mass formula on the A2 input

The positive ordered product and ordinary full-O mass here belong to the actual
integral `2Q` integral model. The input crosswalk is proved in `Inputs`.
This instantiation does not evaluate that product or prove the target `1/12`.
-/

noncomputable section

namespace MassFormulaReleaseExamples

theorem a2_latticeOfPolarForm_binaryContent : a2.latticeOfPolarForm.binaryContent = 2 := by decide

theorem a2_latticeOfPolarForm_binaryPrimitiveDiscriminant :
    a2.latticeOfPolarForm.binaryPrimitiveDiscriminant = -3 := by decide

theorem a2_latticeOfPolarForm_polarDeterminant : a2.latticeOfPolarForm.polarDeterminant = 12 := by
  decide

theorem a4_latticeOfPolarForm_polarDeterminant : a4.latticeOfPolarForm.polarDeterminant = 80 := by
  decide

theorem a4_latticeOfPolarForm_characterDiscriminant :
    PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDiscriminant a4.latticeOfPolarForm 2 = 80 := by
  decide

theorem a4_latticeOfPolarForm_characterModulus :
    PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2 = 320 := by
  decide

theorem a2_actual_massFormula :
    ∃ P : ℝ, 0 < P ∧ a2.latticeOfPolarForm.massLocalInverseProductTendsTo P ∧
      ((a2.latticeOfPolarForm.ordinaryGenusMass : ℚ) : ℝ) =
        (2 / Real.pi) * P := by
  obtain ⟨P, hP, hconv, hmass⟩ := a2.latticeOfPolarForm
    |>.exists_pos_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_two
  refine ⟨P, hP, hconv, ?_⟩
  simpa only [PositiveDefiniteIntegralLattice.archimedeanMassFactor_two] using hmass

end MassFormulaReleaseExamples

#assert_standard_axioms MassFormulaReleaseExamples.a2_actual_massFormula
