import SMSFormula.IntegralQuadraticFormGenusMass
import SMSFormula.Applications.Examples.A2Residue

/-! The A2 endpoint for the independently defined integral-Q genus class sum. -/

namespace MassFormulaReleaseExamples

theorem a2_intrinsic_ordinaryGenusMass : a2.ordinaryGenusMass = (1/12 : ℚ) := by
  rw [PositiveDefiniteIntegralQuadraticForm.ordinaryGenusMass_eq_latticeOfPolarForm,
    a2_latticeOfPolarForm_ordinaryGenusMass]

end MassFormulaReleaseExamples
