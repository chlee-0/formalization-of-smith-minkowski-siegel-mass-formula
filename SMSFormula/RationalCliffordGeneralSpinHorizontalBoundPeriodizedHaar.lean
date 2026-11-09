import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicUnimodular
import SMSFormula.RationalCliffordGeneralSpinHorizontalBoundPeriodizedRightHaar

/-!
# The concrete horizontal periodization against the fixed adelic Haar measure

Full horizontal `GSpin` unimodularity removes the inverse from the
right-Haar comparison.  The scalar is the same positive
finite scalar, which is not evaluated here; its explicit value comes from the
central-extension Weil normalization calculation.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Exact ambient Haar proportionality after certifying horizontal adelic
`GSpin` unimodularity. -/
theorem periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontal
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv)) =
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
          hn inst hP hconv •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [L.periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
      hn inst hP hconv,
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_inv]

end PositiveDefiniteIntegralLattice
