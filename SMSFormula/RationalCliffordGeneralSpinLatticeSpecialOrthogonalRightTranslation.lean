import SMSFormula.RationalCliffordGeneralSpinSpecialOrthogonalCarrierRightTranslation
import SMSFormula.RationalCliffordSpinCandidateLatticeRawOnoTamagawaData
import SMSFormula.RationalCliffordSpinCandidateLatticeSpecialOrthogonalQuotientRightTranslation

/-!
# Right translation of the lattice raw special-orthogonal quotient

The concrete lattice `SO` quotient measure is already known to be invariant
under right translation.  This module transports that exact identity to the
rational-quadratic-space carrier used by the crossed `GSpin` comparison.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The rational-carrier `SO` quotient measure in the exact lattice raw datum
is invariant under every adelic right translation. -/
theorem map_latticeRawSpecialOrthogonalQuotientMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul
          x)
        ((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalData.quotientMeasure) =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L hn inst hP hconv).specialOrthogonalData.quotientMeasure := by
  let μ := L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P
  change Measure.map
      (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul
        x)
      (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μ) =
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μ
  apply L.map_rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure_rightMul
  exact L.map_concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_rightMul
    hn inst hP hconv
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x)

end PositiveDefiniteIntegralLattice
