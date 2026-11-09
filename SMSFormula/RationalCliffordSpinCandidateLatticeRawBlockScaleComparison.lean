import SMSFormula.RationalCliffordSpinCandidateLatticeFiniteScaleComparison
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialMeasure

/-!
# The common lattice Spin--SO raw block scale

At the finite comparison bad set, the coherent Spin block weight differs
from the coherent special-orthogonal block weight by exactly the exceptional
Euler correction.  The lattice raw finite scales differ by the inverse
relation, so the complete raw block scalars agree literally.
-/

noncomputable section

open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- At the common finite comparison bad set, the Spin coherent block weight
is the exceptional correction times the special-orthogonal block weight. -/
theorem cliffordSpinCandidateComparisonBadPlaces_spinBlockWeight_eq_correction_mul_soBlockWeight
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
          V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces =
      V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection *
        V.finiteAdelicSpecialOrthogonalBlockWeight
          V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces := by
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_eq_prod_sdiff_badPlaces]
  change
    V.cliffordSpinCandidateExceptionalIntegralInverseVolume =
      (V.cliffordSpinCandidateExceptionalIntegralInverseVolume *
          V.specialOrthogonalExceptionalIntegralInverseVolume⁻¹) *
        V.specialOrthogonalExceptionalIntegralInverseVolume
  rw [mul_assoc, ENNReal.inv_mul_cancel
    V.specialOrthogonalExceptionalIntegralInverseVolume_ne_zero
    V.specialOrthogonalExceptionalIntegralInverseVolume_ne_top, mul_one]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The literal raw Spin and special-orthogonal scalar weights agree on the
common finite comparison block. -/
theorem cliffordSpinCandidateRawFiniteScaleOfLattice_mul_comparisonBlockWeight_eq_soScale_mul_blockWeight
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv : ℝ≥0∞) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
          L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalBlockWeight
          L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces := by
  rw [L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateComparisonBadPlaces_spinBlockWeight_eq_correction_mul_soBlockWeight]
  rw [← mul_assoc,
    mul_comm
      (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv : ℝ≥0∞)
      L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection,
    L.cliffordSpinCandidateRawFiniteScaleOfLattice_correction_mul_eq_soScale]

/-- Datum-facing form of the common raw block-scalar identity. -/
theorem cliffordSpinCandidateRawOnoTamagawaDataOfLattice_spinScale_mul_comparisonBlockWeight_eq_soScale_mul_blockWeight
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).spinFiniteScale : ℝ≥0∞) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
          L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalFiniteScale *
        L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalBlockWeight
          L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces := by
  simpa using
    L.cliffordSpinCandidateRawFiniteScaleOfLattice_mul_comparisonBlockWeight_eq_soScale_mul_blockWeight
      hn hP hconv

end PositiveDefiniteIntegralLattice

