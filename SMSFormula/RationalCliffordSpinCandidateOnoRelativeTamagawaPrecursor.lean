import SMSFormula.RationalCliffordSpinCandidateFppf
import SMSFormula.RationalCliffordSpinKernelCharacterCoefficient
import SMSFormula.RationalSpecialOrthogonalRawInvariantDifferentialMeasurableWeilMeasureData

/-!
# Ono relative Tamagawa precursor for the Spin candidate

The algebraic central cover is fppf and its intrinsic character
coefficient has `h^0 / i^1 = 2`.  Ono's remaining relative theorem is a
statement about canonically normalized adelic quotient volumes.

This file is the scalar precursor: a prospective Spin Tamagawa number is an
explicit parameter, and the relative comparison is Ono's literal quotient
formula.  The later module
`RationalCliffordSpinCandidateOnoRelativeTamagawaData` specializes that
parameter to the quotient volume of the completed raw Spin measurable-Weil
datum.  Lemmas here reduce the cohomological right side to two
and separate the subsequent input that the Spin Tamagawa number is one.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalTamagawa

/-- The intrinsic central-kernel coefficient, interpreted in `ENNReal` for
comparison with Tamagawa quotient volumes. -/
def spinCentralKernelCharacterCohomologicalFactorENNReal : ℝ≥0∞ :=
  (Nat.card (SpinCentralKernelCharacterFixedPart ℚ) : ℝ≥0∞) /
    Nat.card SpinCentralKernelCharacterI1

/-- The `ENNReal` form of the completed `h^0 / i^1 = 2` calculation. -/
theorem spinCentralKernelCharacterCohomologicalFactorENNReal_eq_two :
    spinCentralKernelCharacterCohomologicalFactorENNReal = 2 := by
  rw [spinCentralKernelCharacterCohomologicalFactorENNReal,
    natCard_spinCentralKernelCharacterFixedPart_eq_two,
    natCard_spinCentralKernelCharacterI1_eq_one]
  norm_num

end RationalTamagawa

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The exact specialized relative-measure statement still required from
Ono's theorem.  The second argument is the Tamagawa number of a canonically
normalized Spin-candidate measurable-Weil datum.

This proposition deliberately says only that the quotient of the two
Tamagawa numbers is the already formalized intrinsic cohomological factor.
It does not manufacture adelic Spin data from the fppf cover. -/
def IsCliffordSpinCandidateOnoRelativeTamagawaComparison
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V)
    (spinTamagawaNumberENNReal : ℝ≥0∞) : Prop :=
  D.tamagawaNumberENNReal / spinTamagawaNumberENNReal =
    spinCentralKernelCharacterCohomologicalFactorENNReal

/-- For the completed central kernel, Ono's relative comparison is literally
the assertion that the quotient of Tamagawa numbers is two. -/
theorem isCliffordSpinCandidateOnoRelativeTamagawaComparison_iff
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V)
    (spinTamagawaNumberENNReal : ℝ≥0∞) :
    V.IsCliffordSpinCandidateOnoRelativeTamagawaComparison
        D spinTamagawaNumberENNReal ↔
      D.tamagawaNumberENNReal / spinTamagawaNumberENNReal = 2 := by
  rw [IsCliffordSpinCandidateOnoRelativeTamagawaComparison,
    spinCentralKernelCharacterCohomologicalFactorENNReal_eq_two]

/-- Positivity and finiteness of the Spin Tamagawa number turn Ono's quotient
formula into the multiplication formula `tau(SO) = 2 * tau(Spin)`. -/
theorem tamagawaNumberENNReal_eq_two_mul_of_onoRelativeComparison
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V)
    (spinTamagawaNumberENNReal : ℝ≥0∞)
    (hspin0 : spinTamagawaNumberENNReal ≠ 0)
    (hspinTop : spinTamagawaNumberENNReal ≠ ⊤)
    (hrelative :
      V.IsCliffordSpinCandidateOnoRelativeTamagawaComparison
        D spinTamagawaNumberENNReal) :
    D.tamagawaNumberENNReal = 2 * spinTamagawaNumberENNReal := by
  have hratio :
      D.tamagawaNumberENNReal / spinTamagawaNumberENNReal = 2 :=
    (V.isCliffordSpinCandidateOnoRelativeTamagawaComparison_iff
      D spinTamagawaNumberENNReal).mp hrelative
  have hinv_mul :
      spinTamagawaNumberENNReal⁻¹ * spinTamagawaNumberENNReal = 1 := by
    rw [mul_comm, ENNReal.mul_inv_cancel hspin0 hspinTop]
  calc
    D.tamagawaNumberENNReal = D.tamagawaNumberENNReal * 1 := by rw [mul_one]
    _ = D.tamagawaNumberENNReal *
        (spinTamagawaNumberENNReal⁻¹ * spinTamagawaNumberENNReal) := by
      rw [hinv_mul]
    _ = (D.tamagawaNumberENNReal / spinTamagawaNumberENNReal) *
        spinTamagawaNumberENNReal := by
      rw [div_eq_mul_inv]
      ac_rfl
    _ = 2 * spinTamagawaNumberENNReal := by rw [hratio]

/-- The completed algebraic prerequisites for Ono's specialized
relative formula: the candidate cover is fppf and its cohomological factor is
two. -/
theorem cliffordSpinCandidateFppf_and_onoCohomologicalFactor :
    V.CliffordSpinCandidateToSpecialOrthogonalFppf ∧
      spinCentralKernelCharacterCohomologicalFactorENNReal = 2 :=
  ⟨V.cliffordSpinCandidateToSpecialOrthogonalFppf,
    spinCentralKernelCharacterCohomologicalFactorENNReal_eq_two⟩

/-- Once the specialized relative-measure comparison and the independent
input `tau(Spin) = 1` are supplied, any raw invariant-differential `SO` datum
has Tamagawa number two.

The normalization certificate is an explicit argument so that this theorem
cannot be applied to an arbitrarily rescaled measurable-Weil datum. -/
theorem specialOrthogonalTamagawaNumberENNReal_eq_two_of_onoRelativeComparison
    (D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V)
    (_C : IsRawInvariantDifferentialMeasurableWeilMeasureData V D)
    (spinTamagawaNumberENNReal : ℝ≥0∞)
    (hrelative :
      V.IsCliffordSpinCandidateOnoRelativeTamagawaComparison
        D spinTamagawaNumberENNReal)
    (hspin : spinTamagawaNumberENNReal = 1) :
    D.tamagawaNumberENNReal = 2 := by
  subst spinTamagawaNumberENNReal
  simpa using
    V.tamagawaNumberENNReal_eq_two_mul_of_onoRelativeComparison
      D 1 one_ne_zero ENNReal.one_ne_top hrelative

end RationalQuadraticSpaceMatrix
