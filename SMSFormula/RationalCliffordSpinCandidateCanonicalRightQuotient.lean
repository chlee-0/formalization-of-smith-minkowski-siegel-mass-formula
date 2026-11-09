import SMSFormula.AdelicMeasurableWeilQuotientUniqueness
import SMSFormula.RationalCliffordSpinCandidateRawOnoRightQuotient

/-!
# Canonical right quotient measure for the raw Spin datum

The exact measurable Spin fundamental domain makes any measurable left Weil
quotient measure equal to its fundamental-domain pushforward.  For the raw
Ono datum, completed inversion and right invariance then place the transported
right quotient in Mathlib's `QuotientMeasureEqMeasurePreimage` class.

Accordingly, comparison with a canonical Tamagawa quotient needs no separate
quotient-measure transport: once its ambient measure is
identified with the raw invariant-differential measure and it satisfies the
canonical quotient class, uniqueness makes the quotient measures equal.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

local instance canonicalSpinRightQuotientDiagonalCountable
    (V : RationalQuadraticSpaceMatrix n) :
    Countable V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
  V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable

namespace CliffordSpinCandidateMeasurableWeilMeasureData

/-- The exact Spin fundamental domain makes every measurable left Weil
quotient measure the corresponding fundamental-domain pushforward. -/
theorem quotientMeasure_eq_fundamentalDomain
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData) :
    D.quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
        D.adelicMeasure
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
  exact
    D.isMeasurableWeilQuotientMeasure
      |>.eq_leftQuotientFundamentalDomainMeasure
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup rfl
        V.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
        V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain

end CliffordSpinCandidateMeasurableWeilMeasureData

namespace CliffordSpinCandidateRawOnoTamagawaData

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
