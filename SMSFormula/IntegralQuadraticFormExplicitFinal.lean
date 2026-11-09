import SMSFormula.IntegralQuadraticFormFinal
import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit
import SMSFormula.FiniteOrthogonalGroupGoodPrimeOddPositivity
import SMSFormula.FiniteOrthogonalGroupGoodPrimeEvenPositivity

/-!
# Explicit odd and even mass formulas for integral quadratic forms

This module inserts the closed Riemann-zeta and quadratic-Dirichlet product
limits into the generic direct mass theorem for integral quadratic forms.  The finite cutoff
prefixes below are the direct `Q_H`/`A`-dual products; comparison with the
scaled integral integral model is used only to prove positivity and convergence.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-- The direct named product limit used by the odd-rank mass formula for integral quadratic
forms.  Its finite prefix is built from the intrinsic local factors. -/
def oddRankOrdinaryMassProductLimit (N s : ℕ) : ℝ :=
  H.massPartialPrimeInverseProduct N *
    (Finset.Icc 1 (s - 1)).prod
      (fun j => PositiveDefiniteIntegralLattice.goodPrimeEulerCoreZetaTailFactor N j)

/-- The direct named product limit used by the non-endpoint even-rank
mass formula for integral quadratic forms. -/
def evenRankOrdinaryMassProductLimit (N s : ℕ) : ℝ :=
  H.massPartialPrimeInverseProduct N *
    ((Finset.Icc 1 (s - 1)).prod
      (fun j => PositiveDefiniteIntegralLattice.goodPrimeEulerCoreZetaTailFactor N j) *
        PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor
          H.latticeOfPolarForm N s)

/-- The direct closed odd-rank product limit is strictly positive. -/
lemma oddRankOrdinaryMassProductLimit_pos (N s : ℕ) :
    0 < H.oddRankOrdinaryMassProductLimit N s := by
  rw [oddRankOrdinaryMassProductLimit,
    H.massPartialPrimeInverseProduct_eq_latticeOfPolarForm]
  exact
    PositiveDefiniteIntegralLattice.oddRankOrdinaryMassProductExpression_pos
      H.latticeOfPolarForm N s

/-- The direct non-endpoint even-rank product limit is strictly positive. -/
lemma evenRankOrdinaryMassProductLimit_pos_of_one_lt
    (N s : ℕ) (hs : 1 < s) (hn : n = 2 * s) :
    0 < H.evenRankOrdinaryMassProductLimit N s := by
  rw [evenRankOrdinaryMassProductLimit,
    H.massPartialPrimeInverseProduct_eq_latticeOfPolarForm,
    PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt hs)]
  exact
    PositiveDefiniteIntegralLattice.evenRankOrdinaryMassProductExpression_pos
      H.latticeOfPolarForm N s hs hn

/-- The closed odd Euler product converges to the direct named
limit of the integral quadratic form. -/
lemma massLocalInverseProductTendsTo_oddRankExplicit
    {N s : ℕ}
    (hB : H.massBadPrimeSet ⊆
      PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    H.massLocalInverseProductTendsTo
      (H.oddRankOrdinaryMassProductLimit N s) := by
  apply
    (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm
      (H.oddRankOrdinaryMassProductLimit N s)).2
  have hBintegralModel :
      PositiveDefiniteIntegralLattice.massBadPrimeSet H.latticeOfPolarForm ⊆
        PositiveDefiniteIntegralLattice.rationalPrimesUpTo N := by
    rw [← H.massBadPrimeSet_eq_latticeOfPolarForm]
    exact hB
  simpa [oddRankOrdinaryMassProductLimit,
    H.massPartialPrimeInverseProduct_eq_latticeOfPolarForm] using
    (PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo_of_goodPrimeOddZetaEulerProduct
        H.latticeOfPolarForm hBintegralModel hs hn)

/-- The closed non-endpoint even Euler product converges to the
direct named limit of the integral quadratic form. -/
lemma massLocalInverseProductTendsTo_evenRankExplicit
    {N s : ℕ}
    (hB : H.massBadPrimeSet ⊆
      PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hs : 1 < s) (hn : n = 2 * s) :
    H.massLocalInverseProductTendsTo
      (H.evenRankOrdinaryMassProductLimit N s) := by
  apply
    (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm
      (H.evenRankOrdinaryMassProductLimit N s)).2
  have hBintegralModel :
      PositiveDefiniteIntegralLattice.massBadPrimeSet H.latticeOfPolarForm ⊆
        PositiveDefiniteIntegralLattice.rationalPrimesUpTo N := by
    rw [← H.massBadPrimeSet_eq_latticeOfPolarForm]
    exact hB
  simpa [evenRankOrdinaryMassProductLimit,
    H.massPartialPrimeInverseProduct_eq_latticeOfPolarForm,
    PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt hs)] using
    (PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct_one_lt
        H.latticeOfPolarForm hBintegralModel hs hn)

/-- The explicit direct ordinary mass formula for integral quadratic forms in odd rank,
stated in `ENNReal`. -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit_ENNReal
    (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : H.massBadPrimeSet ⊆
      PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
      ENNReal.ofReal (H.massFormulaProductSide
        (H.oddRankOrdinaryMassProductLimit N s)) := by
  apply H.transportedOrdinaryGenusMass_eq_massFormulaProductSide_ENNReal hn3
    (H.oddRankOrdinaryMassProductLimit_pos N s)
  exact H.massLocalInverseProductTendsTo_oddRankExplicit hB hs hn

/-- The explicit direct ordinary mass formula for integral quadratic forms in odd rank over
the reals. -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit
    (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : H.massBadPrimeSet ⊆
      PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      H.massFormulaProductSide
        (H.oddRankOrdinaryMassProductLimit N s) := by
  apply H.transportedOrdinaryGenusMass_eq_massFormulaProductSide hn3
    (H.oddRankOrdinaryMassProductLimit_pos N s)
  exact H.massLocalInverseProductTendsTo_oddRankExplicit hB hs hn

/-- The explicit direct ordinary mass formula for integral quadratic forms in even rank,
stated in `ENNReal`.  The canonical rank range forces the non-endpoint
Dirichlet half-plane `1 < s`. -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit_ENNReal
    (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : H.massBadPrimeSet ⊆
      PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hn : n = 2 * s) :
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
      ENNReal.ofReal (H.massFormulaProductSide
        (H.evenRankOrdinaryMassProductLimit N s)) := by
  have hs : 1 < s := by omega
  apply H.transportedOrdinaryGenusMass_eq_massFormulaProductSide_ENNReal hn3
    (H.evenRankOrdinaryMassProductLimit_pos_of_one_lt N s hs hn)
  exact H.massLocalInverseProductTendsTo_evenRankExplicit hB hs hn

/-- The explicit direct ordinary mass formula for integral quadratic forms in even rank over
the reals.  The rank-two continuation endpoint is not used. -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit
    (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : H.massBadPrimeSet ⊆
      PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hn : n = 2 * s) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      H.massFormulaProductSide
        (H.evenRankOrdinaryMassProductLimit N s) := by
  have hs : 1 < s := by omega
  apply H.transportedOrdinaryGenusMass_eq_massFormulaProductSide hn3
    (H.evenRankOrdinaryMassProductLimit_pos_of_one_lt N s hs hn)
  exact H.massLocalInverseProductTendsTo_evenRankExplicit hB hs hn

end PositiveDefiniteIntegralQuadraticForm

end
