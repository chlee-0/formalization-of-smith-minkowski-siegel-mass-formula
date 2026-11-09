import SMSFormula.RankOneProduct
import SMSFormula.BinaryMassFormula
import SMSFormula.RationalSpecialOrthogonalMassFormula
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductConvergence

/-!
# Ordinary full-O mass in every positive rank

For the unchanged Schulze--Pillot densities, the ordinary mass is
`positiveRankMassCorrection n * (archimedeanMassFactor n * P)` for one
positive increasing-prime inverse-product limit P. The correction is one
half in rank one and one in all ranks at least two. All original definitions
and the obstruction to the uncorrected unary formula remain unchanged.
No unordered or absolute convergence is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The transparent rank-one correction for the original literal densities. -/
def positiveRankMassCorrection (n : ℕ) : ℝ := if n = 1 then 1 / 2 else 1

@[simp] theorem positiveRankMassCorrection_one : positiveRankMassCorrection 1 = 1 / 2 := by
  norm_num [positiveRankMassCorrection]

/-- The classical coefficient is unchanged in rank at least two. -/
theorem positiveRankMassCorrection_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    positiveRankMassCorrection n = 1 := by
  simp [positiveRankMassCorrection, show n ≠ 1 by omega]

/-- The literal unary limit and corrected ordinary mass for any positive coefficient. -/
theorem massFormula_positiveRank_rank_one (L : PositiveDefiniteIntegralLattice 1) :
    L.massLocalInverseProductTendsTo (1 / 2 : ℝ) ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) =
        positiveRankMassCorrection 1 * (archimedeanMassFactor 1 * (1 / 2 : ℝ)) := by
  refine ⟨massLocalInverseProductTendsTo_rank_one L, ?_⟩
  rw [ordinaryGenusMass_eq_one_half_rank_one, positiveRankMassCorrection_one,
    archimedeanMassFactor_one]
  norm_num

/-- The classical ordinary mass formula with one positive actual product limit
for every lattice of rank at least two. No caller convergence premise is required. -/
theorem exists_massFormula_of_two_le {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : 2 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ L.massLocalInverseProductTendsTo P ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) = archimedeanMassFactor n * P := by
  by_cases htwo : n = 2
  · subst n
    exact exists_pos_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_two L
  · have hthree : 3 ≤ n := by omega
    obtain ⟨P, hP, hconv⟩ := L.exists_pos_massLocalInverseProductTendsTo hthree
    exact ⟨P, hP, hconv, L.ordinaryGenusMass_eq_massFormulaProductSide hthree hP hconv⟩

/-- The ordinary full-O mass formula for every positive rank, with the explicit
unary correction and one positive increasing-prime limit for the same lattice. -/
theorem exists_massFormula_positiveRank {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : 1 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ L.massLocalInverseProductTendsTo P ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) =
        positiveRankMassCorrection n * (archimedeanMassFactor n * P) := by
  by_cases hone : n = 1
  · subst n
    exact ⟨1 / 2, by norm_num, massFormula_positiveRank_rank_one L⟩
  · have htwo : 2 ≤ n := by omega
    obtain ⟨P, hP, hconv, hmass⟩ := exists_massFormula_of_two_le L htwo
    exact ⟨P, hP, hconv, by rwa [positiveRankMassCorrection_of_two_le htwo, one_mul]⟩

/-- Any supplied ordered-product limit equals the limit in the positive-rank
mass formula, so the formula holds with it.  Its positivity need not be
assumed separately. -/
theorem ordinaryGenusMass_eq_positiveRankMassFormula {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hn : 1 ≤ n) {P : ℝ} (hconv : L.massLocalInverseProductTendsTo P) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      positiveRankMassCorrection n * (archimedeanMassFactor n * P) := by
  obtain ⟨P₀, _, hconv₀, hmass⟩ := exists_massFormula_positiveRank L hn
  have heq : P₀ = P := tendsto_nhds_unique hconv₀ hconv
  simpa only [heq] using hmass

/-- The uncorrected classical formula for any actual limit in rank at least two. -/
theorem ordinaryGenusMass_eq_massFormula_of_two_le {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hn : 2 ≤ n) {P : ℝ} (hconv : L.massLocalInverseProductTendsTo P) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = archimedeanMassFactor n * P := by
  simpa only [positiveRankMassCorrection_of_two_le hn, one_mul] using
    ordinaryGenusMass_eq_positiveRankMassFormula L (by omega) hconv

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.positiveRankMassCorrection
#assert_standard_axioms PositiveDefiniteIntegralLattice.positiveRankMassCorrection_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.positiveRankMassCorrection_of_two_le
#assert_standard_axioms PositiveDefiniteIntegralLattice.massFormula_positiveRank_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_massFormula_of_two_le
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_massFormula_positiveRank
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_positiveRankMassFormula
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_massFormula_of_two_le
