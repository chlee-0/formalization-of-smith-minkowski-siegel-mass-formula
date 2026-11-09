import SMSFormula.PositiveRankMassFormula
import SMSFormula.IntegralQuadraticFormProduct
import SMSFormula.IntegralQuadraticFormMassTransport

/-!
# Positive-rank mass of integral quadratic forms

The mass is the direct Q-genus class sum with full-O weights. The
polarization comparison proves equality to the transported definition.
The direct local-product comparison transports the same positive `P`.
-/

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

/-- Unconditional positive-rank mass with the same integral model and the same product limit. -/
theorem exists_transportedMassFormula_positiveRank (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 1 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ H.massLocalInverseProductTendsTo P ∧
      ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
          (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) := by
  obtain ⟨P, hP, hconv, hmass⟩ :=
    PositiveDefiniteIntegralLattice.exists_massFormula_positiveRank H.latticeOfPolarForm hn
  exact ⟨P, hP, (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm P).mpr hconv, hmass⟩

/-- Classical uncorrected transported mass in rank at least two. -/
theorem exists_transportedMassFormula_of_two_le (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 2 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ H.massLocalInverseProductTendsTo P ∧
      ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P := by
  obtain ⟨P, hP, hconv, hmass⟩ :=
    PositiveDefiniteIntegralLattice.exists_massFormula_of_two_le H.latticeOfPolarForm hn
  exact ⟨P, hP, (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm P).mpr hconv, hmass⟩

/-- The corrected transported mass at any actual direct ordered-product limit. -/
theorem transportedOrdinaryGenusMass_eq_positiveRankMassFormula (H : PositiveDefiniteIntegralQuadraticForm n)
    (hn : 1 ≤ n) {P : ℝ} (hconv : H.massLocalInverseProductTendsTo P) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
        (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) :=
  PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_positiveRankMassFormula H.latticeOfPolarForm hn
    ((H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm P).mp hconv)

/-- The uncorrected transported mass at any actual limit in rank at least two. -/
theorem transportedOrdinaryGenusMass_eq_massFormula_of_two_le (H : PositiveDefiniteIntegralQuadraticForm n)
    (hn : 2 ≤ n) {P : ℝ} (hconv : H.massLocalInverseProductTendsTo P) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P :=
  PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_massFormula_of_two_le H.latticeOfPolarForm hn
    ((H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm P).mp hconv)

/-- The direct full-O Q-class sum and the same positive ordered density limit. -/
theorem exists_massFormula_positiveRank (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 1 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ H.massLocalInverseProductTendsTo P ∧
      ((H.ordinaryGenusMass : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
          (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) := by
  rw [H.ordinaryGenusMass_eq_transportedOrdinaryGenusMass]
  exact H.exists_transportedMassFormula_positiveRank hn

/-- The direct Q-class mass formula in every rank at least two. -/
theorem exists_massFormula_of_two_le (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 2 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ H.massLocalInverseProductTendsTo P ∧
      ((H.ordinaryGenusMass : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P := by
  rw [H.ordinaryGenusMass_eq_transportedOrdinaryGenusMass]
  exact H.exists_transportedMassFormula_of_two_le hn

/-- Direct Q-class mass for any supplied actual positive-rank limit. -/
theorem ordinaryGenusMass_eq_positiveRankMassFormula (H : PositiveDefiniteIntegralQuadraticForm n)
    (hn : 1 ≤ n) {P : ℝ} (hconv : H.massLocalInverseProductTendsTo P) :
    ((H.ordinaryGenusMass : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
        (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) := by
  rw [H.ordinaryGenusMass_eq_transportedOrdinaryGenusMass]
  exact H.transportedOrdinaryGenusMass_eq_positiveRankMassFormula hn hconv

/-- The uncorrected direct Q-class formula for any actual limit in rank at least two. -/
theorem ordinaryGenusMass_eq_massFormula_of_two_le (H : PositiveDefiniteIntegralQuadraticForm n)
    (hn : 2 ≤ n) {P : ℝ} (hconv : H.massLocalInverseProductTendsTo P) :
    ((H.ordinaryGenusMass : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P := by
  rw [H.ordinaryGenusMass_eq_transportedOrdinaryGenusMass]
  exact H.transportedOrdinaryGenusMass_eq_massFormula_of_two_le hn hconv

end PositiveDefiniteIntegralQuadraticForm

#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_transportedMassFormula_positiveRank
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_transportedMassFormula_of_two_le
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.transportedOrdinaryGenusMass_eq_positiveRankMassFormula
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.transportedOrdinaryGenusMass_eq_massFormula_of_two_le

#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_massFormula_positiveRank
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_massFormula_of_two_le
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.ordinaryGenusMass_eq_positiveRankMassFormula
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.ordinaryGenusMass_eq_massFormula_of_two_le
