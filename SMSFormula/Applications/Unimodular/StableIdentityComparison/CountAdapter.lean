import SMSFormula.Applications.Unimodular.StableIdentityComparison.A8Certificate
import SMSFormula.Applications.Unimodular.StableIdentityComparison.CharacteristicOrbit
import SMSFormula.Applications.Unimodular.StableIdentityComparison.FixedLine
import SMSFormula.StandardAxiomsGuard

/-!
# Voskresenskii second-orbit native count adapters

This file composes the checked rank-nine stable-nine certificate with the
characteristic-orbit and fixed-line cardinality transports.  It closes the
one-block native identity/E8 quotient-count relation used by the recursive
seed-coordinate route.
-/

noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice UnimodularMass

namespace StableIdentityComparisonCountAdapter

open StableIdentityComparisonCertificate

/-- The stored-E8 tail quadratic form used by the fixed-line theorem. -/
def e8TailNormModEight (v : Fin 8 → ZMod 4) : ZMod 8 :=
  e8Norm (fun i : Fin 8 => zmodFourLiftToZModEight (v i))

/-- The rank-nine line-plus-E8 quadratic form is definitionally the generic
fixed-line form applied to the stored-E8 tail norm. -/
theorem onePlusE8NormModEight_eq_lineNorm :
    onePlusE8NormModEight = StableIdentityFixedLine.lineNorm e8TailNormModEight := by
  funext x
  simp [onePlusE8NormModEight, StableIdentityFixedLine.lineNorm, e8TailNormModEight]

/-- The stable-nine certificate identifies the fixed characteristic stabilizer
of the diagonal identity target in rank nine with the stored-E8 tail target. -/
def stableNineFixedEquivE8Norm :
    StableIdentityComparison.Fixed 9 ≃ e8NormIsometryModFour := by
  exact StableIdentityFixedLine.fixedTargetEquivTail
    onePlusE8NormModEight identityQuadraticModEight e8TailNormModEight
    (stableNine.map (Int.cast : ℤ → ZMod 4))
    (stableNineInverse.map (Int.cast : ℤ → ZMod 4))
    stableNine_right_inverse_four stableNine_left_inverse_four
    onePlusE8NormModEight_eq_lineNorm
    stableNine_identityQuadraticModEight_eq_onePlusE8Norm
    (StableIdentityComparison.characteristic 9)
    stableNine_modFour_mulVec_firstLine

/-- Cardinality form of the rank-nine fixed-characteristic/E8-tail adapter. -/
theorem fixed_nine_natCard_eq_e8Norm :
    Nat.card (StableIdentityComparison.Fixed 9) = Nat.card e8NormIsometryModFour :=
  Nat.card_congr stableNineFixedEquivE8Norm

/-- The rank-nine identity native quotient count is `2^9` times the concrete
stored-E8 depth-three count. -/
theorem identity_nine_native_quotient_count_eq_two_pow_mul_e8Norm :
    associatedBilinearDualQuotientCount (identityLattice 9) 2 3 =
      2 ^ 9 * Nat.card e8NormIsometryModFour := by
  exact StableIdentityComparison.native_quotient_count_eq_signs_mul_of_fixed_equiv
    9 e8NormIsometryModFour stableNineFixedEquivE8Norm

/-- Fully evaluated one-block Voskresenskii count relation. -/
theorem identity_nine_native_quotient_count_eq_e8_value :
    associatedBilinearDualQuotientCount (identityLattice 9) 2 3 =
      2 ^ 9 * (42525 * 2 ^ 41) := by
  rw [identity_nine_native_quotient_count_eq_two_pow_mul_e8Norm,
    e8NormIsometryModFour_natCard_eq_42525_mul_pow]


/-- The first recursive Type II seed is definitionally a zero block followed by E8;
its stored matrix is the concrete E8 matrix after the recursive reindexing. -/
theorem typeIISeed_one_eq_e8Lattice :
    typeIISeed 1 = e8Lattice := by
  have hform : (typeIISeed 1).pairingMatrix = e8Lattice.pairingMatrix := by
    funext i j
    fin_cases i <;> fin_cases j <;> decide
  cases hseed : typeIISeed 1
  cases he8 : e8Lattice
  simp only [hseed, he8] at hform ⊢
  simpa [PositiveDefiniteIntegralLattice.mk.injEq] using hform

/-- One-block form of the count relation against the concrete production E8 lattice. -/
theorem identity_nine_native_quotient_count_eq_two_pow_mul_e8Lattice :
    associatedBilinearDualQuotientCount (identityLattice 9) 2 3 =
      2 ^ 9 * associatedBilinearDualQuotientCount e8Lattice 2 3 := by
  rw [identity_nine_native_quotient_count_eq_e8_value]
  rw [e8Lattice_associatedBilinearDualQuotientCount_eq_primePowCoordinateSubmodule,
    e8Lattice_primePowCoordinateSubmodule_count_eq_42525_mul_pow]

/-- One-block form matching the conditional native-count premise for `typeIISeed 1`. -/
theorem identity_nine_native_quotient_count_eq_two_pow_mul_typeIISeed_one :
    associatedBilinearDualQuotientCount (identityLattice (8 * 1 + 1)) 2 3 =
      2 ^ (8 * 1 + 1) *
        associatedBilinearDualQuotientCount (typeIISeed 1) 2 3 := by
  rw [show 8 * 1 + 1 = 9 by norm_num]
  rw [typeIISeed_one_eq_e8Lattice]
  exact identity_nine_native_quotient_count_eq_two_pow_mul_e8Lattice


end StableIdentityComparisonCountAdapter

#assert_standard_axioms StableIdentityComparisonCountAdapter.onePlusE8NormModEight_eq_lineNorm
#assert_standard_axioms StableIdentityComparisonCountAdapter.stableNineFixedEquivE8Norm
#assert_standard_axioms StableIdentityComparisonCountAdapter.fixed_nine_natCard_eq_e8Norm
#assert_standard_axioms StableIdentityComparisonCountAdapter.identity_nine_native_quotient_count_eq_two_pow_mul_e8Norm
#assert_standard_axioms StableIdentityComparisonCountAdapter.identity_nine_native_quotient_count_eq_e8_value
#assert_standard_axioms StableIdentityComparisonCountAdapter.typeIISeed_one_eq_e8Lattice
#assert_standard_axioms StableIdentityComparisonCountAdapter.identity_nine_native_quotient_count_eq_two_pow_mul_e8Lattice
#assert_standard_axioms StableIdentityComparisonCountAdapter.identity_nine_native_quotient_count_eq_two_pow_mul_typeIISeed_one
