import SMSFormula.Applications.Unimodular.StableIdentityComparison.CountAdapter
import SMSFormula.StandardAxiomsGuard

/-!
# Seed norm adapters for the Voskresenskii second-orbit route

This file packages the rank-uniform target used after constructing the stable
coordinate matrices.  A supplied pointed quadratic equivalence from the diagonal
identity form in rank `8*k+1` to a norm-one line plus the stored `typeIISeed k`
form gives the fixed-characteristic count against the corresponding seed-tail
isometry type.  The recursive construction of those stable matrices and the
native quotient predicate comparison are not part of this file.
-/

noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice

namespace StableIdentityComparisonSeedNormAdapter

open StableIdentityComparisonCertificate

/-- The stored `typeIISeed k` quadratic form on `ZMod 4` coordinates, valued
modulo `8` by using canonical representatives. -/
def seedNormModEight (k : ℕ) (v : Fin (8 * k) → ZMod 4) : ZMod 8 :=
  ∑ i, zmodFourLiftToZModEight (v i) *
    (((typeIISeed k).pairingMatrix.map (Int.cast : ℤ → ZMod 8)).mulVec
      (fun j : Fin (8 * k) => zmodFourLiftToZModEight (v j)) i)

/-- The mod-four matrix target preserving the stored `typeIISeed k` quadratic
form modulo `8`.  The remaining native-quotient adapter must identify this
finite type with the existing Schulze--Pillot depth-three coordinate count. -/
abbrev seedNormIsometryModFour (k : ℕ) : Type :=
  StableIdentityFixedLine.Iso (seedNormModEight k)

noncomputable instance (k : ℕ) : Fintype (seedNormIsometryModFour k) := by
  unfold seedNormIsometryModFour StableIdentityFixedLine.Iso StableIdentityFixedLine.Mat
  infer_instance

/-- The fixed-characteristic set in rank `8*k+1` is identified with the seed-tail
isometry target from any pointed stable coordinate certificate. -/
def fixedEquivSeedNormOfStable (k : ℕ)
    (U V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight (U.mulVec x) =
        StableIdentityFixedLine.lineNorm (seedNormModEight k) x)
    (hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1)) :
    StableIdentityComparison.Fixed (8 * k + 1) ≃ seedNormIsometryModFour k := by
  exact StableIdentityFixedLine.fixedTargetEquivTail
    (StableIdentityFixedLine.lineNorm (seedNormModEight k))
    identityQuadraticModEight (seedNormModEight k)
    U V hUV hVU rfl hQ
    (StableIdentityComparison.characteristic (8 * k + 1)) hw

/-- Count form of `fixedEquivSeedNormOfStable`. -/
theorem fixed_natCard_eq_seedNorm_of_stable (k : ℕ)
    (U V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight (U.mulVec x) =
        StableIdentityFixedLine.lineNorm (seedNormModEight k) x)
    (hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1)) :
    Nat.card (StableIdentityComparison.Fixed (8 * k + 1)) =
      Nat.card (seedNormIsometryModFour k) :=
  Nat.card_congr (fixedEquivSeedNormOfStable k U V hUV hVU hQ hw)

/-- Characteristic-orbit count specialized to a supplied stable seed coordinate
certificate. -/
theorem identity_native_count_eq_two_pow_mul_seedNorm_of_stable (k : ℕ)
    (U V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight (U.mulVec x) =
        StableIdentityFixedLine.lineNorm (seedNormModEight k) x)
    (hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1)) :
    associatedBilinearDualQuotientCount
        (identityLattice (8 * k + 1)) 2 3 =
      2 ^ (8 * k + 1) * Nat.card (seedNormIsometryModFour k) := by
  exact StableIdentityComparison.native_quotient_count_eq_signs_mul_of_fixed_equiv
    (8 * k + 1) (seedNormIsometryModFour k)
    (fixedEquivSeedNormOfStable k U V hUV hVU hQ hw)

/-- At one block, the generic seed norm is the stored-E8 tail norm used by the
rank-nine adapter. -/
theorem seedNormModEight_one_eq_e8TailNorm :
    seedNormModEight 1 = StableIdentityComparisonCountAdapter.e8TailNormModEight := by
  funext v
  unfold seedNormModEight StableIdentityComparisonCountAdapter.e8TailNormModEight
  rw [StableIdentityComparisonCountAdapter.typeIISeed_one_eq_e8Lattice]
  simp [StableIdentityComparisonCertificate.e8Norm, e8Lattice]

/-- One-block seed-tail isometry target agrees with the stored-E8 target. -/
def seedNormIsometryOneEquivE8Norm :
    seedNormIsometryModFour 1 ≃ e8NormIsometryModFour := by
  rw [show seedNormIsometryModFour 1 = StableIdentityFixedLine.Iso
      StableIdentityComparisonCountAdapter.e8TailNormModEight by
    unfold seedNormIsometryModFour
    rw [seedNormModEight_one_eq_e8TailNorm]]
  rfl

end StableIdentityComparisonSeedNormAdapter

#assert_standard_axioms StableIdentityComparisonSeedNormAdapter.seedNormModEight
#assert_standard_axioms StableIdentityComparisonSeedNormAdapter.fixedEquivSeedNormOfStable
#assert_standard_axioms StableIdentityComparisonSeedNormAdapter.fixed_natCard_eq_seedNorm_of_stable
#assert_standard_axioms StableIdentityComparisonSeedNormAdapter.identity_native_count_eq_two_pow_mul_seedNorm_of_stable
#assert_standard_axioms StableIdentityComparisonSeedNormAdapter.seedNormModEight_one_eq_e8TailNorm
#assert_standard_axioms StableIdentityComparisonSeedNormAdapter.seedNormIsometryOneEquivE8Norm
