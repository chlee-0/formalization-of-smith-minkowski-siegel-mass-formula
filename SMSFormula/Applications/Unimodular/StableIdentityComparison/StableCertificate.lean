import SMSFormula.Applications.Unimodular.StableIdentityComparison.SeedNativeAdapter
import SMSFormula.Applications.Unimodular.StableIdentityComparison.SeedNormAdapter
import SMSFormula.StandardAxiomsGuard

/-!
# Pointed stable-coordinate certificate interface

This file packages the Voskresenskii second-orbit stable-coordinate input used
by the rank-uniform native adapter.  The explicit rank `9`, `17`, and `25`
certificates are checked in the surrounding modules; here they
are exposed through one common interface.  The remaining all-`k` step, the
construction of such certificates for every positive `k`, is stated as the
proposition `AllPositiveStableCertificates`.
-/

noncomputable section
open Matrix PositiveDefiniteIntegralLattice UnimodularMass

namespace StableIdentityComparisonStableCertificate

set_option maxHeartbeats 4000000

/-- A pointed stable-coordinate certificate for `typeIISeed k`.

The matrix `U` is the coordinate change from a norm-one line plus the stored
`typeIISeed k` tail to the diagonal identity form in rank `8*k+1`, modulo four.
The inverse matrix `V`, the quadratic identity modulo eight, and the image of
the distinguished line are exactly the hypotheses consumed by
`SeedNativeAdapter.lean`.
-/
structure PointedStableCertificate (k : ℕ) where
  U : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4)
  V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4)
  hUV : U * V = 1
  hVU : V * U = 1
  hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
    identityQuadraticModEight (U.mulVec x) =
      StableIdentityFixedLine.lineNorm
        (StableIdentityComparisonSeedNormAdapter.seedNormModEight k) x
  hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
    StableIdentityComparison.characteristic (8 * k + 1)

namespace PointedStableCertificate

/-- The native count relation supplied by a pointed stable-coordinate certificate. -/
theorem native_count (k : ℕ) (C : PointedStableCertificate k) :
    StableIdentityNativeAssembly.C (identityLattice (8 * k + 1)) =
      2 ^ (8 * k + 1) * StableIdentityNativeAssembly.C (typeIISeed k) :=
  StableIdentityComparisonSeedNativeAdapter.identity_native_count_eq_two_pow_mul_typeIISeed_of_stable
    k C.U C.V C.hUV C.hVU C.hQ C.hw

/-- Ordinary mass endpoint supplied by a pointed stable-coordinate certificate. -/
theorem seed_mass (k : ℕ) (hk : 0 < k) (C : PointedStableCertificate k) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) :=
  StableIdentityComparisonSeedNativeAdapter.seed_mass_of_stable_count
    k hk C.U C.V C.hUV C.hVU C.hQ C.hw

/-- Literal genus-sum endpoint supplied by a pointed stable-coordinate certificate. -/
theorem seed_literal_sum (k : ℕ) (hk : 0 < k) (C : PointedStableCertificate k) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) :=
  StableIdentityComparisonSeedNativeAdapter.seed_literal_sum_of_stable_count
    k hk C.U C.V C.hUV C.hVU C.hQ C.hw

end PointedStableCertificate

/-- The checked rank-nine stable certificate for `typeIISeed 1`. -/
def certificateOne : PointedStableCertificate 1 where
  U := StableIdentityComparisonCertificate.stableNine.map (Int.cast : ℤ → ZMod 4)
  V := StableIdentityComparisonCertificate.stableNineInverse.map (Int.cast : ℤ → ZMod 4)
  hUV := StableIdentityComparisonCertificate.stableNine_right_inverse_four
  hVU := StableIdentityComparisonCertificate.stableNine_left_inverse_four
  hQ := by
    intro x
    calc
      identityQuadraticModEight
          ((StableIdentityComparisonCertificate.stableNine.map
            (Int.cast : ℤ → ZMod 4)).mulVec x)
          = StableIdentityComparisonCertificate.onePlusE8NormModEight x :=
            StableIdentityComparisonCertificate.stableNine_identityQuadraticModEight_eq_onePlusE8Norm x
      _ = StableIdentityFixedLine.lineNorm
            StableIdentityComparisonCountAdapter.e8TailNormModEight x := by
            simpa using congrFun
              StableIdentityComparisonCountAdapter.onePlusE8NormModEight_eq_lineNorm x
      _ = StableIdentityFixedLine.lineNorm
            (StableIdentityComparisonSeedNormAdapter.seedNormModEight 1) x := by
            rw [StableIdentityComparisonSeedNormAdapter.seedNormModEight_one_eq_e8TailNorm]
  hw := by
    decide

/-- The proposition that a certificate exists for every
positive seed rank. -/
abbrev AllPositiveStableCertificates : Prop :=
  ∀ k : ℕ, 0 < k → Nonempty (PointedStableCertificate k)

/-- All positive E8-power seed masses follow from stable-coordinate certificates
in all positive ranks. -/
theorem all_positive_seed_mass_of_certificates
    (hcert : AllPositiveStableCertificates) (k : ℕ) (hk : 0 < k) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) := by
  rcases hcert k hk with ⟨C⟩
  exact C.seed_mass k hk

/-- Literal genus-sum form of the all-positive conditional endpoint. -/
theorem all_positive_seed_literal_sum_of_certificates
    (hcert : AllPositiveStableCertificates) (k : ℕ) (hk : 0 < k) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) := by
  rcases hcert k hk with ⟨C⟩
  exact C.seed_literal_sum k hk

end StableIdentityComparisonStableCertificate

#assert_standard_axioms StableIdentityComparisonStableCertificate.PointedStableCertificate.native_count
#assert_standard_axioms StableIdentityComparisonStableCertificate.PointedStableCertificate.seed_mass
#assert_standard_axioms StableIdentityComparisonStableCertificate.PointedStableCertificate.seed_literal_sum
#assert_standard_axioms StableIdentityComparisonStableCertificate.all_positive_seed_mass_of_certificates
#assert_standard_axioms StableIdentityComparisonStableCertificate.all_positive_seed_literal_sum_of_certificates
