import SMSFormula.Applications.Unimodular.PadicLifting.ResidueLift
import SMSFormula.Applications.Unimodular.GenusClosure.TypeIModEight
import SMSFormula.Applications.Unimodular.DirectPeeling.TargetBridge

noncomputable section

namespace PositiveDefiniteIntegralLattice
open UnimodularPadicLift

theorem pairingMatrix_padic_isUnit_of_unimodular {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) (prime : ℕ) [Fact prime.Prime] :
    IsUnit (lattice.pairingMatrix_padic prime) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit (lattice.pairingMatrix.map (Int.cast : ℤ → ℤ_[prime])).det
  rw [← Int.cast_det, show lattice.pairingMatrix.det = 1 from hunimodular]
  simp

theorem pairingMatrix_padic_reduces_two_three {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n) :
    (lattice.pairingMatrix_padic 2).map (PadicInt.toZModPow 3) =
      lattice.pairingMatrix.map (Int.cast : ℤ → ZMod 8) := by
  ext row col
  simp [pairingMatrix_padic]

theorem isLocallyIsometricAt_two_of_unimodular_gram_certificate {n : ℕ}
    (lattice reference : PositiveDefiniteIntegralLattice n) (hreference : reference.IsUnimodular)
    (certificate : TypeIIModEightCertificates.GramCongruenceCertificate
      (reference.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (lattice.pairingMatrix.map (Int.cast : ℤ → ZMod 8))) :
    lattice.IsLocallyIsometricAt reference 2 := by
  apply exists_dyadic_unit_isometry_of_gram_certificate
    (reference.pairingMatrix_padic 2) (lattice.pairingMatrix_padic 2)
    (reference.form_symm.map _) (lattice.form_symm.map _)
    (pairingMatrix_padic_isUnit_of_unimodular reference hreference 2)
  rw [pairingMatrix_padic_reduces_two_three reference, pairingMatrix_padic_reduces_two_three lattice]
  exact certificate

theorem isLocallyIsometricAt_two_identity_of_typeIUnimodular {n : ℕ}
    (lattice : PositiveDefiniteIntegralLattice n) (hunimodular : lattice.IsUnimodular)
    (htypeI : lattice.HasOddNorm) :
    lattice.IsLocallyIsometricAt (identityLattice n) 2 := by
  obtain ⟨certificate⟩ := UnimodularGenusClosure.normalizes_typeI_unimodular
    lattice hunimodular htypeI
  apply isLocallyIsometricAt_two_of_unimodular_gram_certificate lattice (identityLattice n)
    (identityLattice_isUnimodular n)
  have hidentity : (identityLattice n).pairingMatrix.map (Int.cast : ℤ → ZMod 8) = 1 := by simp
  simpa only [hidentity] using certificate.symm

theorem isLocallyIsometricAt_two_typeIISeed_of_typeIIUnimodular
    (power : ℕ) (hpower : 0 < power) (lattice : PositiveDefiniteIntegralLattice (8 * power))
    (hunimodular : lattice.IsUnimodular) (htypeII : lattice.HasEvenNorms) :
    lattice.IsLocallyIsometricAt (typeIISeed power) 2 := by
  let left := TypeIIDirectPeeling.typeIIUnimodularRecursiveSplitCertificate
    power hpower lattice hunimodular htypeII
  let right := TypeIIDirectPeeling.typeIIUnimodularRecursiveSplitCertificate
    power hpower (typeIISeed power) (typeIISeed_isUnimodular power)
      (typeIISeed_hasEvenNorms power)
  exact isLocallyIsometricAt_two_of_unimodular_gram_certificate lattice (typeIISeed power)
    (typeIISeed_isUnimodular power) (right.trans left.symm)

#assert_standard_axioms isLocallyIsometricAt_two_of_unimodular_gram_certificate
#assert_standard_axioms isLocallyIsometricAt_two_identity_of_typeIUnimodular
#assert_standard_axioms isLocallyIsometricAt_two_typeIISeed_of_typeIIUnimodular

end PositiveDefiniteIntegralLattice
