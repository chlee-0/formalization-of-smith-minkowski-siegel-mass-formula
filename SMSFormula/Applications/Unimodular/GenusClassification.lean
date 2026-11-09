import SMSFormula.Applications.Unimodular.PadicLifting.OddPrimeClassification
import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped MatrixOrder

namespace PositiveDefiniteIntegralLattice

theorem isLocallyIsometricAtInfinity_of_positiveDefinite {rank : ℕ}
    (lattice reference : PositiveDefiniteIntegralLattice rank) :
    lattice.IsLocallyIsometricAtInfinity reference := by
  have factor (model : PositiveDefiniteIntegralLattice rank) :
      ∃ root : Matrix (Fin rank) (Fin rank) ℝ, IsUnit root ∧
        model.pairingMatrix_real = root.transpose * root := by
    obtain ⟨root, hroot, hgram⟩ :=
      CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp model.form_posDef.isStrictlyPositive
    refine ⟨root, hroot, ?_⟩
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hgram
  obtain ⟨left, hleft, hleftGram⟩ := factor lattice
  obtain ⟨right, hright, hrightGram⟩ := factor reference
  refine ⟨right⁻¹ * left, (Matrix.isUnit_nonsing_inv_iff.mpr hright).mul hleft, ?_⟩
  have hinverse := Matrix.mul_nonsing_inv right ((Matrix.isUnit_iff_isUnit_det right).mp hright)
  have hcancel : right * (right⁻¹ * left) = left := by
    rw [← Matrix.mul_assoc, hinverse, Matrix.one_mul]
  calc
    (right⁻¹ * left).transpose * reference.pairingMatrix_real * (right⁻¹ * left) =
        (right * (right⁻¹ * left)).transpose * (right * (right⁻¹ * left)) := by
      rw [hrightGram]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = left.transpose * left := by rw [hcancel]
    _ = lattice.pairingMatrix_real := hleftGram.symm

theorem isSameGenus_identity_of_typeIUnimodular {rank : ℕ}
    (lattice : PositiveDefiniteIntegralLattice rank) (hunimodular : lattice.IsUnimodular)
    (htypeI : lattice.HasOddNorm) : lattice.IsSameGenus (identityLattice rank) := by
  constructor
  · intro prime hprime
    by_cases htwo : prime = 2
    · subst prime
      exact isLocallyIsometricAt_two_identity_of_typeIUnimodular lattice hunimodular htypeI
    · exact isLocallyIsometricAt_odd_prime_of_unimodular lattice (identityLattice rank)
        hunimodular (identityLattice_isUnimodular rank) prime htwo
  · exact isLocallyIsometricAtInfinity_of_positiveDefinite lattice (identityLattice rank)

theorem isSameGenus_typeIISeed_of_typeIIUnimodular
    (power : ℕ) (hpower : 0 < power) (lattice : PositiveDefiniteIntegralLattice (8 * power))
    (hunimodular : lattice.IsUnimodular) (htypeII : lattice.HasEvenNorms) :
    lattice.IsSameGenus (typeIISeed power) := by
  constructor
  · intro prime hprime
    by_cases htwo : prime = 2
    · subst prime
      exact isLocallyIsometricAt_two_typeIISeed_of_typeIIUnimodular
        power hpower lattice hunimodular htypeII
    · exact isLocallyIsometricAt_odd_prime_of_unimodular lattice (typeIISeed power)
        hunimodular (typeIISeed_isUnimodular power) prime htwo
  · exact isLocallyIsometricAtInfinity_of_positiveDefinite lattice (typeIISeed power)

#assert_standard_axioms isLocallyIsometricAtInfinity_of_positiveDefinite
#assert_standard_axioms isSameGenus_identity_of_typeIUnimodular
#assert_standard_axioms isSameGenus_typeIISeed_of_typeIIUnimodular

end PositiveDefiniteIntegralLattice
