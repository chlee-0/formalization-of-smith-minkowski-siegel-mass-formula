import SMSFormula.RationalIsotropy
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Quadratic norms over finite fields

This module exposes the finite-field norm-surjectivity fact needed by the
odd-prime local norm calculation without importing the global product layer.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

private lemma quadraticAlgebra_algebraNorm_eq_norm
    {K : Type*} [Field K] (d : K)
    [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
    (z : QuadraticAlgebra K d 0) :
    Algebra.norm K z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm z]
  congr 1

/-- Over a finite field, the norm from a nonsplit quadratic algebra represents
every scalar. -/
theorem quadraticNormRepresents_finiteField_of_not_isSquare
    {K : Type*} [Field K] [Finite K]
    (d c : K) (hd : ¬ IsSquare d) :
    quadraticNormRepresents d c := by
  letI : Fact (∀ r : K, r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hd
    exact ⟨r, by simpa [pow_two] using hr.symm⟩⟩
  letI : Finite (QuadraticAlgebra K d 0) :=
    Finite.of_injective (QuadraticAlgebra.equivProd d 0)
      (QuadraticAlgebra.equivProd d 0).injective
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective K (QuadraticAlgebra K d 0) c
  exact ⟨z, by
    rw [← quadraticAlgebra_algebraNorm_eq_norm]
    exact hz⟩

end PositiveDefiniteIntegralLattice
