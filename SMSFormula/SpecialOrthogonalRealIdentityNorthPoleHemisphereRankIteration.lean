import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereTransitionNormalization

/-!
# Iterating the elementary-normalized identity differential mass

The consecutive-rank relation is packaged using the explicit inverse
fixed-to-elementary determinant factor and iterated from rank parameter zero.
The initial normalized mass and the finite sphere-step product are deliberately
left unevaluated.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory
  BigOperators

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

/-- Identity differential mass with the arbitrary rational tangent basis
converted explicitly to the elementary tangent basis in the corresponding
matrix rank. -/
def identitySpecialOrthogonalElementaryNormalizedDifferentialMass
    (n : ℕ) : ℝ≥0∞ :=
  (Real.toNNReal
    |(identitySpecialOrthogonalFixedElementaryDetScalar
      (n + 1) : ℝ)| : ℝ≥0∞)⁻¹ *
    identitySpecialOrthogonalDifferentialMeasure n Set.univ

/-- The elementary-normalized differential mass gains exactly the full sphere
step when the rank parameter is increased by one. -/
theorem identitySpecialOrthogonalElementaryNormalizedDifferentialMass_succ
    (n : ℕ) :
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass (n + 1) =
      (2 * identitySpecialOrthogonalSphereStep (n + 2)) *
        identitySpecialOrthogonalElementaryNormalizedDifferentialMass n := by
  simpa [
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass,
    Nat.add_assoc] using
    identitySpecialOrthogonalElementaryNormalizedHigherMass_eq_two_sphereStep_mul_elementaryNormalizedLowerMass
      n

/-- Finite iteration of the elementary-normalized rank relation.  Neither the
initial normalized mass nor the product of full sphere steps is evaluated. -/
theorem identitySpecialOrthogonalElementaryNormalizedDifferentialMass_eq_prod
    (n : ℕ) :
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass n =
      (∏ k ∈ Finset.range n,
        (2 * identitySpecialOrthogonalSphereStep (k + 2))) *
        identitySpecialOrthogonalElementaryNormalizedDifferentialMass 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [
        identitySpecialOrthogonalElementaryNormalizedDifferentialMass_succ,
        ih,
        Finset.prod_range_succ]
      ac_rfl

end PositiveDefiniteIntegralLattice
