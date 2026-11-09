import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereBaseRank

/-!
# The elementary-normalized identity compact-group Gamma volume

This file substitutes the internally proved `SO(1)` base mass into the finite
rank iteration and evaluates the resulting product of full Euclidean sphere
steps.  The arbitrary rational tangent bases remain visible only through the
elementary-normalized mass; no higher-rank fixed-basis
determinant is assigned a numerical value.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory
  BigOperators

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

/-- The elementary-normalized differential mass is exactly the finite product
of the internally computed full sphere steps. -/
theorem
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass_eq_sphereStep_prod
    (n : ℕ) :
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass n =
      ∏ k ∈ Finset.range n,
        (2 * identitySpecialOrthogonalSphereStep (k + 2)) := by
  rw [identitySpecialOrthogonalElementaryNormalizedDifferentialMass_eq_prod,
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass_zero,
    mul_one]

/-- The real exponents contributed by the sphere dimensions `2, ..., n + 1`
sum to `n * (n + 3) / 4`. -/
private theorem identitySphereStepExponent_sum (n : ℕ) :
    ∑ k ∈ Finset.range n, (((k + 2 : ℕ) : ℝ) / 2) =
      (n : ℝ) * ((n : ℝ) + 3) / 4 := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Product algebra for the positive real representatives of the full sphere
steps. -/
private theorem identityFullSphereStepRealProduct_eq_gamma
    (n : ℕ) :
    (∏ k ∈ Finset.range n,
      (2 : ℝ) *
        (Real.pi ^ (((k + 2 : ℕ) : ℝ) / 2) /
          Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) =
      (2 : ℝ) ^ n *
          Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
        (∏ k ∈ Finset.range n,
          Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_div_distrib, ← Real.rpow_sum_of_pos Real.pi_pos,
    identitySphereStepExponent_sum]
  ring

/-- One full sphere step is the `ENNReal.ofReal` image of its positive real
Gamma expression. -/
private theorem two_mul_identitySpecialOrthogonalSphereStep_eq_ofReal
    (m : ℕ) :
    2 * identitySpecialOrthogonalSphereStep m =
      ENNReal.ofReal
        ((2 : ℝ) *
          (Real.pi ^ ((m : ℝ) / 2) /
            Real.Gamma ((m : ℝ) / 2))) := by
  rw [identitySpecialOrthogonalSphereStep, ← ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by positivity)]

/-- The finite product of internally normalized full sphere steps has the
classical compact-group Gamma value. -/
theorem identitySpecialOrthogonalFullSphereStepProduct_eq_gamma
    (n : ℕ) :
    (∏ k ∈ Finset.range n,
      (2 * identitySpecialOrthogonalSphereStep (k + 2))) =
      ENNReal.ofReal
        ((2 : ℝ) ^ n *
            Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
          (∏ k ∈ Finset.range n,
            Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) := by
  calc
    (∏ k ∈ Finset.range n,
        (2 * identitySpecialOrthogonalSphereStep (k + 2))) =
        ∏ k ∈ Finset.range n,
          ENNReal.ofReal
            ((2 : ℝ) *
              (Real.pi ^ (((k + 2 : ℕ) : ℝ) / 2) /
                Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) := by
          apply Finset.prod_congr rfl
          intro k hk
          exact
            two_mul_identitySpecialOrthogonalSphereStep_eq_ofReal (k + 2)
    _ = ENNReal.ofReal
        (∏ k ∈ Finset.range n,
          (2 : ℝ) *
            (Real.pi ^ (((k + 2 : ℕ) : ℝ) / 2) /
              Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) := by
          rw [ENNReal.ofReal_prod_of_nonneg]
          intro k hk
          positivity
    _ = ENNReal.ofReal
        ((2 : ℝ) ^ n *
            Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
          (∏ k ∈ Finset.range n,
            Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) := by
          rw [identityFullSphereStepRealProduct_eq_gamma]

/-- Explicit Gamma value of the elementary-normalized differential mass of
the identity-model compact special orthogonal group. -/
theorem
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass_eq_gamma
    (n : ℕ) :
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass n =
      ENNReal.ofReal
        ((2 : ℝ) ^ n *
            Real.pi ^ ((n : ℝ) * ((n : ℝ) + 3) / 4) /
          (∏ k ∈ Finset.range n,
            Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))) := by
  rw [
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass_eq_sphereStep_prod,
    identitySpecialOrthogonalFullSphereStepProduct_eq_gamma]

end PositiveDefiniteIntegralLattice
