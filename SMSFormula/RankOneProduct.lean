import SMSFormula.RankOneLocalDensity
import SMSFormula.RankOneMass
import SMSFormula.MassProductDefinitions
import SMSFormula.ArchimedeanMassFactor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Rank-one ordered local product and the mass normalization

The inverse local products converge to one half. The
archimedean factor is two, so their product is one. The ordinary full-O
mass is one half. Thus the rank-at-least-two mass formula, with the same
normalization, does not extend to rank one.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every cutoff containing the dyadic prime has the same rank-one product. -/
theorem massPartialPrimeInverseProduct_rank_one
    (L : PositiveDefiniteIntegralLattice 1) (N : ℕ) (hN : 2 ≤ N) :
    massPartialPrimeInverseProduct L N = (1 / 2 : ℝ) := by
  classical
  unfold massPartialPrimeInverseProduct massFinitePrimeInverseProduct
  rw [Finset.prod_eq_single (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime})]
  · norm_num [massLocalInverseFactorAtPrime, massLocalFactorAtPrime,
      massLocalFactor, normalizedLocalDensity_rank_one]
  · intro q _ hq
    have htwo : q.1 ≠ 2 := by
      intro h
      exact hq (Subtype.ext h)
    simp [massLocalInverseFactorAtPrime, massLocalFactorAtPrime,
      massLocalFactor, normalizedLocalDensity_rank_one, htwo]
  · intro h
    exact False.elim (h ((mem_rationalPrimesUpTo_iff N _).mpr hN))

/-- Ordered-prime convergence uses the literal local factors of the same
rank-one lattice, for every positive coefficient. -/
theorem massLocalInverseProductTendsTo_rank_one (L : PositiveDefiniteIntegralLattice 1) :
    L.massLocalInverseProductTendsTo (1 / 2 : ℝ) := by
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  exact Filter.eventually_atTop.mpr ⟨2, fun N hN =>
    (massPartialPrimeInverseProduct_rank_one L N hN).symm⟩

/-- The original archimedean factor in rank one. -/
theorem archimedeanMassFactor_one : archimedeanMassFactor 1 = 2 := by
  unfold archimedeanMassFactor
  norm_num [Finset.prod_range_succ, Real.Gamma_one_half_eq]
  rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add Real.pi_pos]
  norm_num

/-- A rank-one lattice cannot satisfy the unchanged rank-at-least-two
mass/product endpoint. This is a normalization obstruction, not a failed
convergence statement. -/
theorem not_exists_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_one
    (L : PositiveDefiniteIntegralLattice 1) :
    ¬ ∃ P : ℝ, L.massLocalInverseProductTendsTo P ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) = archimedeanMassFactor 1 * P := by
  rintro ⟨P, hP, hmass⟩
  have heq : P = (1 / 2 : ℝ) := tendsto_nhds_unique hP
    (massLocalInverseProductTendsTo_rank_one L)
  rw [heq, archimedeanMassFactor_one, ordinaryGenusMass_eq_one_half_rank_one] at hmass
  norm_num at hmass

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.archimedeanMassFactor_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.not_exists_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_one
