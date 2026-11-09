import SMSFormula.Applications.Unimodular.Gram
import SMSFormula.Product

/-!
# Dyadic local-density setup for unimodular lattices

This file records the first native dyadic bridge needed by the unimodular mass
application.  Classical unimodularity (`pairingDeterminant = 1`) makes the half-polar
source determinant a `2`-adic unit.  The existing determinant-depth theorem gives
Hensel lattice and quadratic depth at level `1`; the already formalized dyadic
associated-bilinear bridge adds the two powers required by Schulze--Pillot's
`2F`-dual convention.

No dyadic local density or mass factor is evaluated here.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} {L : PositiveDefiniteIntegralLattice n}

/-- A classically unimodular lattice has Schulze--Pillot Hensel exponent `3`
at the dyadic prime.  This is the uniform determinant-depth setup for the later
native dyadic local-factor computation; it does not evaluate the factor. -/
theorem isLocalDensityHenselExponent_three_of_isUnimodular
    (hL : L.IsUnimodular) :
    IsLocalDensityHenselExponent L 2 3 := by
  have hval1 : padicValInt 2 L.pairingDeterminant < 1 := by
    rw [hL]
    simp
  have hlattice1 : L.IsHenselLatticeDepth 2 1 :=
    L.isHenselLatticeDepth_of_pairingDeterminant_val_lt 2 1 hval1
  have hquadratic1 : L.IsHenselQuadraticDepth 2 1 :=
    L.isHenselQuadraticDepth_of_pairingDeterminant_val_lt 2 1 hval1
  refine
    { admissible := isLocalDensityAdmissibleExponent_of_one_le L 2 3 (by omega)
      lattice_depth := ?_
      quadratic_depth := ?_
      associated_bilinear_quadratic_depth := ?_ }
  · simpa using (hlattice1.succ L 2 1).succ L 2 (1 + 1)
  · simpa using (hquadratic1.succ L 2 1).succ L 2 (1 + 1)
  · simpa using hquadratic1.associatedBilinear_add_two_dyadic L 1



/-- Classical unimodularity makes the integral Gram matrix invertible modulo every
prime power.  This is the determinant-unit input for rewriting the local-dual
coordinate denominator to the ordinary coordinate quotient. -/
theorem matrixMod_pairingMatrix_isUnit_of_isUnimodular
    (hL : L.IsUnimodular) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsUnit (matrixMod L.pairingMatrix (primePowModulus p k)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : (matrixMod L.pairingMatrix (primePowModulus p k)).det =
      ((L.pairingDeterminant : ℤ) : ZMod (primePowModulus p k : ℕ)) := by
    simpa [matrixMod, pairingDeterminant] using
      (RingHom.map_det (Int.castRingHom (ZMod (primePowModulus p k : ℕ)))
        L.pairingMatrix).symm
  rw [hdet, hL]
  simp

/-- For a classically unimodular lattice, Schulze--Pillot's associated-bilinear
dyadic source denominator at depth three has integral integral model `2^2 ℤ^n`.  This
turns the native finite count into a concrete mod-`4` coordinate quotient count. -/
theorem associatedBilinearDualPadicDenominatorIntegralPreimage_two_three_eq_primePowCoordinateSubmodule
    (hL : L.IsUnimodular) :
    associatedBilinearDualPadicDenominatorIntegralPreimage L 2 3 =
      primePowCoordinateSubmodule (n := n) 2 2 := by
  have hF : IsUnit (matrixMod L.pairingMatrix (primePowModulus 2 2)) :=
    matrixMod_pairingMatrix_isUnit_of_isUnimodular (n := n) (L := L) hL 2 2
  rw [show (3 : ℕ) = 2 + 1 by norm_num]
  rw [associatedBilinearDualPadicDenominatorIntegralPreimage_succ_eq_localDualPadicDenominatorIntegralPreimage_dyadic]
  rw [localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule]
  rw [localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDualCoordinateSubmodule]
  exact pairingMatrixLocalDualCoordinateSubmodule_eq_primePowCoordinateSubmodule_of_zmod_isUnit
    L 2 2 hF

/-- The depth-three associated-bilinear finite count for a classically
unimodular lattice can be computed on the explicit mod-`4` coordinate quotient.
This is still only a finite-count bridge; it does not evaluate the count. -/
theorem associatedBilinearDualQuotientCount_two_three_eq_primePowCoordinateSubmodule
    (hL : L.IsUnimodular) :
    associatedBilinearDualQuotientCount L 2 3 =
      coordinateLocalDualQuotientCount L 2 3
        (primePowCoordinateSubmodule (n := n) 2 2)
        (primePowCoordinateSubmodule_rank (n := n) 2 2) := by
  unfold associatedBilinearDualQuotientCount
  exact coordinateLocalDualQuotientCount_eq_of_submodule_eq L 2 3
    (associatedBilinearDualPadicDenominatorIntegralPreimage_two_three_eq_primePowCoordinateSubmodule
      (n := n) (L := L) hL)
    (associatedBilinearDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 3)
    (primePowCoordinateSubmodule_rank (n := n) 2 2)

/-- A classically unimodular lattice has dyadic polar-discriminant norm
`2^{-n}`, since `polarDeterminant = 2^n`. -/
theorem polarDeterminant_padic_norm_two_eq_two_pow_neg_rank_of_isUnimodular
    (hL : L.IsUnimodular) :
    ‖(L.polarDeterminant : ℤ_[2])‖ = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [polarDeterminant_padic_norm_eq_padicValInt]
  rw [L.polarDeterminant_eq_two_pow_of_isUnimodular hL]
  have hval : padicValInt 2 ((2 : ℤ) ^ n) = n := by
    simp [padicValInt]
  rw [hval]
  norm_num

/-- Under classical unimodularity, the dyadic Gram-determinant norm factor is
the valuation factor with visible valuation `n`. -/
theorem gramDetPadicNormFactor_two_eq_valuationFactor_of_isUnimodular
    (hL : L.IsUnimodular) :
    gramDetPadicNormFactor L 2 =
      gramDetPadicValuationFactor 2 n n := by
  exact gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq
    L 2 n (polarDeterminant_padic_norm_two_eq_two_pow_neg_rank_of_isUnimodular hL)

/-- For a classically unimodular lattice, the native dyadic Schulze--Pillot
local factor is the fixed depth-three associated-bilinear finite quotient count
with the existing Schulze--Pillot normalization.  This specializes the native
`normalizedLocalDensity` finite-count theorem; it does not evaluate the count. -/
theorem massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_of_isUnimodular
    (hL : L.IsUnimodular) :
    L.massLocalFactor 2 =
      (((1 / 2 : ℚ) * (2 : ℚ) ^ n *
        ((2 : ℚ) ^ (3 * (n * (n - 1) / 2)))⁻¹ *
        (associatedBilinearDualQuotientCount L 2 3 : ℚ) : ℚ) : ℝ) *
        gramDetPadicNormFactor L 2 := by
  rw [massLocalFactor_eq_normalizedLocalDensity]
  rw [normalizedLocalDensity_eq_associatedBilinearDualQuotientCount L 2 3
    (isLocalDensityHenselExponent_three_of_isUnimodular hL)]
  simp [twoPadicNormInvPow, localDensityDenominatorExponent]

/-- Same depth-three dyadic finite-count formula as
`massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_of_isUnimodular`,
but with the unimodular determinant norm already rewritten as valuation `n`. -/
theorem massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_valuationFactor_of_isUnimodular
    (hL : L.IsUnimodular) :
    L.massLocalFactor 2 =
      (((1 / 2 : ℚ) * (2 : ℚ) ^ n *
        ((2 : ℚ) ^ (3 * (n * (n - 1) / 2)))⁻¹ *
        (associatedBilinearDualQuotientCount L 2 3 : ℚ) : ℚ) : ℝ) *
        gramDetPadicValuationFactor 2 n n := by
  rw [massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_of_isUnimodular hL,
    gramDetPadicNormFactor_two_eq_valuationFactor_of_isUnimodular hL]

end PositiveDefiniteIntegralLattice
