import SMSFormula.BinaryNormCharacterReciprocity

/-!
# The rank-two Smith--Minkowski--Siegel mass formula

The Picard image has index two in the finite Bad product.
The finite reduction identifies the same positive ordered local
product with the ordinary full-orthogonal genus mass of the same lattice.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every actual rank-two lattice has one positive ordered inverse-product
limit whose product-side value is its ordinary full-O genus mass. -/
theorem exists_pos_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_two
    (K : PositiveDefiniteIntegralLattice 2) :
    ∃ P : ℝ, 0<P ∧ massLocalInverseProductTendsTo K P ∧
      ((ordinaryGenusMass K : ℚ) : ℝ)=archimedeanMassFactor 2*P := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact K.binaryMassFormula_iff_localNormImage_index_two.mpr
    K.binaryBadLocalNormImage_index_two

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_pos_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_two
