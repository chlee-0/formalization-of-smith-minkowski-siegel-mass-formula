import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicUniformAttainedFiber

/-!
# Cardinality of the doubled attained dyadic residue image

The original attained dyadic residues map surjectively onto their literal
doubled image.  Every fiber of this map is one of the already computed
doubled-attained fibers, hence has cardinal `2^d`.  The finite constant-fiber
theorem therefore gives the exact product relation between the doubled image
and the original attained residue count.

No additive closure, quotient descent, dyadic gauge identity, or global prime
product is asserted here.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_doubled_attained_cardinality : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The finite subtype of residues in the literal doubled attained image. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex
    (L : PositiveDefiniteIntegralLattice n) :=
  ↥L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet

/-- The doubling map with its image as codomain. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        2 →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex :=
  fun a ↦
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
        a,
      ⟨a, rfl⟩⟩

/-- The doubled-image map is surjective by its range witness. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap := by
  intro y
  rcases y.2 with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/-- A chosen original attained preimage of a doubled attained image point. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResiduePreimage
    (L : PositiveDefiniteIntegralLattice n)
    (y : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2 :=
  Classical.choose
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap_surjective
      y)

/-- The chosen attained preimage maps literally to the prescribed doubled
image point. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap_preimage
    (L : PositiveDefiniteIntegralLattice n)
    (y : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResiduePreimage
          y) = y :=
  Classical.choose_spec
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap_surjective
      y)

/-- The fiber of the doubled-image map is the fiber of the doubling map over
the chosen attained preimage. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMapFiberEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (y : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex) :
    {a :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          2 //
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap
          a = y} ≃
      {a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            2 //
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
            a =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResiduePreimage
              y)} where
  toFun a := by
    refine ⟨a.1, ?_⟩
    have ha := congrArg Subtype.val a.2
    have hy := congrArg Subtype.val
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap_preimage
        y)
    exact ha.trans hy.symm
  invFun a := by
    refine ⟨a.1, ?_⟩
    apply Subtype.ext
    have hy := congrArg Subtype.val
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap_preimage
        y)
    exact a.2.trans hy
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every fiber of the doubled-image map has cardinal `2^d`. -/
theorem
    natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMapFiber
    (L : PositiveDefiniteIntegralLattice n)
    (y : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex) :
    Nat.card
        {a :
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
              2 //
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap
              a = y} =
      2 ^ Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) := by
  rw [Nat.card_congr
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMapFiberEquiv
      y)]
  exact
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueFiber
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResiduePreimage
        y)

/-- The doubled attained image cardinal times the one-layer fiber cardinal is
the original attained residue cardinal. -/
theorem
    natCard_dyadicDoubledAttainedResidueIndex_mul_two_pow_tangentRank
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex *
        2 ^ Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
      Nat.card
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          2) := by
  letI : Fintype
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        2) :=
    (L.finite_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      2).fintype
  letI : Fintype
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex :=
    Set.toFinite
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet |>.fintype
  symm
  exact nat_card_eq_mul_of_fiber_card
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMap
    (2 ^ Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix))
    L.natCard_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueMapFiber

/-- The same product identity with the original attained count written as
the `ncard` of its literal residue image. -/
theorem
    natCard_dyadicDoubledAttainedResidueIndex_mul_two_pow_tangentRank_eq_residueImage_ncard
    (L : PositiveDefiniteIntegralLattice n) :
    Nat.card
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueIndex *
        2 ^ Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        2).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact
    L.natCard_dyadicDoubledAttainedResidueIndex_mul_two_pow_tangentRank

end PositiveDefiniteIntegralLattice
