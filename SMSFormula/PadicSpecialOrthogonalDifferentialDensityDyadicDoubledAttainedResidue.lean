import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDeterminantLossTwo

/-!
# The doubled attained dyadic residue image

Multiplication by two sends each original attained density residue into the
one-power-enlarged dyadic determinant-loss carrier.  This module packages that
doubled image and proves that it is exactly the image of the complete
depth-`k` principal kernel under the scaled dyadic Cayley residue map.

The converse keeps track of the source witness: its canonical residue center
determines the unique corrected principal-kernel stabilizer, whose common
original matrix lies in the shifted subgroup `H₂`.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_doubled_attained : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Twice an original attained dyadic residue, as an element of the enlarged
determinant-loss carrier. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossTwo
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceResidueIndexToDyadicDeterminantLossResidue
      a)

/-- The literal image of multiplication by two on original attained
dyadic density residues. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet
    (L : PositiveDefiniteIntegralLattice n) :
    Set
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
  Set.range
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidue

/-- The canonical ambient dyadic source point represented by the chosen
center of an attained residue. -/
def
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicResidueIndexSourcePoint
    (L : PositiveDefiniteIntegralLattice n)
    (a : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet 2 :=
  ⟨(L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      2 a).1,
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
      2 a⟩

end PositiveDefiniteIntegralLattice
