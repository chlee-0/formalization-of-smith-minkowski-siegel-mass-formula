import SMSFormula.RationalCliffordSpinCandidateAlmostEverywhereIntegralLifting
import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction

/-!
# Integral comap volume outside the lifting bad set

The lifted exceptional-coset calculation leaves the Haar mass of the inverse
image of the integral `SO` subgroup.  Outside the already named finite
integral-lifting bad set, this inverse image is exactly the literal
point-and-inverse integral Clifford--Spin locus.  Its chart-glued Haar mass is
therefore the existing integral volume used by the coherent block correction.

This statement does not claim the equality at the finitely many lifting-bad
places.  In particular, it introduces neither an integrality hypothesis nor a
replacement local normalization at those remaining places.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance integralComapVolumePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Away from the lifting denominator set, a local Clifford--Spin point is
integral exactly when its represented special-orthogonal image is integral. -/
theorem heightOnePadicCliffordSpinCandidateIsIntegral_iff_pointMap_mem_integralSubgroup_of_not_mem_liftingBadPlaces
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces)
    (g : V.HeightOnePadicCliffordSpinCandidateGroup v) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v g ↔
      V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g ∈
        V.heightOnePadicSpecialOrthogonalIntegralSubgroup v := by
  constructor
  · intro hg
    exact V.heightOnePadicCliffordSpinCandidateIsIntegral_pointMap v g hg
  · intro hg
    have hgcoords :=
      (V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic
        v
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g)).1 hg
    have hforward :=
      V.heightOnePadicCliffordSpinCandidateForwardCoordinates_mem_padicInt
        v hv g (by
          intro i j
          simpa [
            cliffordSpinCandidateGroupToSpecialOrthogonal,
            cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
            V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix,
            cliffordSpinCandidateMatrixOfCoordinateAlgHom,
            CliffordSpinCandidatePointData.matrixGroup_coe] using
            hgcoords.1 i j)
    have hinverse :=
      V.heightOnePadicCliffordSpinCandidateForwardCoordinates_mem_padicInt
        v hv (g⁻¹) (by
          intro i j
          have hmap_inv :
              V.cliffordSpinCandidateGroupToSpecialOrthogonal
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (g⁻¹) =
                (V.cliffordSpinCandidateGroupToSpecialOrthogonal
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g)⁻¹ := by
            rw [map_inv]
          have hij :
              (V.cliffordSpinCandidateGroupToSpecialOrthogonal
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (g⁻¹)).1.1.1 i j ∈
                  PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
            rw [hmap_inv]
            exact hgcoords.2 i j
          simpa [
            cliffordSpinCandidateGroupToSpecialOrthogonal,
            cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup,
            V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix,
            cliffordSpinCandidateMatrixOfCoordinateAlgHom,
            CliffordSpinCandidatePointData.matrixGroup_coe] using hij)
    exact
      (V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic v g).2
        ⟨hforward.1, hforward.2, hinverse.1, hinverse.2⟩

end RationalQuadraticSpaceMatrix

end
