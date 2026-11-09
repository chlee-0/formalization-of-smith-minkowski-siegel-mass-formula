import SMSFormula.FiniteDualBasisFaithfullyFlat
import SMSFormula.RationalCliffordSpinCandidateCoordinateHopf

/-!
# Rank-two faithful-flatness precursor for the Spin candidate

This file specializes the finite-dual-basis criterion to the injective
coordinate Hopf map of the Spin-candidate cover. The bundled data state the
two equations supplied by the inverse rank-two torsor canonical map and a
trace lift into the `SO` coordinate ring.

The trace lift is the exact remaining effective-quotient input: it asserts
that the involution trace, which is visibly invariant, actually descends to
the implemented base coordinate ring. No such descent is inferred here from
the represented torsor identity or scheme surjectivity.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The coordinate map makes the Spin-candidate coordinate ring an algebra
over the special-orthogonal coordinate ring. -/
noncomputable instance cliffordSpinCandidateOverSpecialOrthogonalCoordinateAlgebra :
    Algebra V.specialOrthogonalCoordinateRing
      V.cliffordSpinCandidateCoordinateRing :=
  V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.toAlgebra

/-- The finite tensor witness and trace descent needed by the elementary
rank-two torsor flatness calculation. -/
structure CliffordSpinCandidateRankTwoFlatnessData where
  size : ℕ
  sigma : V.cliffordSpinCandidateCoordinateRing ≃ₐ[
    V.specialOrthogonalCoordinateRing] V.cliffordSpinCandidateCoordinateRing
  trace : V.cliffordSpinCandidateCoordinateRing →ₗ[
    V.specialOrthogonalCoordinateRing] V.specialOrthogonalCoordinateRing
  trace_spec : ∀ b, algebraMap V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing (trace b) = b + sigma b
  left : Fin size → V.cliffordSpinCandidateCoordinateRing
  right : Fin size → V.cliffordSpinCandidateCoordinateRing
  canonical_one : ∑ i, left i * right i = 1
  canonical_zero : ∑ i, left i * sigma (right i) = 0

/-- The rank-two descent data give faithful flatness of the Spin-candidate
coordinate map. -/
theorem faithfullyFlat_of_rankTwoFlatnessData
    (D : V.CliffordSpinCandidateRankTwoFlatnessData) :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat := by
  change (algebraMap V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing).FaithfullyFlat
  exact RingHom.faithfullyFlat_of_involution_torsor_witness
    D.sigma D.trace D.trace_spec D.left D.right D.canonical_one
    D.canonical_zero
    V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_injective

end RationalQuadraticSpaceMatrix
