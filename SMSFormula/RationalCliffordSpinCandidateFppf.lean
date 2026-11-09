import SMSFormula.FaithfullyFlatRightTensorDescent
import SMSFormula.RationalCliffordSpinCandidateInvariantAlgebraicClosureCover
import SMSFormula.RationalCliffordSpinCandidateInvariantGroupScheme
import SMSFormula.RationalSpecialOrthogonalReduced
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The Spin-candidate cover is fppf

The literal invariant quotient agrees with the implemented special
orthogonal carrier after faithfully descending their completed isomorphism
over `AlgebraicClosure Q`.  The rank-two invariant criterion then makes the
actual Spin coordinate map faithfully flat, completing its fppf property.
-/

noncomputable section

open TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev B := V.cliffordSpinCandidateCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

local instance fppfInvariantCommRing : CommRing V.C :=
  V.negOneInvariantSubalgebra.toCommRing

local instance fppfInvariantCommSemiring : CommSemiring V.C :=
  (fppfInvariantCommRing V).toCommSemiring

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance fppfSourceTensorCommRing : CommRing (V.A ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.A) (B := Qbar)

local instance fppfInvariantTensorCommRing : CommRing (V.C ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.C) (B := Qbar)

local instance fppfSourceTensorCommSemiring : CommSemiring (V.A ⊗[ℚ] Qbar) :=
  (fppfSourceTensorCommRing V).toCommSemiring

local instance fppfInvariantTensorCommSemiring : CommSemiring (V.C ⊗[ℚ] Qbar) :=
  (fppfInvariantTensorCommRing V).toCommSemiring

set_option backward.isDefEq.respectTransparency false in
/-- Faithful scalar descent identifies the implemented special orthogonal
coordinate ring with the full fixed subalgebra. -/
theorem specialOrthogonalToNegOneInvariantAlgHom_bijective :
    Function.Bijective V.specialOrthogonalToNegOneInvariantRatAlgHom := by
  apply Algebra.TensorProduct.bijective_of_mapRightAlgHom
    (R := ℚ) (K := Qbar) (A := V.A) (B := V.C)
      V.specialOrthogonalToNegOneInvariantRatAlgHom
  simpa only [specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom,
    specialOrthogonalToNegOneInvariantRatAlgHom] using
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_bijective

/-- The implemented special orthogonal coordinate ring is algebra-equivalent
to the literal invariant quotient coordinate ring. -/
noncomputable def specialOrthogonalToNegOneInvariantAlgEquiv :
    V.A ≃ₐ[ℚ] V.C :=
  AlgEquiv.ofBijective V.specialOrthogonalToNegOneInvariantRatAlgHom
    V.specialOrthogonalToNegOneInvariantAlgHom_bijective

@[simp]
theorem specialOrthogonalToNegOneInvariantAlgEquiv_apply (x : V.A) :
    V.specialOrthogonalToNegOneInvariantAlgEquiv x =
      V.specialOrthogonalToNegOneInvariantRatAlgHom x :=
  rfl

/-- The actual Spin-candidate coordinate map is faithfully flat. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_faithfullyFlat :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat :=
  V.faithfullyFlat_of_negOneInvariant_surjective
    V.specialOrthogonalToNegOneInvariantAlgHom_bijective.surjective

/-- The completed Spin-candidate morphism to the special orthogonal group is
fppf. -/
theorem cliffordSpinCandidateToSpecialOrthogonalFppf :
    V.CliffordSpinCandidateToSpecialOrthogonalFppf :=
  V.cliffordSpinCandidateToSpecialOrthogonalFppf_iff_faithfullyFlat.mpr
    V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_faithfullyFlat

end RationalQuadraticSpaceMatrix
