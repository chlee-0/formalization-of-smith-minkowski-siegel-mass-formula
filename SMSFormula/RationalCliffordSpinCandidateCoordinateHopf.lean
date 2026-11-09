import SMSFormula.AffinePointGroupHopf
import SMSFormula.RationalCliffordSpinCandidateCoordinateHopfPrecursor
import SMSFormula.RationalSpecialOrthogonalReduced
import Mathlib.RingTheory.Bialgebra.Hom

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The natural group law on special-orthogonal algebra points, packaged as
the data needed to recover the representing Hopf algebra. -/
def specialOrthogonalAffinePointGroupData :
    AffinePointGroupData ℚ V.specialOrthogonalCoordinateRing where
  pointGroup B := V.specialOrthogonalCoordinateAlgHomGroup B
  map f := V.specialOrthogonalCoordinateAlgHomMap f
  map_apply f F := V.specialOrthogonalCoordinateAlgHomMap_apply f F

/-- The natural group law on Spin-candidate algebra points, packaged as the
data needed to recover the representing Hopf algebra. -/
def cliffordSpinCandidateAffinePointGroupData :
    AffinePointGroupData ℚ V.cliffordSpinCandidateCoordinateRing where
  pointGroup B := V.cliffordSpinCandidateCoordinateAlgHomGroup B
  map f := V.cliffordSpinCandidateCoordinateAlgHomMap _ f
  map_apply f F := by
    change (V.cliffordSpinCandidateCoordinateAlgHomMap _ f) F = f.comp F
    rfl

/-- The Hopf-algebra structure on the completed special-orthogonal coordinate
ring induced by its natural group-valued functor of points. -/
noncomputable instance specialOrthogonalCoordinateHopfAlgebra :
    HopfAlgebra ℚ V.specialOrthogonalCoordinateRing :=
  V.specialOrthogonalAffinePointGroupData.hopfAlgebra

/-- The Hopf-algebra structure on the completed Spin-candidate coordinate ring
induced by its natural group-valued functor of points. -/
noncomputable instance cliffordSpinCandidateCoordinateHopfAlgebra :
    HopfAlgebra ℚ V.cliffordSpinCandidateCoordinateRing :=
  V.cliffordSpinCandidateAffinePointGroupData.hopfAlgebra

/-- The bundled special-orthogonal comultiplication is the explicit
coordinate comultiplication. -/
theorem specialOrthogonalCoordinate_comulAlgHom :
    Bialgebra.comulAlgHom ℚ V.specialOrthogonalCoordinateRing =
      V.specialOrthogonalCoordinateComul := rfl

/-- The bundled special-orthogonal counit is the explicit coordinate
counit. -/
theorem specialOrthogonalCoordinate_counitAlgHom :
    Bialgebra.counitAlgHom ℚ V.specialOrthogonalCoordinateRing =
      V.specialOrthogonalCoordinateCounit := rfl

/-- The bundled special-orthogonal antipode is the explicit inverse
of the universal algebra point. -/
theorem specialOrthogonalCoordinate_antipode :
    HopfAlgebra.antipode ℚ (A := V.specialOrthogonalCoordinateRing) =
      V.specialOrthogonalCoordinateAntipode.toLinearMap := rfl

/-- The bundled Spin-candidate comultiplication is the explicit
coordinate comultiplication. -/
theorem cliffordSpinCandidateCoordinate_comulAlgHom :
    Bialgebra.comulAlgHom ℚ V.cliffordSpinCandidateCoordinateRing =
      V.cliffordSpinCandidateCoordinateComul := rfl

/-- The bundled Spin-candidate counit is the explicit coordinate
counit. -/
theorem cliffordSpinCandidateCoordinate_counitAlgHom :
    Bialgebra.counitAlgHom ℚ V.cliffordSpinCandidateCoordinateRing =
      V.cliffordSpinCandidateCoordinateCounit := rfl

/-- The bundled Spin-candidate antipode is the explicit inverse of
the universal algebra point. -/
theorem cliffordSpinCandidateCoordinate_antipode :
    HopfAlgebra.antipode ℚ (A := V.cliffordSpinCandidateCoordinateRing) =
      V.cliffordSpinCandidateCoordinateAntipode.toLinearMap := rfl

/-- The injective coordinate map of the Spin-candidate cover, bundled as a
homomorphism of bialgebras. -/
def specialOrthogonalToCliffordSpinCandidateCoordinateBialgHom :
    V.specialOrthogonalCoordinateRing →ₐc[ℚ]
      V.cliffordSpinCandidateCoordinateRing :=
  BialgHom.ofAlgHom
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
    V.cliffordSpinCandidateCoordinateCounit_comp
    V.cliffordSpinCandidateCoordinateComul_comp.symm

/-- The coordinate bialgebra homomorphism of the Spin-candidate cover is
injective. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateBialgHom_injective :
    Function.Injective
      V.specialOrthogonalToCliffordSpinCandidateCoordinateBialgHom :=
  V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_injective

end RationalQuadraticSpaceMatrix
