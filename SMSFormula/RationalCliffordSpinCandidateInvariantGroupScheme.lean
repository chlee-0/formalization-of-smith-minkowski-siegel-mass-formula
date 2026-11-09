import SMSFormula.HopfAlgebraAffinePointGroup
import SMSFormula.RationalCliffordSpinCandidateInvariantHopf
import SMSFormula.RationalCliffordSpinCandidateInvariantQuotient
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# The Spin invariant quotient as a group scheme

The fixed ring `C = O(SpinCandidate)^sigma` already carries a
commutative Hopf algebra.  This file equips every algebra-point set
`Hom_Q(C,D)` with its convolution group, proves naturality, and uses affine
representability to install a group object on `Spec C` over `Spec Q`.

The injective coordinate bialgebra map `O(SO) -> C` is then transported to a
group-scheme homomorphism whose underlying scheme morphism is the
invariant-quotient comparison.  It does not prove that the comparison is an isomorphism or
that `O(SO) -> C` is surjective.
-/

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidalCategory
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

theorem negOneInvariantQuotientStructureRingHom_eq_algebraMap :
    V.negOneInvariantQuotientStructureRingHom =
      algebraMap ℚ V.negOneInvariantSubalgebra := by
  ext q
  rfl

def negOneInvariantAffinePointGroupData :
    AffinePointGroupData ℚ V.negOneInvariantSubalgebra :=
  HopfAlgebra.affinePointGroupData V.negOneInvariantAntipode
    V.negOneInvariant_antipode.symm

noncomputable instance negOneInvariantCoordinateAlgHomGroup
    (D : Type) [CommRing D] [Algebra ℚ D] :
    Group (V.negOneInvariantSubalgebra →ₐ[ℚ] D) :=
  V.negOneInvariantAffinePointGroupData.pointGroup D

set_option diagnostics true in
def negOneInvariantCoordinateAlgHomToSpecialOrthogonal
    (D : Type) [CommRing D] [Algebra ℚ D] :
    (V.negOneInvariantSubalgebra →ₐ[ℚ] D) →*
      (V.specialOrthogonalCoordinateRing →ₐ[ℚ] D) where
  toFun f := f.comp V.specialOrthogonalToNegOneInvariantRatAlgHom
  map_one' := by
    change ((AffinePointGroupData.unitAlgHom (R := ℚ) (A := D)).comp
        V.negOneInvariantCounit).comp
          V.specialOrthogonalToNegOneInvariantRatAlgHom = 1
    rw [AlgHom.comp_assoc]
    have hcounit := BialgHomClass.counitAlgHom_comp
      V.specialOrthogonalToNegOneInvariantBialgHom
    change V.negOneInvariantCounit.comp
        V.specialOrthogonalToNegOneInvariantRatAlgHom =
      V.specialOrthogonalCoordinateCounit at hcounit
    rw [hcounit]
    change (AffinePointGroupData.unitAlgHom (R := ℚ) (A := D)).comp
      V.specialOrthogonalAffinePointGroupData.counit = 1
    rw [← V.specialOrthogonalAffinePointGroupData.map_apply]
    exact map_one
      (V.specialOrthogonalAffinePointGroupData.map
        (AffinePointGroupData.unitAlgHom (R := ℚ) (A := D)))
  map_mul' f g := by
    change (HopfAlgebra.algHomConvolution (R := ℚ)
        (A := V.negOneInvariantSubalgebra) (D := D) f g).comp
          V.specialOrthogonalToNegOneInvariantRatAlgHom =
      (f.comp V.specialOrthogonalToNegOneInvariantRatAlgHom) *
        (g.comp V.specialOrthogonalToNegOneInvariantRatAlgHom)
    have hprecomp :=
      HopfAlgebra.algHomPrecompBialgHom_convolution (R := ℚ)
        (A := V.specialOrthogonalCoordinateRing)
        (E := V.negOneInvariantSubalgebra) (D := D)
        V.specialOrthogonalToNegOneInvariantBialgHom f g
    change
        (HopfAlgebra.algHomConvolution (R := ℚ)
          (A := V.negOneInvariantSubalgebra) (D := D) f g).comp
            V.specialOrthogonalToNegOneInvariantRatAlgHom =
        HopfAlgebra.algHomConvolution (R := ℚ)
          (A := V.specialOrthogonalCoordinateRing) (D := D)
          (f.comp V.specialOrthogonalToNegOneInvariantRatAlgHom)
          (g.comp V.specialOrthogonalToNegOneInvariantRatAlgHom) at hprecomp
    exact hprecomp.trans
      (AffinePointGroupData.algHomConvolution_eq_mul (R := ℚ)
        (A := V.specialOrthogonalCoordinateRing) (D := D)
        V.specialOrthogonalAffinePointGroupData
        (f.comp V.specialOrthogonalToNegOneInvariantRatAlgHom)
        (g.comp V.specialOrthogonalToNegOneInvariantRatAlgHom))

end RationalQuadraticSpaceMatrix
