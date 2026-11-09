import SMSFormula.RationalCliffordSpinCandidateCanonicalMapIso
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import SMSFormula.RationalCliffordSpinCandidateFppf
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalCliffordSpinCandidateSurjectivity
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The Spin-candidate map is a finite etale central `mu_2` cover

This file proves the scheme-level finite and etale properties of the
represented Clifford--Spin candidate map.  Together with scheme
surjectivity, its unit-fiber identification with `mu_2`, and
the functorial pointwise centrality of the kernel inclusion, these give the
central-cover data.

Scheme surjectivity does not assert surjectivity on rational, real, or p-adic
points.  The results here do not prove that the source is connected, identify
it with the standard classical Spin group, define an algebraic-group isogeny,
establish condition (K), compare Tamagawa volumes, or evaluate the Spin
quotient volume.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance finiteCoverInvariantCommRing : CommRing V.negOneInvariantSubalgebra :=
  V.negOneInvariantSubalgebra.toCommRing

local instance finiteCoverInvariantCommSemiring : CommSemiring V.negOneInvariantSubalgebra :=
  (finiteCoverInvariantCommRing V).toCommSemiring

set_option backward.isDefEq.respectTransparency false in
/-- The actual coordinate-ring homomorphism of the Spin cover is finite.
This is the composite of the completed `SO`--invariant equivalence and the
rank-two finite invariant extension. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finite :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.Finite := by
  change V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.Finite
  have inclusionFinite : V.negOneInvariantInclusionAlgHom.Finite := by
    change (algebraMap V.negOneInvariantSubalgebra
      V.cliffordSpinCandidateCoordinateRing).Finite
    exact V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_finite
  have comparisonFinite : V.specialOrthogonalToNegOneInvariantRatAlgHom.Finite :=
    AlgHom.Finite.of_surjective _
      V.specialOrthogonalToNegOneInvariantAlgHom_bijective.surjective
  have compositeFinite := AlgHom.Finite.comp inclusionFinite comparisonFinite
  rw [V.negOneInvariantInclusion_comp_specialOrthogonal] at compositeFinite
  exact compositeFinite

/-- The affine Clifford--Spin candidate map is finite as a scheme morphism. -/
instance cliffordSpinCandidateToSpecialOrthogonalFinite :
    IsFinite V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom))
  rw [IsFinite.SpecMap_iff]
  exact V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finite

end RationalQuadraticSpaceMatrix
