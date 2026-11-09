import SMSFormula.RationalCliffordSpinCandidateSurjectivity
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Reduced-target injectivity for the affine Spin cover

For a homomorphism of commutative rings, surjectivity of the induced map on
prime spectra forces the kernel into the nilradical.  A reduced source ring
therefore makes the homomorphism injective.

Applied to the Clifford--Spin candidate cover, this reduces
injectivity of its coordinate-ring homomorphism exactly to reducedness of the
special-orthogonal coordinate ring.  The implication from an
injective morphism of commutative Hopf algebras over a field to faithful
flatness is the Takeuchi--Waterhouse theorem; it is not asserted
in this file.
-/

noncomputable section

open AlgebraicGeometry

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective map on prime spectra has injective coordinate homomorphism
when the target coordinate ring is reduced. -/
theorem injective_of_comap_surjective_of_isReduced [IsReduced R]
    (f : R →+* S)
    (h : Function.Surjective (PrimeSpectrum.comap f)) :
    Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · have hker : RingHom.ker f ≤ nilradical R :=
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mp
        h.denseRange
    simpa [(nilradical_eq_bot_iff.mpr (inferInstance : IsReduced R))] using hker
  · exact bot_le

end RingHom

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Once the explicit special-orthogonal coordinate ring is known reduced,
scheme surjectivity of the Clifford--Spin candidate cover makes its affine
coordinate homomorphism injective. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_injective_of_isReduced
    [IsReduced V.specialOrthogonalCoordinateRing] :
    Function.Injective
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom :=
  RingHom.injective_of_comap_surjective_of_isReduced _
    V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_comap_surjective

end RationalQuadraticSpaceMatrix
