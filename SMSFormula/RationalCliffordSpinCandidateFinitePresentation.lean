import SMSFormula.RationalCliffordSpinCandidatePointGroup
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of the Clifford--Spin candidate cover

The affine morphism

```text
SpinCandidate_V ⟶ SO_V
```

is locally of finite presentation. Both coordinate rings are finite-type
quotients of finite-variable polynomial rings over `ℚ`. Since `ℚ` is
noetherian, the candidate algebra is finitely presented over `ℚ`; the
restriction-of-scalars theorem and finite type of the `SO` algebra then make
the relative coordinate map finitely presented.

For affine schemes, flatness together with surjectivity is equivalent to
faithful flatness of the contravariant coordinate-ring map.  The last theorem
therefore reduces the fppf property exactly to one algebraic
statement.  This file does not prove faithful flatness or pointwise
surjectivity.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The coordinate-ring map underlying the Clifford--Spin candidate morphism
is finitely presented. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finitePresentation :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_comp_finiteType
    (algebraMap ℚ V.specialOrthogonalCoordinateRing)
  · have hcomp :
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.comp
            (algebraMap ℚ V.specialOrthogonalCoordinateRing) =
          algebraMap ℚ V.cliffordSpinCandidateCoordinateRing := by
        ext q
        exact V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.commutes q
    rw [hcomp]
    exact RingHom.FinitePresentation.of_finiteType.mp (by
      rw [RingHom.finiteType_algebraMap]
      infer_instance)
  · rw [RingHom.finiteType_algebraMap]
    infer_instance

/-- The affine Clifford--Spin candidate morphism is locally of finite
presentation. -/
instance cliffordSpinCandidateToSpecialOrthogonalLocallyOfFinitePresentation :
    LocallyOfFinitePresentation
      V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finitePresentation

/-- The precise fppf property for the candidate morphism, with its three
standard components stated explicitly. -/
abbrev CliffordSpinCandidateToSpecialOrthogonalFppf : Prop :=
  (Surjective V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom ∧
      Flat V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom) ∧
    LocallyOfFinitePresentation
      V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom

/-- Since the morphism is locally of finite presentation, the fppf property is
equivalent to faithful flatness of the affine coordinate-ring map. -/
theorem cliffordSpinCandidateToSpecialOrthogonalFppf_iff_faithfullyFlat :
    V.CliffordSpinCandidateToSpecialOrthogonalFppf ↔
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat := by
  constructor
  · rintro ⟨⟨hsurj, hflat⟩, -⟩
    exact (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom)).mp
          ⟨hflat, hsurj⟩
  · intro h
    have hfs := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom)).mpr h
    exact ⟨⟨hfs.2, hfs.1⟩, inferInstance⟩

end RationalQuadraticSpaceMatrix
