import SMSFormula.RationalCliffordSpinCandidateInvariantFlatness
import SMSFormula.RationalCliffordSpinCandidateFinitePresentation
import SMSFormula.RationalCliffordSpinCandidateSurjectivity
import SMSFormula.RationalCliffordSpinCandidateTorsorPoints
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Adjoin.Tower

/-!
# The fixed-subalgebra quotient of the Clifford--Spin candidate

Let `B` be the Clifford--Spin candidate coordinate ring and let
`C = B^sigma` be the literal fixed subalgebra of the nontrivial central
`mu_2` action.  This file bundles `Spec C` and factors the candidate cover as

```text
Spec B -> Spec C -> SO.
```

The first arrow is finite fppf by the completed explicit dual-basis theorem.
The second arrow is affine, separated, scheme-surjective, locally finitely
presented, and locally quasi-finite.  Its finite-type statement uses
Artin--Tate: `B` is finite type over `O(SO)` and finite over `C`.

These properties do not identify `C` with the implemented `SO` coordinate
ring.  In particular, no surjectivity of
`specialOrthogonalToNegOneInvariantAlgHom` and no flatness of the original
candidate cover is inferred here.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- Finite fibers descend through a surjective precomposition. -/
lemma Scheme.Hom.finite_preimage_singleton_of_surjective_precomp
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] (z : Z)
    (hfinite : ((f ≫ g) ⁻¹' {z}).Finite) :
    (g ⁻¹' {z}).Finite := by
  refine (hfinite.image f).subset ?_
  intro y hy
  obtain ⟨x, hx⟩ := f.surjective y
  refine ⟨x, ?_, hx⟩
  have : g (f x) = z := by
    rw [hx]
    simpa using hy
  simpa using this

/-- A locally finite-type morphism is locally quasi-finite when it becomes
locally quasi-finite and quasi-compact after a surjective precomposition. -/
lemma LocallyQuasiFinite.of_surjective_precomp
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite (f ≫ g)]
    [QuasiCompact (f ≫ g)] : LocallyQuasiFinite g := by
  exact .of_finite_preimage_singleton g (fun z =>
    f.finite_preimage_singleton_of_surjective_precomp g z
      ((f ≫ g).finite_preimage_singleton z))

end AlgebraicGeometry

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The affine scheme represented by the fixed subalgebra of the nontrivial
central `mu_2` action. -/
abbrev negOneInvariantQuotientAffineScheme : Scheme :=
  Spec (CommRingCat.of V.negOneInvariantSubalgebra)

/-- The rational structure map on the fixed subalgebra, written explicitly
through `O(SO)` because the fixed subalgebra is natively bundled as an
`O(SO)`-subalgebra of the candidate coordinate ring. -/
def negOneInvariantQuotientStructureRingHom :
    ℚ →+* V.negOneInvariantSubalgebra :=
  V.specialOrthogonalToNegOneInvariantAlgHom.toRingHom.comp
    (algebraMap ℚ V.specialOrthogonalCoordinateRing)

/-- The finite fppf map from the candidate to its literal invariant
quotient. -/
def cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom :
    V.cliffordSpinCandidateAffineScheme ⟶
      V.negOneInvariantQuotientAffineScheme :=
  Spec.map (CommRingCat.ofHom
    (R := V.negOneInvariantSubalgebra) (S := V.cliffordSpinCandidateCoordinateRing)
    (algebraMap V.negOneInvariantSubalgebra
      V.cliffordSpinCandidateCoordinateRing))

/-- The comparison from the literal invariant quotient to the implemented
special-orthogonal carrier. -/
def negOneInvariantQuotientToSpecialOrthogonalSchemeHom :
    V.negOneInvariantQuotientAffineScheme ⟶
      V.specialOrthogonalAffineScheme :=
  Spec.map (CommRingCat.ofHom
    (R := V.specialOrthogonalCoordinateRing) (S := V.negOneInvariantSubalgebra)
    V.specialOrthogonalToNegOneInvariantAlgHom.toRingHom)

/-- The original candidate cover factors through the literal fixed-subalgebra
quotient. -/
theorem cliffordSpinCandidateToNegOneInvariantQuotient_comp_comparison :
    V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom ≫
        V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom =
      V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom := by
  unfold cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom
    negOneInvariantQuotientToSpecialOrthogonalSchemeHom
    cliffordSpinCandidateToSpecialOrthogonalSchemeHom
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply DFunLike.ext _ _
  intro a
  rfl

instance cliffordSpinCandidateToNegOneInvariantQuotientFlat :
    Flat V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom := by
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (R := V.negOneInvariantSubalgebra)
      (S := V.cliffordSpinCandidateCoordinateRing) (algebraMap V.negOneInvariantSubalgebra
      V.cliffordSpinCandidateCoordinateRing))).mpr
        V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_faithfullyFlat).1

instance cliffordSpinCandidateToNegOneInvariantQuotientSurjective :
    Surjective
      V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom := by
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (R := V.negOneInvariantSubalgebra)
      (S := V.cliffordSpinCandidateCoordinateRing) (algebraMap V.negOneInvariantSubalgebra
      V.cliffordSpinCandidateCoordinateRing))).mpr
        V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_faithfullyFlat).2

instance cliffordSpinCandidateToNegOneInvariantQuotientFinite :
    IsFinite V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    (R := V.negOneInvariantSubalgebra) (S := V.cliffordSpinCandidateCoordinateRing)
    (algebraMap V.negOneInvariantSubalgebra
      V.cliffordSpinCandidateCoordinateRing)))
  rw [IsFinite.SpecMap_iff]
  exact V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_finite

/-- Artin--Tate finite generation for the invariant ring over `O(SO)`. -/
theorem negOneInvariantSubalgebra_finiteType : Algebra.FiniteType
    V.specialOrthogonalCoordinateRing V.negOneInvariantSubalgebra := by
  have hspin : Algebra.FiniteType V.specialOrthogonalCoordinateRing
      V.cliffordSpinCandidateCoordinateRing := by
    rw [← RingHom.finiteType_algebraMap]
    change V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FiniteType
    exact RingHom.FiniteType.of_finitePresentation
      V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finitePresentation
  rw [← Subalgebra.fg_iff_finiteType]
  exact V.negOneInvariantSubalgebra.fg_top.mp
    (fg_of_fg_of_fg V.specialOrthogonalCoordinateRing
      V.negOneInvariantSubalgebra V.cliffordSpinCandidateCoordinateRing
      hspin.out
      V.cliffordSpinCandidateModuleFiniteOverNegOneInvariant.1
      V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_injective)

/-- The finite invariant quotient map is finitely presented. -/
theorem negOneInvariantToCliffordSpinCandidateCoordinateRingHom_finitePresentation :
    RingHom.FinitePresentation (A := V.negOneInvariantSubalgebra)
      (B := V.cliffordSpinCandidateCoordinateRing)
      (algebraMap V.negOneInvariantSubalgebra V.cliffordSpinCandidateCoordinateRing) := by
  apply RingHom.FinitePresentation.of_comp_finiteType
    (algebraMap V.specialOrthogonalCoordinateRing V.negOneInvariantSubalgebra)
  · have hcomp : (algebraMap V.negOneInvariantSubalgebra
        V.cliffordSpinCandidateCoordinateRing).comp
          (algebraMap V.specialOrthogonalCoordinateRing
            V.negOneInvariantSubalgebra) =
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom := by
      apply DFunLike.ext _ _
      intro a
      rfl
    rw [hcomp]
    exact V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finitePresentation
  · rw [RingHom.finiteType_algebraMap]
    exact V.negOneInvariantSubalgebra_finiteType

instance cliffordSpinCandidateToNegOneInvariantQuotientLocallyOfFinitePresentation :
    LocallyOfFinitePresentation
      V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
    (R := V.negOneInvariantSubalgebra) (S := V.cliffordSpinCandidateCoordinateRing)
    (algebraMap V.negOneInvariantSubalgebra
      V.cliffordSpinCandidateCoordinateRing)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_finitePresentation

/-- The candidate is a finite fppf cover of its literal invariant quotient. -/
theorem cliffordSpinCandidateToNegOneInvariantQuotient_finite_fppf :
    (Surjective V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom ∧
      Flat V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom) ∧
      LocallyOfFinitePresentation
        V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom ∧
      IsFinite V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom := by
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

instance negOneInvariantQuotientToSpecialOrthogonalSurjective :
    Surjective V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom := by
  haveI : Surjective
      (V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom ≫
        V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom) := by
    rw [V.cliffordSpinCandidateToNegOneInvariantQuotient_comp_comparison]
    infer_instance
  exact Surjective.of_comp
    V.cliffordSpinCandidateToNegOneInvariantQuotientSchemeHom
    V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom

/-- The invariant quotient comparison is finitely presented over `O(SO)`. -/
theorem specialOrthogonalToNegOneInvariantCoordinateRingHom_finitePresentation :
    RingHom.FinitePresentation (A := V.specialOrthogonalCoordinateRing)
      (B := V.negOneInvariantSubalgebra)
      V.specialOrthogonalToNegOneInvariantAlgHom.toRingHom := by
  exact (RingHom.FinitePresentation.of_finiteType
    (A := V.specialOrthogonalCoordinateRing) (B := V.negOneInvariantSubalgebra)).mp (by
    change RingHom.FiniteType (A := V.specialOrthogonalCoordinateRing)
      (B := V.negOneInvariantSubalgebra)
      (algebraMap V.specialOrthogonalCoordinateRing V.negOneInvariantSubalgebra)
    rw [RingHom.finiteType_algebraMap]
    exact V.negOneInvariantSubalgebra_finiteType)

instance negOneInvariantQuotientToSpecialOrthogonalLocallyOfFinitePresentation :
    LocallyOfFinitePresentation
      V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
    (R := V.specialOrthogonalCoordinateRing) (S := V.negOneInvariantSubalgebra)
    V.specialOrthogonalToNegOneInvariantAlgHom.toRingHom))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact V.specialOrthogonalToNegOneInvariantCoordinateRingHom_finitePresentation

instance negOneInvariantQuotientToSpecialOrthogonalQuasiCompact :
    QuasiCompact V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom := by
  infer_instance

instance negOneInvariantQuotientToSpecialOrthogonalIsAffineHom :
    IsAffineHom V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom := by
  infer_instance

instance negOneInvariantQuotientToSpecialOrthogonalIsSeparated :
    IsSeparated V.negOneInvariantQuotientToSpecialOrthogonalSchemeHom := by
  infer_instance

end RationalQuadraticSpaceMatrix
