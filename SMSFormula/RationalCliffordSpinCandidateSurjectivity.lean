import SMSFormula.RationalCliffordIteratedReflectionPairLift
import SMSFormula.RationalCliffordSpinCandidateFinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Surjectivity of the affine Clifford--Spin candidate cover

The completed iterated reflection-pair lift over characteristic-zero fields
is applied to the residue field of every prime of the special-orthogonal
coordinate ring.  The terminal quadratic-root tower is faithfully flat over
that field, so it has a prime above the zero prime.  Pulling this prime back
through the terminal Spin-candidate point produces a prime of the candidate
coordinate ring above the original special-orthogonal prime.

Consequently the affine morphism

```text
SpinCandidate_V -> SO_V
```

is surjective on underlying topological spaces.  This is scheme
surjectivity, not surjectivity on rational or local field points.  Flatness
of the global coordinate-ring map is not proved here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- A special-orthogonal matrix over a rational field acts as a quadratic
isometry of the quadratic form represented by the mapped form matrix. -/
def specialOrthogonalMatrixGroupIsometryEquiv
    (K : Type*) [Field K] [Algebra ℚ K]
    (g : V.specialOrthogonalMatrixGroup K) :
    (V.commutativeScalarExtensionQuadraticForm K).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm K) := by
  letI : Invertible (2 : K) := rationalAlgebraInvertibleTwo K
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))
      (Matrix.GeneralLinearGroup.toLin g.1.1)
  have he : LinearMap.toMatrix' e.toLinearMap = g.1.1.1 := by
    change LinearMap.toMatrix' (Matrix.toLin' g.1.1.1) = g.1.1.1
    exact LinearMap.toMatrix'_toLin' _
  have hmatrix :
      QuadraticForm.toMatrix'
        ((V.commutativeScalarExtensionQuadraticForm K).comp e.toLinearMap) =
      QuadraticForm.toMatrix' (V.commutativeScalarExtensionQuadraticForm K) := by
    rw [QuadraticForm.toMatrix'_comp, he,
      V.commutativeScalarExtensionQuadraticForm_toMatrix' K]
    have hg := (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix K) g.1.1).1 g.1.2
    simpa [commutativeScalarExtensionFormMatrix,
      specialOrthogonalMappedFormMatrix] using hg
  have hassoc :
      ((V.commutativeScalarExtensionQuadraticForm K).comp
        e.toLinearMap).associated =
      (V.commutativeScalarExtensionQuadraticForm K).associated := by
    exact (LinearMap.toMatrix₂' K).injective hmatrix
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  calc
    V.commutativeScalarExtensionQuadraticForm K (e x) =
        ((V.commutativeScalarExtensionQuadraticForm K).comp
          e.toLinearMap) x := rfl
    _ = ((V.commutativeScalarExtensionQuadraticForm K).comp
          e.toLinearMap).associated x x :=
        (((V.commutativeScalarExtensionQuadraticForm K).comp
          e.toLinearMap).associated_eq_self_apply ℕ x).symm
    _ = (V.commutativeScalarExtensionQuadraticForm K).associated x x :=
        congrArg (fun B => B x x) hassoc
    _ = V.commutativeScalarExtensionQuadraticForm K x :=
        (V.commutativeScalarExtensionQuadraticForm K).associated_eq_self_apply ℕ x

@[simp]
theorem specialOrthogonalMatrixGroupIsometryEquiv_toMatrix'
    (K : Type*) [Field K] [Algebra ℚ K]
    (g : V.specialOrthogonalMatrixGroup K) :
    LinearMap.toMatrix'
        (V.specialOrthogonalMatrixGroupIsometryEquiv K g).toLinearEquiv.toLinearMap =
      g.1.1.1 := by
  letI : Invertible (2 : K) := rationalAlgebraInvertibleTwo K
  simp only [specialOrthogonalMatrixGroupIsometryEquiv]
  change LinearMap.toMatrix' (Matrix.toLin' g.1.1.1) = g.1.1.1
  exact LinearMap.toMatrix'_toLin' _

set_option maxHeartbeats 800000 in
/-- Every special-orthogonal coordinate point over a characteristic-zero
field lifts after a finite faithfully-flat quadratic-root tower.  The final
equality is an equality of complete coordinate algebra maps, not only of
their matrix entries. -/
theorem exists_fppfLift_of_specialOrthogonalCoordinatePoint
    (K : Type*) [Field K] [CharZero K]
    (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) :
    ∃ ps : List (V.ReflectionPair K),
      ∃ lift : V.ReflectionPairFppfLift K ps,
        lift.point.comp
            V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom =
          lift.base.comp F := by
  let M : V.specialOrthogonalMatrixPoint K :=
    V.specialOrthogonalCoordinateAlgHomEquivMatrixPoint K F
  let G : V.specialOrthogonalMatrixGroup K :=
    V.specialOrthogonalMatrixPointToGroup K M
  let g := V.specialOrthogonalMatrixGroupIsometryEquiv K G
  have hQ :
      (V.commutativeScalarExtensionQuadraticForm K).associated.Nondegenerate := by
    simpa [commutativeScalarExtensionQuadraticForm,
      commutativeScalarExtensionFormMatrix,
      scalarExtensionQuadraticForm, scalarExtensionFormMatrix] using
      V.scalarExtensionQuadraticForm_associated_nondegenerate K
  have hdet : LinearMap.det g.toLinearEquiv.toLinearMap = 1 := by
    rw [← LinearMap.det_toMatrix',
      V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix']
    exact (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix K) G.1).1 G.2
  obtain ⟨ps, lift, -, hlift⟩ :=
    ReflectionPairFppfLift.exists_fppfLift_of_isometry_det_one
      (V := V) hQ g hdet
  refine ⟨ps, lift, ?_⟩
  apply (V.specialOrthogonalCoordinateAlgHomEquivMatrixPoint lift.Carrier).injective
  apply Subtype.ext
  ext i j
  change lift.point
      (V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
        (V.specialOrthogonalCoordinate i j)) =
    lift.base (F (V.specialOrthogonalCoordinate i j))
  rw [V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom_coordinate,
    hlift]
  rw [V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix']
  change lift.base (M.1 i j) = lift.base (F (V.specialOrthogonalCoordinate i j))
  rfl

set_option maxHeartbeats 800000 in
/-- The map on prime spectra induced by the affine candidate coordinate map
is surjective. -/
theorem specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom) := by
  intro p
  let P : Ideal V.specialOrthogonalCoordinateRing := p.asIdeal
  let K := P.ResidueField
  letI : Field K := inferInstance
  have hchar : CharZero K := by
    letI : Algebra ℚ K := inferInstance
    exact algebraRat.charZero K
  letI : CharZero K := hchar
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  let F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K :=
    { toRingHom := algebraMap V.specialOrthogonalCoordinateRing K
      commutes' := by
        intro q
        simp }
  obtain ⟨_, lift, hcomp⟩ :=
    V.exists_fppfLift_of_specialOrthogonalCoordinatePoint K F
  have hbaseSurj : Function.Surjective
      (PrimeSpectrum.comap lift.base.toRingHom) :=
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
      lift.faithfullyFlat).2
  let z : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  obtain ⟨q, hq⟩ := hbaseSurj z
  refine ⟨PrimeSpectrum.comap lift.point.toRingHom q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have hring :
      lift.point.toRingHom.comp
          V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom =
        lift.base.toRingHom.comp F.toRingHom := by
    exact congrArg AlgHom.toRingHom hcomp
  rw [hring, PrimeSpectrum.comap_comp_apply, hq]
  apply PrimeSpectrum.ext
  change RingHom.ker F.toRingHom = p.asIdeal
  change RingHom.ker (algebraMap V.specialOrthogonalCoordinateRing K) = P
  exact Ideal.ker_algebraMap_residueField P

/-- The affine Clifford--Spin candidate morphism is surjective as a morphism
of schemes.  This instance concerns underlying topological spaces. -/
instance cliffordSpinCandidateToSpecialOrthogonalSurjective :
    Surjective V.cliffordSpinCandidateToSpecialOrthogonalSchemeHom := by
  rw [surjective_iff]
  exact V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_comap_surjective

end RationalQuadraticSpaceMatrix
