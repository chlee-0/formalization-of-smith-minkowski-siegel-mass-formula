import SMSFormula.RationalCliffordSpinCandidateRankTwoFlatnessPrecursor
import SMSFormula.RationalCliffordSpinCandidateTorsorPoints

/-!
# The nontrivial `mu_2` involution on the Spin candidate

The nontrivial rational point of `mu_2` gives a scalar kernel point of the
Spin-candidate cover. Right multiplication by that point is reconstructed
contravariantly as an involutive automorphism of the candidate coordinate
ring. The automorphism fixes the special-orthogonal coordinate subalgebra
because the scalar point lies in the completed kernel.

This closes the involution part of the elementary rank-two flatness argument.
The remaining inputs are the finite canonical-map witness and descent of the
involution trace to the special-orthogonal coordinate ring.
-/

noncomputable section

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The nontrivial square root of one over a commutative ring. -/
def negOneRootOfUnity (A : Type*) [CommRing A] : rootsOfUnity 2 A :=
  ⟨-1, by
    apply Units.ext
    simp [pow_two]⟩

theorem negOneRootOfUnity_mul_self (A : Type*) [CommRing A] :
    negOneRootOfUnity A * negOneRootOfUnity A = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [negOneRootOfUnity]

theorem restrictRootsOfUnity_negOne
    (A B : Type*) [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    restrictRootsOfUnity f 2 (negOneRootOfUnity A) =
      negOneRootOfUnity B := by
  apply Subtype.ext
  apply Units.ext
  simp [negOneRootOfUnity]

/-- The scalar candidate point corresponding to the nontrivial element of
`mu_2`, evaluated in the candidate coordinate ring itself. -/
def cliffordSpinCandidateNegOneKernelPoint :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing :=
  (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
    V.cliffordSpinCandidateCoordinateRing
    (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)).1

/-- Right multiplication of the universal candidate point by the nontrivial
scalar kernel point, as a rational coordinate endomorphism. -/
def cliffordSpinCandidateNegOneCoordinateEnd :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing :=
  (V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing).mul
    (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
    V.cliffordSpinCandidateNegOneKernelPoint

theorem cliffordSpinCandidateNegOneKernelPoint_map_end :
    V.cliffordSpinCandidateCoordinateAlgHomMap
        V.cliffordSpinCandidateCoordinateRing
        V.cliffordSpinCandidateNegOneCoordinateEnd
        V.cliffordSpinCandidateNegOneKernelPoint =
      V.cliffordSpinCandidateNegOneKernelPoint := by
  simpa only [cliffordSpinCandidateNegOneKernelPoint,
    restrictRootsOfUnity_negOne] using
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint_naturality
      V.cliffordSpinCandidateNegOneCoordinateEnd
      (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing))

set_option maxHeartbeats 800000 in
/-- Right multiplication by the nontrivial scalar point is involutive. -/
theorem cliffordSpinCandidateNegOneCoordinateEnd_comp_self :
    V.cliffordSpinCandidateNegOneCoordinateEnd.comp
        V.cliffordSpinCandidateNegOneCoordinateEnd =
      AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing := by
  let B := V.cliffordSpinCandidateCoordinateRing
  letI : Group (B →ₐ[ℚ] B) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup B
  letI : Monoid (B →ₐ[ℚ] B) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup B).toMonoid
  let e : B →ₐ[ℚ] B := AlgHom.id ℚ B
  let k : B →ₐ[ℚ] B := V.cliffordSpinCandidateNegOneKernelPoint
  change V.cliffordSpinCandidateCoordinateAlgHomMap B
    V.cliffordSpinCandidateNegOneCoordinateEnd
    V.cliffordSpinCandidateNegOneCoordinateEnd = e
  rw [show V.cliffordSpinCandidateNegOneCoordinateEnd = e * k by rfl]
  rw [map_mul]
  change V.cliffordSpinCandidateNegOneCoordinateEnd.comp e *
      V.cliffordSpinCandidateNegOneCoordinateEnd.comp k = e
  rw [show V.cliffordSpinCandidateNegOneCoordinateEnd.comp e =
    V.cliffordSpinCandidateNegOneCoordinateEnd by rfl]
  have hk : V.cliffordSpinCandidateNegOneCoordinateEnd.comp k = k := by
    change V.cliffordSpinCandidateCoordinateAlgHomMap B
      V.cliffordSpinCandidateNegOneCoordinateEnd
      V.cliffordSpinCandidateNegOneKernelPoint =
        V.cliffordSpinCandidateNegOneKernelPoint
    exact V.cliffordSpinCandidateNegOneKernelPoint_map_end
  rw [hk]
  rw [show V.cliffordSpinCandidateNegOneCoordinateEnd = e * k by rfl]
  rw [mul_assoc]
  rw [show k * k = 1 by
    change ((V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
      B) (negOneRootOfUnity B) *
      (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
        B) (negOneRootOfUnity B)).1 = 1
    rw [← map_mul, negOneRootOfUnity_mul_self, map_one]
    rfl]
  simp [e]

set_option maxHeartbeats 800000 in
/-- The nontrivial scalar action fixes the special-orthogonal coordinate
subalgebra. -/
theorem cliffordSpinCandidateNegOneCoordinateEnd_comp_base :
    V.cliffordSpinCandidateNegOneCoordinateEnd.comp
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom =
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
  let B := V.cliffordSpinCandidateCoordinateRing
  letI : Group (B →ₐ[ℚ] B) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup B
  letI : Monoid (B →ₐ[ℚ] B) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup B).toMonoid
  let e : B →ₐ[ℚ] B := AlgHom.id ℚ B
  let k : B →ₐ[ℚ] B := V.cliffordSpinCandidateNegOneKernelPoint
  let F := V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom B
  change F V.cliffordSpinCandidateNegOneCoordinateEnd = _
  rw [show V.cliffordSpinCandidateNegOneCoordinateEnd = e * k by rfl]
  rw [map_mul]
  have hk : F k = 1 := by
    apply (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B).injective
    change V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B
        (k.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom) =
      V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B 1
    rw [V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp]
    rw [map_one]
    exact
      (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
        B (negOneRootOfUnity B)).2
  rw [hk, mul_one]
  rfl

/-- The nontrivial scalar action as an endomorphism over the `SO` coordinate
ring. -/
def cliffordSpinCandidateNegOneCoordinateAlgHom :
    V.cliffordSpinCandidateCoordinateRing →ₐ[
      V.specialOrthogonalCoordinateRing]
        V.cliffordSpinCandidateCoordinateRing where
  toFun := V.cliffordSpinCandidateNegOneCoordinateEnd
  map_one' := V.cliffordSpinCandidateNegOneCoordinateEnd.map_one
  map_mul' := V.cliffordSpinCandidateNegOneCoordinateEnd.map_mul
  map_zero' := V.cliffordSpinCandidateNegOneCoordinateEnd.map_zero
  map_add' := V.cliffordSpinCandidateNegOneCoordinateEnd.map_add
  commutes' a := by
    change V.cliffordSpinCandidateNegOneCoordinateEnd
        (V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a) =
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a
    exact DFunLike.congr_fun
      V.cliffordSpinCandidateNegOneCoordinateEnd_comp_base a

theorem cliffordSpinCandidateNegOneCoordinateAlgHom_comp_self :
    V.cliffordSpinCandidateNegOneCoordinateAlgHom.comp
        V.cliffordSpinCandidateNegOneCoordinateAlgHom =
      AlgHom.id V.specialOrthogonalCoordinateRing
        V.cliffordSpinCandidateCoordinateRing := by
  ext b
  exact DFunLike.congr_fun
    V.cliffordSpinCandidateNegOneCoordinateEnd_comp_self b

/-- The actual `O(SO)`-algebra involution supplied by the nontrivial scalar
kernel point. -/
def cliffordSpinCandidateNegOneCoordinateAlgEquiv :
    V.cliffordSpinCandidateCoordinateRing ≃ₐ[
      V.specialOrthogonalCoordinateRing]
        V.cliffordSpinCandidateCoordinateRing :=
  AlgEquiv.ofAlgHom V.cliffordSpinCandidateNegOneCoordinateAlgHom
    V.cliffordSpinCandidateNegOneCoordinateAlgHom
    V.cliffordSpinCandidateNegOneCoordinateAlgHom_comp_self
    V.cliffordSpinCandidateNegOneCoordinateAlgHom_comp_self

/-- The remaining effective-quotient data after fixing the canonical
nontrivial `mu_2` involution. -/
structure CliffordSpinCandidateRankTwoEffectiveQuotientData where
  size : ℕ
  trace : V.cliffordSpinCandidateCoordinateRing →ₗ[
    V.specialOrthogonalCoordinateRing] V.specialOrthogonalCoordinateRing
  trace_spec : ∀ b, algebraMap V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing (trace b) =
      b + V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b
  left : Fin size → V.cliffordSpinCandidateCoordinateRing
  right : Fin size → V.cliffordSpinCandidateCoordinateRing
  canonical_one : ∑ i, left i * right i = 1
  canonical_zero : ∑ i,
    left i * V.cliffordSpinCandidateNegOneCoordinateAlgEquiv (right i) = 0

/-- The narrowed effective-quotient data assemble the earlier rank-two
flatness record. -/
def CliffordSpinCandidateRankTwoEffectiveQuotientData.toFlatnessData
    (D : V.CliffordSpinCandidateRankTwoEffectiveQuotientData) :
    V.CliffordSpinCandidateRankTwoFlatnessData where
  size := D.size
  sigma := V.cliffordSpinCandidateNegOneCoordinateAlgEquiv
  trace := D.trace
  trace_spec := D.trace_spec
  left := D.left
  right := D.right
  canonical_one := D.canonical_one
  canonical_zero := D.canonical_zero

/-- The explicit nontrivial action reduces faithful flatness to the finite
canonical witness and trace descent. -/
theorem faithfullyFlat_of_rankTwoEffectiveQuotientData
    (D : V.CliffordSpinCandidateRankTwoEffectiveQuotientData) :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat :=
  V.faithfullyFlat_of_rankTwoFlatnessData D.toFlatnessData

end RationalQuadraticSpaceMatrix
