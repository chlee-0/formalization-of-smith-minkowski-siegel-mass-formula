import SMSFormula.QuadraticCartanDieudonneParity
import SMSFormula.RationalCliffordReflectionPairArbitraryBase
import SMSFormula.RationalCliffordSpinCandidateKernelFiber

/-!
# Iterated fppf lifts of quadratic reflection pairs

This file iterates the quadratic square-root normalization for a finite list
of certified reflection pairs over a characteristic-zero field.  The tower is
constructed from the tail toward the head, matching the convention that a
reflection word acts from left to right while its matrices multiply in the
opposite recursive order.
-/

noncomputable section

open CliffordAlgebra
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The special-orthogonal matrix of a pair of anisotropic vectors before
adjoining its normalizing square root. -/
def commutativeReflectionPairSpecialOrthogonalMatrixPoint
    (v w : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)] :
    V.specialOrthogonalMatrixPoint A := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let Q := V.commutativeScalarExtensionQuadraticForm A
  let e := CliffordAlgebra.quadraticReflectionPair Q v w
  refine ⟨LinearMap.toMatrix' e.toLinearMap, ?_, ?_⟩
  · have hcomp : Q.comp e.toLinearMap = Q := by
      apply QuadraticMap.ext
      intro m
      exact CliffordAlgebra.quadraticReflectionPair_map_app Q v w m
    have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
    rw [QuadraticForm.toMatrix'_comp,
      V.commutativeScalarExtensionQuadraticForm_toMatrix'] at hmatrix
    simpa [e, Q, specialOrthogonalMappedFormMatrix,
      commutativeScalarExtensionFormMatrix] using hmatrix
  · exact CliffordAlgebra.quadraticReflectionPair_toMatrix'_det Q v w

def commutativeReflectionPairSpecialOrthogonalMatrixGroup
    (v w : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)] :
    V.specialOrthogonalMatrixGroup A :=
  V.specialOrthogonalMatrixPointToGroup A
    (V.commutativeReflectionPairSpecialOrthogonalMatrixPoint A v w)

@[simp]
theorem commutativeReflectionPairSpecialOrthogonalMatrixGroup_apply_matrix
    (v w : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)] :
    (V.commutativeReflectionPairSpecialOrthogonalMatrixGroup A v w).1.1.1 =
      LinearMap.toMatrix'
        (CliffordAlgebra.quadraticReflectionPair
          (V.commutativeScalarExtensionQuadraticForm A) v w).toLinearMap := by
  ext i j
  simp [commutativeReflectionPairSpecialOrthogonalMatrixGroup,
    commutativeReflectionPairSpecialOrthogonalMatrixPoint,
    specialOrthogonalMatrixPointToGroup]

theorem commutativeQuadraticReflection_map
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x m : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A x)]
    [Invertible
      (V.commutativeScalarExtensionQuadraticForm B (fun i => f (x i)))] :
    CliffordAlgebra.quadraticReflection
        (V.commutativeScalarExtensionQuadraticForm B)
        (fun i => f (x i)) (fun i => f (m i)) =
      fun i => f (CliffordAlgebra.quadraticReflection
        (V.commutativeScalarExtensionQuadraticForm A) x m i) := by
  have hQ (z : Fin n → A) :
      V.commutativeScalarExtensionQuadraticForm B (fun i => f (z i)) =
        f (V.commutativeScalarExtensionQuadraticForm A z) :=
    V.commutativeScalarExtensionQuadraticForm_map A f z
  have hpolar :
      QuadraticMap.polar (V.commutativeScalarExtensionQuadraticForm B)
          (fun i => f (x i)) (fun i => f (m i)) =
        f (QuadraticMap.polar
          (V.commutativeScalarExtensionQuadraticForm A) x m) := by
    simp only [QuadraticMap.polar]
    rw [show (fun i => f (x i)) + (fun i => f (m i)) =
        fun i => f ((x + m) i) by
      ext i
      simp]
    rw [hQ, hQ, hQ, map_sub, map_sub]
  have hinv :
      ⅟(V.commutativeScalarExtensionQuadraticForm B (fun i => f (x i))) =
        f (⅟(V.commutativeScalarExtensionQuadraticForm A x)) := by
    apply invOf_eq_right_inv
    rw [hQ, ← map_mul, mul_invOf_self, map_one]
  rw [CliffordAlgebra.quadraticReflection_apply,
    CliffordAlgebra.quadraticReflection_apply]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpolar, hinv, map_sub, map_mul, map_mul]

theorem commutativeReflectionPairSpecialOrthogonalMatrixGroup_map
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (v w : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)]
    [Invertible
      (V.commutativeScalarExtensionQuadraticForm B (fun i => f (v i)))]
    [Invertible
      (V.commutativeScalarExtensionQuadraticForm B (fun i => f (w i)))] :
    V.specialOrthogonalMatrixGroupMap f
        (V.commutativeReflectionPairSpecialOrthogonalMatrixGroup A v w) =
      V.commutativeReflectionPairSpecialOrthogonalMatrixGroup B
        (fun i => f (v i)) (fun i => f (w i)) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [V.specialOrthogonalMatrixGroupMap_apply_matrix]
  rw [V.commutativeReflectionPairSpecialOrthogonalMatrixGroup_apply_matrix]
  rw [V.commutativeReflectionPairSpecialOrthogonalMatrixGroup_apply_matrix]
  simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
  change f ((CliffordAlgebra.quadraticReflectionPair
      (V.commutativeScalarExtensionQuadraticForm A) v w
      (Pi.single j 1)) i) = _
  simp only [CliffordAlgebra.quadraticReflectionPair_apply]
  rw [show (Pi.single j (1 : B) : Fin n → B) =
      fun i => f ((Pi.single j (1 : A) : Fin n → A) i) by
    ext k
    simp [Pi.single_apply]]
  change f ((CliffordAlgebra.quadraticReflection
      (V.commutativeScalarExtensionQuadraticForm A) v
      (CliffordAlgebra.quadraticReflection
        (V.commutativeScalarExtensionQuadraticForm A) w
        (Pi.single j 1))) i) =
    (CliffordAlgebra.quadraticReflection
      (V.commutativeScalarExtensionQuadraticForm B) (fun i => f (v i))
      (CliffordAlgebra.quadraticReflection
        (V.commutativeScalarExtensionQuadraticForm B) (fun i => f (w i))
        (fun i => f ((Pi.single j (1 : A) : Fin n → A) i)))) i
  rw [V.commutativeQuadraticReflection_map A f w]
  rw [V.commutativeQuadraticReflection_map A f v]

theorem commutativeReflectionPairRoot_quadraticReflection_map
    (v w x m : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A x)]
    [Invertible
      (V.commutativeScalarExtensionQuadraticForm
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootVector A v w x))] :
    CliffordAlgebra.quadraticReflection
        (V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w))
        (V.commutativeReflectionPairRootVector A v w x)
        (V.commutativeReflectionPairRootVector A v w m) =
      V.commutativeReflectionPairRootVector A v w
        (CliffordAlgebra.quadraticReflection
          (V.commutativeScalarExtensionQuadraticForm A) x m) := by
  let f := IsScalarTower.toAlgHom ℚ A
    (V.commutativeReflectionPairRootAlgebra A v w)
  have hQ (z : Fin n → A) :
      V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootVector A v w z) =
        f (V.commutativeScalarExtensionQuadraticForm A z) := by
    simpa [f, commutativeReflectionPairRootVector] using
      V.commutativeScalarExtensionQuadraticForm_map A f z
  have hpolar :
      QuadraticMap.polar
          (V.commutativeScalarExtensionQuadraticForm
            (V.commutativeReflectionPairRootAlgebra A v w))
          (V.commutativeReflectionPairRootVector A v w x)
          (V.commutativeReflectionPairRootVector A v w m) =
        f (QuadraticMap.polar
          (V.commutativeScalarExtensionQuadraticForm A) x m) := by
    simp only [QuadraticMap.polar]
    rw [← show V.commutativeReflectionPairRootVector A v w (x + m) =
        V.commutativeReflectionPairRootVector A v w x +
          V.commutativeReflectionPairRootVector A v w m by
      ext i
      simp [commutativeReflectionPairRootVector]]
    rw [hQ, hQ, hQ, map_sub, map_sub]
  have hinv :
      ⅟(V.commutativeScalarExtensionQuadraticForm
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootVector A v w x)) =
      f (⅟(V.commutativeScalarExtensionQuadraticForm A x)) := by
    apply invOf_eq_right_inv
    rw [hQ, ← map_mul, mul_invOf_self, map_one]
  rw [CliffordAlgebra.quadraticReflection_apply,
    CliffordAlgebra.quadraticReflection_apply]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    commutativeReflectionPairRootVector]
  rw [hpolar, hinv, map_sub, map_mul, map_mul]
  rfl

theorem commutativeReflectionPairRootMatrix_eq_map
    (v w : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)] :
    V.commutativeReflectionPairRootMatrix A v w =
      (LinearMap.toMatrix'
        (CliffordAlgebra.quadraticReflectionPair
          (V.commutativeScalarExtensionQuadraticForm A) v w).toLinearMap).map
        (algebraMap A (V.commutativeReflectionPairRootAlgebra A v w)) := by
  letI := V.commutativeReflectionPairRootVectorInvertible A v w v
  letI := V.commutativeReflectionPairRootVectorInvertible A v w w
  ext i j
  simp only [commutativeReflectionPairRootMatrix, LinearMap.toMatrix'_apply,
    Matrix.map_apply]
  change
    (CliffordAlgebra.quadraticReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        (V.commutativeReflectionPairRootAlgebra A v w))
      (V.commutativeReflectionPairRootVector A v w v)
      (V.commutativeReflectionPairRootVector A v w w)
      (Pi.single j 1)) i =
    algebraMap A (V.commutativeReflectionPairRootAlgebra A v w)
      ((CliffordAlgebra.quadraticReflectionPair
        (V.commutativeScalarExtensionQuadraticForm A) v w
        (Pi.single j 1)) i)
  rw [CliffordAlgebra.quadraticReflectionPair_apply,
    CliffordAlgebra.quadraticReflectionPair_apply]
  rw [show (Pi.single j (1 : V.commutativeReflectionPairRootAlgebra A v w) :
      Fin n → V.commutativeReflectionPairRootAlgebra A v w) =
      V.commutativeReflectionPairRootVector A v w
        (Pi.single j (1 : A) : Fin n → A) by
    ext k
    simp [commutativeReflectionPairRootVector, Pi.single_apply]]
  rw [V.commutativeReflectionPairRoot_quadraticReflection_map A v w w]
  rw [V.commutativeReflectionPairRoot_quadraticReflection_map A v w v]
  rfl

theorem commutativeReflectionPairRootCandidatePoint_image
    (v w : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
    [Invertible (V.commutativeScalarExtensionQuadraticForm A w)] :
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootCandidatePoint A v w) =
      V.specialOrthogonalMatrixGroupMap
        (IsScalarTower.toAlgHom ℚ A
          (V.commutativeReflectionPairRootAlgebra A v w))
        (V.commutativeReflectionPairSpecialOrthogonalMatrixGroup A v w) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix]
  rw [V.specialOrthogonalMatrixGroupMap_apply_matrix]
  rw [V.commutativeReflectionPairSpecialOrthogonalMatrixGroup_apply_matrix]
  change V.commutativeReflectionPairRootCandidatePoint A v w
      (V.cliffordSpinCandidateMatrixCoordinate i j) = _
  rw [V.commutativeReflectionPairRootCandidatePoint_matrixCoordinate]
  change V.commutativeReflectionPairRootMatrix A v w i j =
    (LinearMap.toMatrix'
      (CliffordAlgebra.quadraticReflectionPair
        (V.commutativeScalarExtensionQuadraticForm A) v w).toLinearMap).map
      (algebraMap A (V.commutativeReflectionPairRootAlgebra A v w)) i j
  exact congrFun (congrFun
    (V.commutativeReflectionPairRootMatrix_eq_map A v w) i) j

universe u

variable (K : Type u) [Field K] [CharZero K]

abbrev ReflectionPair :=
  QuadraticMap.ReflectionWord.ReflectionPair
    (V.commutativeScalarExtensionQuadraticForm K)

/-- The special-orthogonal matrix represented by one certified pair.  The
tuple is reversed when passed to `quadraticReflectionPair`, matching the
reflection-word evaluation convention. -/
def reflectionPairMatrixGroup (p : V.ReflectionPair K) :
    V.specialOrthogonalMatrixGroup K := by
  letI : Invertible
      ((V.commutativeScalarExtensionQuadraticForm K) p.2.1) :=
    invertibleOfNonzero p.2.2
  letI : Invertible
      ((V.commutativeScalarExtensionQuadraticForm K) p.1.1) :=
    invertibleOfNonzero p.1.2
  exact V.commutativeReflectionPairSpecialOrthogonalMatrixGroup K p.2.1 p.1.1

@[simp]
theorem reflectionPairMatrixGroup_apply_matrix (p : V.ReflectionPair K) :
    letI : Invertible
        ((V.commutativeScalarExtensionQuadraticForm K) p.2.1) :=
      invertibleOfNonzero p.2.2
    letI : Invertible
        ((V.commutativeScalarExtensionQuadraticForm K) p.1.1) :=
      invertibleOfNonzero p.1.2
    (V.reflectionPairMatrixGroup K p).1.1.1 =
      LinearMap.toMatrix'
        (CliffordAlgebra.quadraticReflectionPair
          (V.commutativeScalarExtensionQuadraticForm K) p.2.1 p.1.1).toLinearMap := by
  letI : Invertible
      ((V.commutativeScalarExtensionQuadraticForm K) p.2.1) :=
    invertibleOfNonzero p.2.2
  letI : Invertible
      ((V.commutativeScalarExtensionQuadraticForm K) p.1.1) :=
    invertibleOfNonzero p.1.2
  exact V.commutativeReflectionPairSpecialOrthogonalMatrixGroup_apply_matrix
    K p.2.1 p.1.1

/-- Matrix product represented by a list of consecutive reflection pairs. -/
def reflectionPairsMatrixGroup :
    List (V.ReflectionPair K) → V.specialOrthogonalMatrixGroup K
  | [] => 1
  | p :: ps => reflectionPairsMatrixGroup ps * V.reflectionPairMatrixGroup K p

@[simp]
theorem reflectionPairsMatrixGroup_nil :
    V.reflectionPairsMatrixGroup K [] = 1 := rfl

@[simp]
theorem reflectionPairsMatrixGroup_cons
    (p : V.ReflectionPair K) (ps : List (V.ReflectionPair K)) :
    V.reflectionPairsMatrixGroup K (p :: ps) =
      V.reflectionPairsMatrixGroup K ps * V.reflectionPairMatrixGroup K p := rfl

/-- The recursively multiplied pair matrix is literally the matrix of the
flattened reflection word. -/
theorem reflectionPairsMatrixGroup_apply_matrix
    (ps : List (V.ReflectionPair K)) :
    (V.reflectionPairsMatrixGroup K ps).1.1.1 =
      LinearMap.toMatrix'
        (QuadraticMap.ReflectionWord.eval
          (V.commutativeScalarExtensionQuadraticForm K)
          (QuadraticMap.ReflectionWord.flattenPairs
            (V.commutativeScalarExtensionQuadraticForm K) ps)).toLinearEquiv.toLinearMap := by
  induction ps with
  | nil =>
      simp only [reflectionPairsMatrixGroup_nil,
        QuadraticMap.ReflectionWord.flattenPairs_nil,
        QuadraticMap.ReflectionWord.eval_nil,
        QuadraticMap.IsometryEquiv.refl,
        LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
      rfl
  | cons p ps ih =>
      letI : Invertible
          ((V.commutativeScalarExtensionQuadraticForm K) p.2.1) :=
        invertibleOfNonzero p.2.2
      letI : Invertible
          ((V.commutativeScalarExtensionQuadraticForm K) p.1.1) :=
        invertibleOfNonzero p.1.2
      rw [V.reflectionPairsMatrixGroup_cons]
      change (V.reflectionPairsMatrixGroup K ps).1.1.1 *
          (V.reflectionPairMatrixGroup K p).1.1.1 = _
      rw [ih, V.reflectionPairMatrixGroup_apply_matrix]
      simp only [QuadraticMap.ReflectionWord.flattenPairs_cons,
        QuadraticMap.ReflectionWord.eval_cons]
      change LinearMap.toMatrix'
          (QuadraticMap.ReflectionWord.eval
            (V.commutativeScalarExtensionQuadraticForm K)
            (QuadraticMap.ReflectionWord.flattenPairs
              (V.commutativeScalarExtensionQuadraticForm K) ps)).toLinearEquiv.toLinearMap *
          LinearMap.toMatrix'
            (CliffordAlgebra.quadraticReflectionPair
              (V.commutativeScalarExtensionQuadraticForm K)
              p.2.1 p.1.1).toLinearMap =
        LinearMap.toMatrix'
          ((QuadraticMap.ReflectionWord.eval
            (V.commutativeScalarExtensionQuadraticForm K)
            (QuadraticMap.ReflectionWord.flattenPairs
              (V.commutativeScalarExtensionQuadraticForm K) ps)).toLinearEquiv.toLinearMap ∘ₗ
            (CliffordAlgebra.quadraticReflectionPair
              (V.commutativeScalarExtensionQuadraticForm K)
              p.2.1 p.1.1).toLinearMap)
      rw [LinearMap.toMatrix'_comp]

/-- A finite tower of quadratic root extensions carrying one candidate point
and its certified special-orthogonal image. -/
structure ReflectionPairFppfLift (ps : List (V.ReflectionPair K)) where
  Carrier : Type u
  [commRing : CommRing Carrier]
  [nontrivial : Nontrivial Carrier]
  [algebra : Algebra ℚ Carrier]
  base : K →ₐ[ℚ] Carrier
  faithfullyFlat : base.toRingHom.FaithfullyFlat
  finitePresentation : base.toRingHom.FinitePresentation
  point : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] Carrier
  target : V.specialOrthogonalMatrixGroup Carrier
  image_eq :
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup Carrier point =
      target
  target_eq :
    target = V.specialOrthogonalMatrixGroupMap base
      (V.reflectionPairsMatrixGroup K ps)

attribute [instance] ReflectionPairFppfLift.commRing
  ReflectionPairFppfLift.nontrivial ReflectionPairFppfLift.algebra

namespace ReflectionPairFppfLift

variable {V K}

/-- The empty reflection-pair list lifts over the base field itself. -/
def nil : V.ReflectionPairFppfLift K [] where
  Carrier := K
  base := AlgHom.id ℚ K
  faithfullyFlat := RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  finitePresentation := RingHom.FinitePresentation.of_bijective Function.bijective_id
  point := 1
  target := 1
  image_eq := map_one _
  target_eq := by
    change 1 = V.specialOrthogonalMatrixGroupMap (AlgHom.id ℚ K) 1
    rw [map_one]

set_option maxHeartbeats 800000 in
/-- Extend an existing tail lift by adjoining the quadratic root normalizing
one more reflection pair.  The pair is supplied to the Clifford constructor
in reversed tuple order, so that its action agrees with `eval_pair_apply`. -/
def cons (p : V.ReflectionPair K) {ps : List (V.ReflectionPair K)}
    (tail : V.ReflectionPairFppfLift K ps) :
    V.ReflectionPairFppfLift K (p :: ps) := by
  let A := tail.Carrier
  let f : K →ₐ[ℚ] A := tail.base
  let v : Fin n → A := fun i => f (p.2.1 i)
  let w : Fin n → A := fun i => f (p.1.1 i)
  letI : Invertible
      ((V.commutativeScalarExtensionQuadraticForm K) p.2.1) :=
    invertibleOfNonzero p.2.2
  letI : Invertible
      ((V.commutativeScalarExtensionQuadraticForm K) p.1.1) :=
    invertibleOfNonzero p.1.2
  letI : Invertible (V.commutativeScalarExtensionQuadraticForm A v) :=
    Invertible.copy
      (Invertible.map f.toRingHom
        ((V.commutativeScalarExtensionQuadraticForm K) p.2.1)) _
      (by
        simpa [v] using
          V.commutativeScalarExtensionQuadraticForm_map K f p.2.1)
  letI : Invertible (V.commutativeScalarExtensionQuadraticForm A w) :=
    Invertible.copy
      (Invertible.map f.toRingHom
        ((V.commutativeScalarExtensionQuadraticForm K) p.1.1)) _
      (by
        simpa [w] using
          V.commutativeScalarExtensionQuadraticForm_map K f p.1.1)
  let B := V.commutativeReflectionPairRootAlgebra A v w
  let g : A →ₐ[ℚ] B := IsScalarTower.toAlgHom ℚ A B
  have hgff : g.toRingHom.FaithfullyFlat := by
    exact RationalTamagawa.quadraticRootAlgebra_faithfullyFlat A _
  have hgfp : g.toRingHom.FinitePresentation := by
    exact RationalTamagawa.quadraticRootAlgebra_finitePresentation A _
  letI : Nontrivial B := hgff.injective.nontrivial
  let mappedTail : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] B :=
    V.cliffordSpinCandidateCoordinateAlgHomMap A g tail.point
  let pairPoint : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] B :=
    V.commutativeReflectionPairRootCandidatePoint A v w
  let pairTarget : V.specialOrthogonalMatrixGroup B :=
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup B pairPoint
  refine
    { Carrier := B
      base := g.comp f
      faithfullyFlat :=
        RingHom.FaithfullyFlat.stableUnderComposition f.toRingHom g.toRingHom
          tail.faithfullyFlat hgff
      finitePresentation :=
        RingHom.finitePresentation_stableUnderComposition f.toRingHom g.toRingHom
          tail.finitePresentation hgfp
      point := mappedTail * pairPoint
      target := V.specialOrthogonalMatrixGroupMap g tail.target * pairTarget
      image_eq := ?_
      target_eq := ?_ }
  · rw [map_mul]
    change V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup B
          (g.comp tail.point) *
        V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup B
          pairPoint =
      V.specialOrthogonalMatrixGroupMap g tail.target * pairTarget
    rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_map,
      tail.image_eq]
  · have hpairA :
        V.specialOrthogonalMatrixGroupMap f
            (V.reflectionPairMatrixGroup K p) =
          V.commutativeReflectionPairSpecialOrthogonalMatrixGroup A v w := by
      simpa [reflectionPairMatrixGroup, v, w] using
        V.commutativeReflectionPairSpecialOrthogonalMatrixGroup_map
          K f p.2.1 p.1.1
    have hpairB :
        pairTarget = V.specialOrthogonalMatrixGroupMap g
          (V.commutativeReflectionPairSpecialOrthogonalMatrixGroup A v w) := by
      exact V.commutativeReflectionPairRootCandidatePoint_image A v w
    calc
      V.specialOrthogonalMatrixGroupMap g tail.target * pairTarget =
          V.specialOrthogonalMatrixGroupMap g
              (V.specialOrthogonalMatrixGroupMap f
                (V.reflectionPairsMatrixGroup K ps)) *
            V.specialOrthogonalMatrixGroupMap g
              (V.specialOrthogonalMatrixGroupMap f
                (V.reflectionPairMatrixGroup K p)) := by
        rw [tail.target_eq, hpairB, hpairA]
      _ = V.specialOrthogonalMatrixGroupMap g
          (V.specialOrthogonalMatrixGroupMap f
            (V.reflectionPairsMatrixGroup K ps *
              V.reflectionPairMatrixGroup K p)) := by
        rw [map_mul, map_mul]
      _ = V.specialOrthogonalMatrixGroupMap (g.comp f)
          (V.reflectionPairsMatrixGroup K ps *
            V.reflectionPairMatrixGroup K p) :=
        V.specialOrthogonalMatrixGroupMap_comp f g _

/-- Iterate the quadratic root construction along a finite reflection-pair
list. -/
def ofList : (ps : List (V.ReflectionPair K)) → V.ReflectionPairFppfLift K ps
  | [] => nil
  | p :: ps => cons p (ofList ps)

/-- Ring-theoretic fppf certificate for the composite terminal extension. -/
theorem base_faithfullyFlat_and_finitePresentation
    (lift : V.ReflectionPairFppfLift K ps) :
    lift.base.toRingHom.FaithfullyFlat ∧
      lift.base.toRingHom.FinitePresentation :=
  ⟨lift.faithfullyFlat, lift.finitePresentation⟩

/-- The terminal candidate point maps to the scalar extension of the original
paired reflection-word matrix. -/
theorem image_eq_scalarExtension (lift : V.ReflectionPairFppfLift K ps) :
    V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup
        lift.Carrier lift.point =
      V.specialOrthogonalMatrixGroupMap lift.base
        (V.reflectionPairsMatrixGroup K ps) := by
  rw [lift.image_eq, lift.target_eq]

/-- Entrywise form of the terminal-image theorem, expressed directly by the
matrix of the evaluated flattened reflection word. -/
theorem point_matrixCoordinate_eq_eval
    (lift : V.ReflectionPairFppfLift K ps) (i j : Fin n) :
    lift.point (V.cliffordSpinCandidateMatrixCoordinate i j) =
      lift.base
        (LinearMap.toMatrix'
          (QuadraticMap.ReflectionWord.eval
            (V.commutativeScalarExtensionQuadraticForm K)
            (QuadraticMap.ReflectionWord.flattenPairs
              (V.commutativeScalarExtensionQuadraticForm K) ps)).toLinearEquiv.toLinearMap i j) := by
  have h := congrArg
    (fun g : V.specialOrthogonalMatrixGroup lift.Carrier => g.1.1.1 i j)
    (lift.image_eq_scalarExtension)
  calc
    lift.point (V.cliffordSpinCandidateMatrixCoordinate i j) =
        (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup
          lift.Carrier lift.point).1.1.1 i j := by
      rw [V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup_apply_matrix]
      rfl
    _ = (V.specialOrthogonalMatrixGroupMap lift.base
        (V.reflectionPairsMatrixGroup K ps)).1.1.1 i j := h
    _ = lift.base
        (LinearMap.toMatrix'
          (QuadraticMap.ReflectionWord.eval
            (V.commutativeScalarExtensionQuadraticForm K)
            (QuadraticMap.ReflectionWord.flattenPairs
              (V.commutativeScalarExtensionQuadraticForm K) ps)).toLinearEquiv.toLinearMap i j) := by
      rw [V.specialOrthogonalMatrixGroupMap_apply_matrix,
        Matrix.map_apply, V.reflectionPairsMatrixGroup_apply_matrix]
      rfl

/-- Every determinant-one isometry has one finite faithfully-flat quadratic
root tower over which it is the image of an actual Spin-candidate point. -/
theorem exists_fppfLift_of_isometry_det_one
    (hQ : (V.commutativeScalarExtensionQuadraticForm K).associated.Nondegenerate)
    (g : (V.commutativeScalarExtensionQuadraticForm K).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm K))
    (hdet : LinearMap.det g.toLinearEquiv.toLinearMap = 1) :
    ∃ ps : List (V.ReflectionPair K),
      ∃ lift : V.ReflectionPairFppfLift K ps,
        ps.length ≤ Module.finrank K (Fin n → K) ∧
        ∀ i j,
          lift.point (V.cliffordSpinCandidateMatrixCoordinate i j) =
            lift.base (LinearMap.toMatrix' g.toLinearEquiv.toLinearMap i j) := by
  obtain ⟨ps, hps, hlen⟩ :=
    QuadraticMap.ReflectionWord.exists_reflectionPairs_eval_eq
      (V.commutativeScalarExtensionQuadraticForm K) hQ g hdet
  let lift := ofList ps
  refine ⟨ps, lift, hlen, ?_⟩
  intro i j
  rw [lift.point_matrixCoordinate_eq_eval]
  rw [hps]

end ReflectionPairFppfLift

end RationalQuadraticSpaceMatrix
