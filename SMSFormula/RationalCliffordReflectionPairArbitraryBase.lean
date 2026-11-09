import SMSFormula.RationalCliffordReflectionPairNormalization

/-!
# Reflection-pair normalization over arbitrary rational algebras

This file extends the rational-vector reflection-pair lift to vectors over an
arbitrary commutative rational algebra `A`.  It identifies the coordinate
base change of the rational Clifford algebra with the Clifford algebra of the
entrywise mapped form matrix over every commutative rational algebra.

For vectors `v,w : Fin n → A` of unit quadratic value, adjoining a square
root of `(Q(v)Q(w))⁻¹` gives a normalized even Clifford product. Its action is
the ordered pair of quadratic reflections, its matrix has determinant one,
and the finite-coordinate relations therefore give a point of the
affine Spin candidate over the quadratic fppf cover.

This is a local two-reflection lift for arbitrary affine base points.  It does
not prove that every special-orthogonal point is locally a product of such
pairs; that needs a separate Cartan--Dieudonne or standard-open generation
argument.
-/

noncomputable section

open CliffordAlgebra
open scoped Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}
variable (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

def rationalAlgebraInvertibleTwo : Invertible (2 : A) :=
  Invertible.copy
    (Invertible.map (algebraMap ℚ A) (2 : ℚ)) (2 : A)
      (map_ofNat (algebraMap ℚ A) 2).symm

attribute [local instance] rationalAlgebraInvertibleTwo

def commutativeScalarExtensionFormMatrix : Matrix (Fin n) (Fin n) A :=
  V.pairingMatrix.map (algebraMap ℚ A)

theorem commutativeScalarExtensionFormMatrix_isSymm :
    (V.commutativeScalarExtensionFormMatrix A).IsSymm := by
  exact V.form_symm.map (algebraMap ℚ A)

def commutativeScalarExtensionQuadraticForm : QuadraticForm A (Fin n → A) :=
  (V.commutativeScalarExtensionFormMatrix A).toQuadraticMap'

@[simp]
theorem commutativeScalarExtensionQuadraticForm_toMatrix' :
    (V.commutativeScalarExtensionQuadraticForm A).toMatrix' =
      V.commutativeScalarExtensionFormMatrix A :=
  Matrix.toMatrix'_toQuadraticMap'_of_isSymm _
    (V.commutativeScalarExtensionFormMatrix_isSymm A)

/-- The canonical coordinates on the scalar extension of the rational
coordinate module. -/
def commutativeScalarExtensionModuleEquiv :
    A ⊗[ℚ] (Fin n → ℚ) ≃ₗ[A] (Fin n → A) :=
  TensorProduct.piScalarRight ℚ A A (Fin n)

/-- The canonical coordinate equivalence identifies base change of the
rational quadratic form with the quadratic form of the mapped matrix. -/
theorem commutativeScalarExtensionModuleEquiv_isometry :
    ∀ z : A ⊗[ℚ] (Fin n → ℚ),
      V.commutativeScalarExtensionQuadraticForm A
          (commutativeScalarExtensionModuleEquiv (n := n) A z) =
        V.quadraticForm.baseChange A z := by
  intro z
  rw [← (V.commutativeScalarExtensionQuadraticForm A).associated_eq_self_apply ℕ]
  rw [← (V.quadraticForm.baseChange A).associated_eq_self_apply ℕ]
  suffices hbilin : ∀ x y : A ⊗[ℚ] (Fin n → ℚ),
      (V.commutativeScalarExtensionQuadraticForm A).associated
          (commutativeScalarExtensionModuleEquiv (n := n) A x)
          (commutativeScalarExtensionModuleEquiv (n := n) A y) =
        (V.quadraticForm.baseChange A).associated x y by
    exact hbilin z z
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      intro z
      simp only [map_add, LinearMap.add_apply, hx z, hy z]
  | tmul a v =>
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simp only [map_add, hx, hy]
      | tmul b w =>
          rw [QuadraticForm.associated_baseChange,
            LinearMap.BilinForm.baseChange_tmul]
          change (V.commutativeScalarExtensionQuadraticForm A).associated
              (fun i => v i • a) (fun i => w i • b) = _
          change QuadraticMap.associatedHom ℕ
              (LinearMap.BilinMap.toQuadraticMap
                (Matrix.toBilin' (V.commutativeScalarExtensionFormMatrix A)))
              (fun i => v i • a) (fun i => w i • b) = _
          have hsymmK :
              (Matrix.toBilin' (V.commutativeScalarExtensionFormMatrix A)).IsSymm := by
            constructor
            intro s t
            simp only [Matrix.toBilin'_apply]
            calc
              (∑ i, ∑ j, s i * V.commutativeScalarExtensionFormMatrix A i j * t j) =
                  ∑ j, ∑ i, s i * V.commutativeScalarExtensionFormMatrix A i j * t j :=
                Finset.sum_comm
              _ = ∑ i, ∑ j, t i * V.commutativeScalarExtensionFormMatrix A i j * s j := by
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro j _
                rw [(V.commutativeScalarExtensionFormMatrix_isSymm A).apply i j]
                ring
          rw [QuadraticMap.associated_left_inverse ℕ hsymmK.1]
          change Matrix.toBilin' (V.commutativeScalarExtensionFormMatrix A)
              (fun i => v i • a) (fun i => w i • b) = _
          have hsymmQ : (Matrix.toBilin' V.pairingMatrix).IsSymm := by
            constructor
            intro s t
            simp only [Matrix.toBilin'_apply]
            calc
              (∑ i, ∑ j, s i * V.pairingMatrix i j * t j) =
                  ∑ j, ∑ i, s i * V.pairingMatrix i j * t j :=
                Finset.sum_comm
              _ = ∑ i, ∑ j, t i * V.pairingMatrix i j * s j := by
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro j _
                rw [V.form_symm.apply i j]
                ring
          change Matrix.toBilin' (V.commutativeScalarExtensionFormMatrix A)
              (fun i => v i • a) (fun i => w i • b) =
            QuadraticMap.associatedHom ℕ V.quadraticForm v w • (a * b)
          change _ = QuadraticMap.associatedHom ℕ
            (LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' V.pairingMatrix)) v w •
              (a * b)
          rw [QuadraticMap.associated_left_inverse ℕ hsymmQ.1]
          simp only [Matrix.toBilin'_apply, commutativeScalarExtensionFormMatrix,
            Matrix.map_apply]
          simp only [Algebra.smul_def]
          change (∑ i, ∑ j,
              (algebraMap ℚ A (v i) * a) * algebraMap ℚ A (V.pairingMatrix i j) *
                (algebraMap ℚ A (w j) * b)) =
            algebraMap ℚ A (∑ i, ∑ j, v i * V.pairingMatrix i j * w j) * (a * b)
          simp_rw [map_sum, map_mul]
          have hterm (i j : Fin n) :
              (algebraMap ℚ A (v i) * a) *
                    algebraMap ℚ A (V.pairingMatrix i j) *
                  (algebraMap ℚ A (w j) * b) =
                (algebraMap ℚ A (v i) *
                    algebraMap ℚ A (V.pairingMatrix i j) *
                  algebraMap ℚ A (w j)) * (a * b) := by
            ring
          simp_rw [hterm]
          calc
            (∑ i, ∑ j,
                (algebraMap ℚ A (v i) *
                    algebraMap ℚ A (V.pairingMatrix i j) *
                  algebraMap ℚ A (w j)) * (a * b)) =
                ∑ i, (∑ j,
                  algebraMap ℚ A (v i) *
                    algebraMap ℚ A (V.pairingMatrix i j) *
                  algebraMap ℚ A (w j)) * (a * b) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
            _ = (∑ i, ∑ j,
                  algebraMap ℚ A (v i) *
                    algebraMap ℚ A (V.pairingMatrix i j) *
                  algebraMap ℚ A (w j)) * (a * b) :=
              by rw [Finset.sum_mul]

/-- The isometry between the abstract base-changed quadratic form and its
matrix-coordinate realization. -/
def commutativeScalarExtensionQuadraticIsometryEquiv :
    (V.quadraticForm.baseChange A).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm A) where
  toLinearEquiv := commutativeScalarExtensionModuleEquiv (n := n) A
  map_app' := V.commutativeScalarExtensionModuleEquiv_isometry A

/-- The Clifford algebras of the abstract and matrix-coordinate scalar
extensions are isomorphic. -/
def commutativeScalarExtensionCliffordAlgEquiv :
    CliffordAlgebra (V.quadraticForm.baseChange A) ≃ₐ[A]
      CliffordAlgebra (V.commutativeScalarExtensionQuadraticForm A) :=
  CliffordAlgebra.equivOfIsometry
    (V.commutativeScalarExtensionQuadraticIsometryEquiv A)

/-- Base change of the rational Clifford algebra, expressed directly in the
matrix-coordinate Clifford algebra over `A`. -/
def commutativeTensorCliffordEquiv :
    A ⊗[ℚ] CliffordAlgebra V.quadraticForm ≃ₐ[A]
      CliffordAlgebra (V.commutativeScalarExtensionQuadraticForm A) :=
  (CliffordAlgebra.equivBaseChange A V.quadraticForm).symm.trans
    (V.commutativeScalarExtensionCliffordAlgEquiv A)

@[simp]
theorem commutativeTensorCliffordEquiv_tmul_ι
    (a : A) (v : Fin n → ℚ) :
    V.commutativeTensorCliffordEquiv A
        (a ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm v) =
      CliffordAlgebra.ι (V.commutativeScalarExtensionQuadraticForm A)
        (fun i => v i • a) := by
  rw [commutativeTensorCliffordEquiv, AlgEquiv.trans_apply]
  change V.commutativeScalarExtensionCliffordAlgEquiv A
      (CliffordAlgebra.ofBaseChange A V.quadraticForm
        (a ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm v)) = _
  rw [CliffordAlgebra.ofBaseChange_tmul_ι]
  change CliffordAlgebra.equivOfIsometry
      (V.commutativeScalarExtensionQuadraticIsometryEquiv A)
        (CliffordAlgebra.ι (V.quadraticForm.baseChange A) (a ⊗ₜ[ℚ] v)) = _
  rw [CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  rfl

/-- The Clifford generator attached to a vector with coefficients in the
scalar algebra, written in the fixed rational Clifford coordinates. -/
def cliffordCoordinateBaseChangeVectorOfCoordinates
    (x : Fin n → A) :
    V.cliffordCoordinateBaseChangeAlgebra A :=
  ∑ i, x i • V.cliffordCoordinateBaseChangeVector A i

omit [Algebra ℚ A] in
theorem commutativeScalarExtension_single_sum (x : Fin n → A) :
    (∑ i, x i • (Pi.single i (1 : A) : Fin n → A)) = x := by
  ext j
  simp [Pi.single_apply]

@[simp]
theorem commutativeTensorCliffordEquiv_baseChangeVector (i : Fin n) :
    V.commutativeTensorCliffordEquiv A
        (V.cliffordCoordinateBaseChangeVector A i) =
      CliffordAlgebra.ι (V.commutativeScalarExtensionQuadraticForm A)
        (Pi.single i (1 : A) : Fin n → A) := by
  change V.commutativeTensorCliffordEquiv A
      (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
        (Pi.single i (1 : ℚ) : Fin n → ℚ)) = _
  rw [V.commutativeTensorCliffordEquiv_tmul_ι]
  congr 1
  ext j
  simp [Pi.single_apply]

@[simp]
theorem commutativeTensorCliffordEquiv_vectorOfCoordinates
    (x : Fin n → A) :
    V.commutativeTensorCliffordEquiv A
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates A x) =
      CliffordAlgebra.ι (V.commutativeScalarExtensionQuadraticForm A) x := by
  rw [cliffordCoordinateBaseChangeVectorOfCoordinates, map_sum]
  simp_rw [map_smul, V.commutativeTensorCliffordEquiv_baseChangeVector A]
  simp_rw [← map_smul (CliffordAlgebra.ι
    (V.commutativeScalarExtensionQuadraticForm A))]
  rw [← map_sum]
  congr 1
  exact commutativeScalarExtension_single_sum A x

@[simp]
theorem cliffordCoordinateBaseChangeInvolute_vector (i : Fin n) :
    V.cliffordCoordinateBaseChangeInvolute A
        (V.cliffordCoordinateBaseChangeVector A i) =
      -V.cliffordCoordinateBaseChangeVector A i := by
  change V.cliffordCoordinateBaseChangeInvolute A
      (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
        (Pi.single i (1 : ℚ) : Fin n → ℚ)) = _
  rw [V.cliffordCoordinateBaseChangeInvolute_tmul]
  rw [CliffordAlgebra.involute_ι, TensorProduct.tmul_neg]
  rfl

@[simp]
theorem cliffordCoordinateBaseChangeReverse_vector (i : Fin n) :
    V.cliffordCoordinateBaseChangeReverse A
        (V.cliffordCoordinateBaseChangeVector A i) =
      V.cliffordCoordinateBaseChangeVector A i := by
  change V.cliffordCoordinateBaseChangeReverse A
      (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
        (Pi.single i (1 : ℚ) : Fin n → ℚ)) = _
  rw [V.cliffordCoordinateBaseChangeReverse_tmul]
  rw [CliffordAlgebra.reverse_ι]
  rfl

@[simp]
theorem cliffordCoordinateBaseChangeInvolute_vectorOfCoordinates
    (x : Fin n → A) :
    V.cliffordCoordinateBaseChangeInvolute A
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates A x) =
      -V.cliffordCoordinateBaseChangeVectorOfCoordinates A x := by
  simp [cliffordCoordinateBaseChangeVectorOfCoordinates]

@[simp]
theorem cliffordCoordinateBaseChangeReverse_vectorOfCoordinates
    (x : Fin n → A) :
    V.cliffordCoordinateBaseChangeReverse A
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates A x) =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates A x := by
  simp [cliffordCoordinateBaseChangeVectorOfCoordinates]

theorem commutativeScalarExtensionQuadraticForm_map
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : Fin n → A) :
    V.commutativeScalarExtensionQuadraticForm B (fun i => f (x i)) =
      f (V.commutativeScalarExtensionQuadraticForm A x) := by
  simp only [commutativeScalarExtensionQuadraticForm,
    Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap,
    commutativeScalarExtensionFormMatrix]
  change (((Matrix.toLinearMap₂' B)
        (V.pairingMatrix.map (algebraMap ℚ B))) (fun i => f (x i)))
      (fun i => f (x i)) =
    f ((((Matrix.toLinearMap₂' A)
      (V.pairingMatrix.map (algebraMap ℚ A))) x) x)
  rw [Matrix.toLinearMap₂'_apply, Matrix.toLinearMap₂'_apply]
  simp only [Matrix.map_apply, smul_eq_mul]
  simp_rw [map_sum, map_mul, f.commutes]

section ReflectionPairRoot

variable (v w : Fin n → A)
variable [Invertible (V.commutativeScalarExtensionQuadraticForm A v)]
variable [Invertible (V.commutativeScalarExtensionQuadraticForm A w)]

abbrev commutativeReflectionPairRootAlgebra :=
  RationalTamagawa.QuadraticRootAlgebra A
    (⅟(V.commutativeScalarExtensionQuadraticForm A v) *
      ⅟(V.commutativeScalarExtensionQuadraticForm A w))

def commutativeReflectionPairRoot :
    V.commutativeReflectionPairRootAlgebra A v w :=
  AdjoinRoot.root
    (RationalTamagawa.quadraticRootPolynomial A
      (⅟(V.commutativeScalarExtensionQuadraticForm A v) *
        ⅟(V.commutativeScalarExtensionQuadraticForm A w)))

def commutativeReflectionPairRootVector (x : Fin n → A) :
    Fin n → V.commutativeReflectionPairRootAlgebra A v w :=
  fun i => algebraMap A (V.commutativeReflectionPairRootAlgebra A v w) (x i)

def commutativeReflectionPairRootVectorInvertible
    (x : Fin n → A)
    [Invertible (V.commutativeScalarExtensionQuadraticForm A x)] :
    Invertible
      (V.commutativeScalarExtensionQuadraticForm
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootVector A v w x)) :=
  Invertible.copy
    (Invertible.map
      (algebraMap A (V.commutativeReflectionPairRootAlgebra A v w))
      (V.commutativeScalarExtensionQuadraticForm A x)) _
    (by
      simpa [commutativeReflectionPairRootVector] using
        V.commutativeScalarExtensionQuadraticForm_map A
          (IsScalarTower.toAlgHom ℚ A
            (V.commutativeReflectionPairRootAlgebra A v w)) x)

attribute [local instance] commutativeReflectionPairRootVectorInvertible

theorem commutativeReflectionPairRoot_normalizes :
    V.commutativeReflectionPairRoot A v w ^ 2 *
          V.commutativeScalarExtensionQuadraticForm
            (V.commutativeReflectionPairRootAlgebra A v w)
            (V.commutativeReflectionPairRootVector A v w v) *
        V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootVector A v w w) = 1 := by
  rw [commutativeReflectionPairRoot,
    RationalTamagawa.quadraticRootAlgebra_root_sq]
  let f := algebraMap A (V.commutativeReflectionPairRootAlgebra A v w)
  have hv : V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootVector A v w v) =
        f (V.commutativeScalarExtensionQuadraticForm A v) := by
    simpa [f, commutativeReflectionPairRootVector] using
      V.commutativeScalarExtensionQuadraticForm_map A
        (IsScalarTower.toAlgHom ℚ A
          (V.commutativeReflectionPairRootAlgebra A v w)) v
  have hw : V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootVector A v w w) =
        f (V.commutativeScalarExtensionQuadraticForm A w) := by
    simpa [f, commutativeReflectionPairRootVector] using
      V.commutativeScalarExtensionQuadraticForm_map A
        (IsScalarTower.toAlgHom ℚ A
          (V.commutativeReflectionPairRootAlgebra A v w)) w
  rw [hv, hw]
  letI : Invertible (f (V.commutativeScalarExtensionQuadraticForm A v)) :=
    Invertible.map f (V.commutativeScalarExtensionQuadraticForm A v)
  letI : Invertible (f (V.commutativeScalarExtensionQuadraticForm A w)) :=
    Invertible.map f (V.commutativeScalarExtensionQuadraticForm A w)
  rw [map_mul, map_invOf, map_invOf]
  calc
    _ =
        (⅟(f (V.commutativeScalarExtensionQuadraticForm A v)) *
          f (V.commutativeScalarExtensionQuadraticForm A v)) *
        (⅟(f (V.commutativeScalarExtensionQuadraticForm A w)) *
          f (V.commutativeScalarExtensionQuadraticForm A w)) := by ring
    _ = 1 := by rw [invOf_mul_self, invOf_mul_self, one_mul]

def commutativeReflectionPairRootClifford :
    V.cliffordCoordinateBaseChangeAlgebra
      (V.commutativeReflectionPairRootAlgebra A v w) :=
  V.commutativeReflectionPairRoot A v w •
    (V.cliffordCoordinateBaseChangeVectorOfCoordinates
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootVector A v w v) *
      V.cliffordCoordinateBaseChangeVectorOfCoordinates
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootVector A v w w))

theorem commutativeTensorCliffordEquiv_rootClifford :
    V.commutativeTensorCliffordEquiv
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootClifford A v w) =
      CliffordAlgebra.normalizedReflectionPair
        (V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w))
        (V.commutativeReflectionPairRoot A v w)
        (V.commutativeReflectionPairRootVector A v w v)
        (V.commutativeReflectionPairRootVector A v w w) := by
  simp [commutativeReflectionPairRootClifford,
    CliffordAlgebra.normalizedReflectionPair]

theorem commutativeReflectionPairRootClifford_involute :
    V.cliffordCoordinateBaseChangeInvolute
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootClifford A v w) =
      V.commutativeReflectionPairRootClifford A v w := by
  simp only [commutativeReflectionPairRootClifford, map_smul, map_mul,
    V.cliffordCoordinateBaseChangeInvolute_vectorOfCoordinates]
  congr 1
  exact neg_mul_neg
    (V.cliffordCoordinateBaseChangeVectorOfCoordinates
      (V.commutativeReflectionPairRootAlgebra A v w)
      (V.commutativeReflectionPairRootVector A v w v))
    (V.cliffordCoordinateBaseChangeVectorOfCoordinates
      (V.commutativeReflectionPairRootAlgebra A v w)
      (V.commutativeReflectionPairRootVector A v w w))

theorem commutativeReflectionPairRootClifford_reverse :
    V.cliffordCoordinateBaseChangeReverse
        (V.commutativeReflectionPairRootAlgebra A v w)
        (V.commutativeReflectionPairRootClifford A v w) =
      V.commutativeReflectionPairRoot A v w •
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates
            (V.commutativeReflectionPairRootAlgebra A v w)
            (V.commutativeReflectionPairRootVector A v w w) *
          V.cliffordCoordinateBaseChangeVectorOfCoordinates
            (V.commutativeReflectionPairRootAlgebra A v w)
            (V.commutativeReflectionPairRootVector A v w v)) := by
  rw [commutativeReflectionPairRootClifford, map_smul,
    V.cliffordCoordinateBaseChangeReverse_mul]
  simp

theorem commutativeReflectionPairRootClifford_mul_reverse :
    V.commutativeReflectionPairRootClifford A v w *
        V.cliffordCoordinateBaseChangeReverse
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootClifford A v w) = 1 := by
  apply (V.commutativeTensorCliffordEquiv
    (V.commutativeReflectionPairRootAlgebra A v w)).injective
  rw [map_mul, map_one,
    V.commutativeTensorCliffordEquiv_rootClifford A v w,
    V.commutativeReflectionPairRootClifford_reverse]
  simp only [map_smul, map_mul,
    V.commutativeTensorCliffordEquiv_vectorOfCoordinates]
  rw [← CliffordAlgebra.reverse_normalizedReflectionPair]
  exact CliffordAlgebra.normalizedReflectionPair_mul_reverse_eq_one
      (V.commutativeScalarExtensionQuadraticForm
        (V.commutativeReflectionPairRootAlgebra A v w))
      (V.commutativeReflectionPairRoot A v w)
      (V.commutativeReflectionPairRootVector A v w v)
      (V.commutativeReflectionPairRootVector A v w w)
      (V.commutativeReflectionPairRoot_normalizes A v w)

def commutativeReflectionPairRootMatrix :
    Matrix (Fin n) (Fin n)
      (V.commutativeReflectionPairRootAlgebra A v w) :=
  LinearMap.toMatrix'
    (CliffordAlgebra.quadraticReflectionPair
      (V.commutativeScalarExtensionQuadraticForm
        (V.commutativeReflectionPairRootAlgebra A v w))
      (V.commutativeReflectionPairRootVector A v w v)
      (V.commutativeReflectionPairRootVector A v w w)).toLinearMap

def commutativeReflectionPairRootSpecialOrthogonalMatrixPoint :
    V.specialOrthogonalMatrixPoint
      (V.commutativeReflectionPairRootAlgebra A v w) := by
  let Q := V.commutativeScalarExtensionQuadraticForm
    (V.commutativeReflectionPairRootAlgebra A v w)
  let e := CliffordAlgebra.quadraticReflectionPair Q
    (V.commutativeReflectionPairRootVector A v w v)
    (V.commutativeReflectionPairRootVector A v w w)
  refine ⟨V.commutativeReflectionPairRootMatrix A v w, ?_, ?_⟩
  · have hcomp : Q.comp e.toLinearMap = Q := by
      apply QuadraticMap.ext
      intro m
      exact CliffordAlgebra.quadraticReflectionPair_map_app Q
        (V.commutativeReflectionPairRootVector A v w v)
        (V.commutativeReflectionPairRootVector A v w w) m
    have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
    rw [QuadraticForm.toMatrix'_comp,
      V.commutativeScalarExtensionQuadraticForm_toMatrix'] at hmatrix
    simpa [commutativeReflectionPairRootMatrix, e, Q,
      specialOrthogonalMappedFormMatrix,
      commutativeScalarExtensionFormMatrix] using hmatrix
  · exact CliffordAlgebra.quadraticReflectionPair_toMatrix'_det
      Q (V.commutativeReflectionPairRootVector A v w v)
        (V.commutativeReflectionPairRootVector A v w w)

theorem commutativeReflectionPairRootClifford_conjugation
    (m : Fin n → V.commutativeReflectionPairRootAlgebra A v w) :
    V.commutativeReflectionPairRootClifford A v w *
          V.cliffordCoordinateBaseChangeVectorOfCoordinates
            (V.commutativeReflectionPairRootAlgebra A v w) m *
        V.cliffordCoordinateBaseChangeReverse
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootClifford A v w) =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates
        (V.commutativeReflectionPairRootAlgebra A v w)
        (CliffordAlgebra.quadraticReflectionPair
          (V.commutativeScalarExtensionQuadraticForm
            (V.commutativeReflectionPairRootAlgebra A v w))
          (V.commutativeReflectionPairRootVector A v w v)
          (V.commutativeReflectionPairRootVector A v w w) m) := by
  apply (V.commutativeTensorCliffordEquiv
    (V.commutativeReflectionPairRootAlgebra A v w)).injective
  rw [map_mul, map_mul,
    V.commutativeTensorCliffordEquiv_rootClifford A v w,
    V.commutativeTensorCliffordEquiv_vectorOfCoordinates,
    V.commutativeReflectionPairRootClifford_reverse]
  simp only [map_smul, map_mul,
    V.commutativeTensorCliffordEquiv_vectorOfCoordinates]
  rw [← CliffordAlgebra.reverse_normalizedReflectionPair,
    CliffordAlgebra.normalizedReflectionPair_conjugation,
    CliffordAlgebra.reflectionPairVector_eq_reflections _ _ _ _ _
      (V.commutativeReflectionPairRoot_normalizes A v w)]
  rfl

theorem commutativeReflectionPairRoot_single_eq_sum_matrix (i : Fin n) :
    CliffordAlgebra.quadraticReflectionPair
        (V.commutativeScalarExtensionQuadraticForm
          (V.commutativeReflectionPairRootAlgebra A v w))
        (V.commutativeReflectionPairRootVector A v w v)
        (V.commutativeReflectionPairRootVector A v w w)
        (Pi.single i 1) =
      ∑ j, V.commutativeReflectionPairRootMatrix A v w j i •
        (Pi.single j (1 : V.commutativeReflectionPairRootAlgebra A v w) :
          Fin n → V.commutativeReflectionPairRootAlgebra A v w) := by
  let e := CliffordAlgebra.quadraticReflectionPair
    (V.commutativeScalarExtensionQuadraticForm
      (V.commutativeReflectionPairRootAlgebra A v w))
    (V.commutativeReflectionPairRootVector A v w v)
    (V.commutativeReflectionPairRootVector A v w w)
  have h := LinearMap.congr_fun
    (Matrix.toLin'_toMatrix' e.toLinearMap) (Pi.single i 1)
  ext k
  have hk := congrFun h k
  convert hk.symm using 1
  simp [commutativeReflectionPairRootMatrix, e, Pi.single_apply]

theorem commutativeReflectionPairRootClifford_vectorGraph (i : Fin n) :
    V.commutativeReflectionPairRootClifford A v w *
          V.cliffordCoordinateBaseChangeVector
            (V.commutativeReflectionPairRootAlgebra A v w) i *
        V.cliffordCoordinateBaseChangeReverse
          (V.commutativeReflectionPairRootAlgebra A v w)
          (V.commutativeReflectionPairRootClifford A v w) =
      ∑ j,
        (V.commutativeReflectionPairRootSpecialOrthogonalMatrixPoint
          A v w).1 j i •
          V.cliffordCoordinateBaseChangeVector
            (V.commutativeReflectionPairRootAlgebra A v w) j := by
  rw [show V.cliffordCoordinateBaseChangeVector
      (V.commutativeReflectionPairRootAlgebra A v w) i =
        V.cliffordCoordinateBaseChangeVectorOfCoordinates
          (V.commutativeReflectionPairRootAlgebra A v w)
          (Pi.single i 1) by
    apply (V.commutativeTensorCliffordEquiv
      (V.commutativeReflectionPairRootAlgebra A v w)).injective
    simp]
  rw [V.commutativeReflectionPairRootClifford_conjugation A v w]
  apply (V.commutativeTensorCliffordEquiv
    (V.commutativeReflectionPairRootAlgebra A v w)).injective
  rw [V.commutativeTensorCliffordEquiv_vectorOfCoordinates,
    V.commutativeReflectionPairRoot_single_eq_sum_matrix A v w i, map_sum]
  conv_rhs => rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [commutativeReflectionPairRootSpecialOrthogonalMatrixPoint,
    V.commutativeTensorCliffordEquiv_baseChangeVector]

def commutativeReflectionPairRootCandidatePointData :
    V.CliffordSpinCandidatePointData
      (V.commutativeReflectionPairRootAlgebra A v w) where
  clifford := V.commutativeReflectionPairRootClifford A v w
  matrixPoint :=
    V.commutativeReflectionPairRootSpecialOrthogonalMatrixPoint A v w
  involute_eq :=
    V.commutativeReflectionPairRootClifford_involute A v w
  mul_reverse_eq_one :=
    V.commutativeReflectionPairRootClifford_mul_reverse A v w
  vectorGraph :=
    V.commutativeReflectionPairRootClifford_vectorGraph A v w

def commutativeReflectionPairRootCandidatePoint :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.commutativeReflectionPairRootAlgebra A v w :=
  V.cliffordSpinCandidateCoordinateAlgHomOfPointData
    (V.commutativeReflectionPairRootAlgebra A v w)
    (V.commutativeReflectionPairRootCandidatePointData A v w)

@[simp]
theorem commutativeReflectionPairRootCandidatePoint_matrixCoordinate
    (i j : Fin n) :
    V.commutativeReflectionPairRootCandidatePoint A v w
        (V.cliffordSpinCandidateMatrixCoordinate i j) =
      V.commutativeReflectionPairRootMatrix A v w i j := by
  rw [commutativeReflectionPairRootCandidatePoint,
    V.cliffordSpinCandidateCoordinateAlgHomOfPointData_matrixCoordinate]
  rfl

end ReflectionPairRoot

end RationalQuadraticSpaceMatrix
