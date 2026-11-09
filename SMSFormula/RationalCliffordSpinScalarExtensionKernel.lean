import SMSFormula.RationalCliffordSpinKernel
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The Spin kernel after scalar extension from the rationals

For a `RationalQuadraticSpaceMatrix V` and a field extension `K / ℚ`, this
file applies the already generic Clifford action, determinant-parity, and
exterior Euler theorems to the matrix

`V.pairingMatrix.map (algebraMap ℚ K)`.

It constructs the fieldwise homomorphism from Spin to the corresponding
special orthogonal matrix group and proves, in positive rank and
characteristic zero,

```text
rootsOfUnity 2 K ≃*
  ker(V.scalarExtensionSpinSpecialOrthogonalRepresentation K).
```

The file also identifies the base-changed Clifford algebra with the Clifford
algebra of the coordinate scalar extension and proves the formula on vector
generators. Restricting this equivalence to Spin and proving naturality of the
Spin action remain separate. All results here concern `K`-points, not
scheme-level exactness or surjectivity on points.
-/

noncomputable section

open CliffordAlgebra MulAction
open scoped Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}
variable (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [Algebra ℚ K]
variable [Invertible (2 : K)]

def scalarExtensionFormMatrix : Matrix (Fin n) (Fin n) K :=
  V.pairingMatrix.map (algebraMap ℚ K)

omit [Invertible (2 : K)] in
theorem scalarExtensionFormMatrix_isSymm :
    (V.scalarExtensionFormMatrix K).IsSymm := by
  exact V.form_symm.map (algebraMap ℚ K)

omit [Invertible (2 : K)] in
theorem scalarExtensionFormMatrix_det_ne_zero :
    (V.scalarExtensionFormMatrix K).det ≠ 0 := by
  change (RingHom.mapMatrix (algebraMap ℚ K) V.pairingMatrix).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap ℚ K)).2 V.form_det_ne_zero

def scalarExtensionQuadraticForm : QuadraticForm K (Fin n → K) :=
  (V.scalarExtensionFormMatrix K).toQuadraticMap'

@[simp]
theorem scalarExtensionQuadraticForm_toMatrix' :
    (V.scalarExtensionQuadraticForm K).toMatrix' =
      V.scalarExtensionFormMatrix K :=
  Matrix.toMatrix'_toQuadraticMap'_of_isSymm _
    (V.scalarExtensionFormMatrix_isSymm K)

/-- The canonical coordinates on the scalar extension of the rational
coordinate module. -/
def scalarExtensionModuleEquiv :
    K ⊗[ℚ] (Fin n → ℚ) ≃ₗ[K] (Fin n → K) :=
  TensorProduct.piScalarRight ℚ K K (Fin n)

/-- The canonical coordinate equivalence identifies base change of the
rational quadratic form with the quadratic form of the mapped matrix. -/
theorem scalarExtensionModuleEquiv_isometry :
    ∀ z : K ⊗[ℚ] (Fin n → ℚ),
      V.scalarExtensionQuadraticForm K
          (scalarExtensionModuleEquiv (n := n) K z) =
        V.quadraticForm.baseChange K z := by
  intro z
  rw [← (V.scalarExtensionQuadraticForm K).associated_eq_self_apply ℕ]
  rw [← (V.quadraticForm.baseChange K).associated_eq_self_apply ℕ]
  suffices hbilin : ∀ x y : K ⊗[ℚ] (Fin n → ℚ),
      (V.scalarExtensionQuadraticForm K).associated
          (scalarExtensionModuleEquiv (n := n) K x)
          (scalarExtensionModuleEquiv (n := n) K y) =
        (V.quadraticForm.baseChange K).associated x y by
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
          change (V.scalarExtensionQuadraticForm K).associated
              (fun i => v i • a) (fun i => w i • b) = _
          change QuadraticMap.associatedHom ℕ
              (LinearMap.BilinMap.toQuadraticMap
                (Matrix.toBilin' (V.scalarExtensionFormMatrix K)))
              (fun i => v i • a) (fun i => w i • b) = _
          have hsymmK :
              (Matrix.toBilin' (V.scalarExtensionFormMatrix K)).IsSymm := by
            constructor
            intro s t
            simp only [Matrix.toBilin'_apply]
            calc
              (∑ i, ∑ j, s i * V.scalarExtensionFormMatrix K i j * t j) =
                  ∑ j, ∑ i, s i * V.scalarExtensionFormMatrix K i j * t j :=
                Finset.sum_comm
              _ = ∑ i, ∑ j, t i * V.scalarExtensionFormMatrix K i j * s j := by
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro j _
                rw [(V.scalarExtensionFormMatrix_isSymm K).apply i j]
                ring
          rw [QuadraticMap.associated_left_inverse ℕ hsymmK.1]
          change Matrix.toBilin' (V.scalarExtensionFormMatrix K)
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
          change Matrix.toBilin' (V.scalarExtensionFormMatrix K)
              (fun i => v i • a) (fun i => w i • b) =
            QuadraticMap.associatedHom ℕ V.quadraticForm v w • (a * b)
          change _ = QuadraticMap.associatedHom ℕ
            (LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' V.pairingMatrix)) v w •
              (a * b)
          rw [QuadraticMap.associated_left_inverse ℕ hsymmQ.1]
          simp only [Matrix.toBilin'_apply, scalarExtensionFormMatrix,
            Matrix.map_apply]
          simp only [Algebra.smul_def]
          change (∑ i, ∑ j,
              (algebraMap ℚ K (v i) * a) * algebraMap ℚ K (V.pairingMatrix i j) *
                (algebraMap ℚ K (w j) * b)) =
            algebraMap ℚ K (∑ i, ∑ j, v i * V.pairingMatrix i j * w j) * (a * b)
          simp_rw [map_sum, map_mul]
          have hterm (i j : Fin n) :
              (algebraMap ℚ K (v i) * a) *
                    algebraMap ℚ K (V.pairingMatrix i j) *
                  (algebraMap ℚ K (w j) * b) =
                (algebraMap ℚ K (v i) *
                    algebraMap ℚ K (V.pairingMatrix i j) *
                  algebraMap ℚ K (w j)) * (a * b) := by
            ring
          simp_rw [hterm]
          calc
            (∑ i, ∑ j,
                (algebraMap ℚ K (v i) *
                    algebraMap ℚ K (V.pairingMatrix i j) *
                  algebraMap ℚ K (w j)) * (a * b)) =
                ∑ i, (∑ j,
                  algebraMap ℚ K (v i) *
                    algebraMap ℚ K (V.pairingMatrix i j) *
                  algebraMap ℚ K (w j)) * (a * b) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
            _ = (∑ i, ∑ j,
                  algebraMap ℚ K (v i) *
                    algebraMap ℚ K (V.pairingMatrix i j) *
                  algebraMap ℚ K (w j)) * (a * b) :=
              by rw [Finset.sum_mul]

/-- The isometry between the abstract base-changed quadratic form and its
matrix-coordinate realization. -/
def scalarExtensionQuadraticIsometryEquiv :
    (V.quadraticForm.baseChange K).IsometryEquiv
      (V.scalarExtensionQuadraticForm K) where
  toLinearEquiv := scalarExtensionModuleEquiv (n := n) K
  map_app' := V.scalarExtensionModuleEquiv_isometry K

/-- The Clifford algebras of the abstract and matrix-coordinate scalar
extensions are isomorphic. -/
def scalarExtensionCliffordAlgEquiv :
    CliffordAlgebra (V.quadraticForm.baseChange K) ≃ₐ[K]
      CliffordAlgebra (V.scalarExtensionQuadraticForm K) :=
  CliffordAlgebra.equivOfIsometry
    (V.scalarExtensionQuadraticIsometryEquiv K)

/-- Base change of the rational Clifford algebra, expressed directly in the
matrix-coordinate Clifford algebra over `K`. -/
def tensorCliffordScalarExtensionEquiv :
    K ⊗[ℚ] CliffordAlgebra V.quadraticForm ≃ₐ[K]
      CliffordAlgebra (V.scalarExtensionQuadraticForm K) :=
  (CliffordAlgebra.equivBaseChange K V.quadraticForm).symm.trans
    (V.scalarExtensionCliffordAlgEquiv K)

@[simp]
theorem tensorCliffordScalarExtensionEquiv_tmul_ι
    (a : K) (v : Fin n → ℚ) :
    V.tensorCliffordScalarExtensionEquiv K
        (a ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm v) =
      CliffordAlgebra.ι (V.scalarExtensionQuadraticForm K)
        (fun i => v i • a) := by
  rw [tensorCliffordScalarExtensionEquiv, AlgEquiv.trans_apply]
  change V.scalarExtensionCliffordAlgEquiv K
      (CliffordAlgebra.ofBaseChange K V.quadraticForm
        (a ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm v)) = _
  rw [CliffordAlgebra.ofBaseChange_tmul_ι]
  change CliffordAlgebra.equivOfIsometry
      (V.scalarExtensionQuadraticIsometryEquiv K)
        (CliffordAlgebra.ι (V.quadraticForm.baseChange K) (a ⊗ₜ[ℚ] v)) = _
  rw [CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  rfl

abbrev scalarExtensionOrthogonalMatrixSubgroup :=
  PositiveDefiniteIntegralLattice.formPreservingMatrixSubgroup (V.scalarExtensionFormMatrix K)

abbrev scalarExtensionSpecialOrthogonalMatrixSubgroup :=
  PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup (V.scalarExtensionFormMatrix K)

def scalarExtensionSpinMatrixRepresentation :
    spinGroup (V.scalarExtensionQuadraticForm K) →*
      (Matrix (Fin n) (Fin n) K)ˣ :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (Fin n → K)).symm.toMonoidHom.comp
        (spinGroup.conjugationRepresentation (V.scalarExtensionQuadraticForm K)))

@[simp]
theorem scalarExtensionSpinMatrixRepresentation_val
    (x : spinGroup (V.scalarExtensionQuadraticForm K)) :
    (V.scalarExtensionSpinMatrixRepresentation K x :
        Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix'
        ((spinGroup.conjugationRepresentation
          (V.scalarExtensionQuadraticForm K) x).toLinearMap) := by
  rfl

@[simp]
theorem scalarExtensionSpinMatrixRepresentation_mulVec
    (x : spinGroup (V.scalarExtensionQuadraticForm K)) (m : Fin n → K) :
    (V.scalarExtensionSpinMatrixRepresentation K x :
        Matrix (Fin n) (Fin n) K) *ᵥ m =
      spinGroup.conjugationRepresentation
        (V.scalarExtensionQuadraticForm K) x m := by
  rw [scalarExtensionSpinMatrixRepresentation_val]
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix'
    (spinGroup.conjugationRepresentation
      (V.scalarExtensionQuadraticForm K) x).toLinearMap) m

theorem scalarExtensionSpinMatrixRepresentation_mem_orthogonal
    (x : spinGroup (V.scalarExtensionQuadraticForm K)) :
    V.scalarExtensionSpinMatrixRepresentation K x ∈
      V.scalarExtensionOrthogonalMatrixSubgroup K := by
  rw [PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff]
  rw [scalarExtensionSpinMatrixRepresentation_val,
    ← V.scalarExtensionQuadraticForm_toMatrix' K]
  rw [← QuadraticForm.toMatrix'_comp]
  have hcomp : (V.scalarExtensionQuadraticForm K).comp
      (spinGroup.conjugationRepresentation
        (V.scalarExtensionQuadraticForm K) x).toLinearMap =
      V.scalarExtensionQuadraticForm K := by
    apply QuadraticMap.ext
    intro m
    exact spinGroup.conjugationRepresentation_map_app
      (V.scalarExtensionQuadraticForm K) x m
  rw [hcomp]

def scalarExtensionSpinOrthogonalRepresentation :
    spinGroup (V.scalarExtensionQuadraticForm K) →*
      V.scalarExtensionOrthogonalMatrixSubgroup K where
  toFun x := ⟨V.scalarExtensionSpinMatrixRepresentation K x,
    V.scalarExtensionSpinMatrixRepresentation_mem_orthogonal K x⟩
  map_one' := Subtype.ext (map_one (V.scalarExtensionSpinMatrixRepresentation K))
  map_mul' x y := Subtype.ext
    (map_mul (V.scalarExtensionSpinMatrixRepresentation K) x y)

theorem scalarExtensionQuadraticForm_associated_nondegenerate :
    (V.scalarExtensionQuadraticForm K).associated.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toMatrix'_iff.mp
  change (V.scalarExtensionQuadraticForm K).toMatrix'.Nondegenerate
  rw [V.scalarExtensionQuadraticForm_toMatrix' K]
  exact Matrix.nondegenerate_iff_det_ne_zero.mpr
    (V.scalarExtensionFormMatrix_det_ne_zero K)

theorem sq_eq_one_of_scalarExtensionSpin_eq_algebraMap
    (x : spinGroup (V.scalarExtensionQuadraticForm K)) (r : K)
    (hx : (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) =
      algebraMap K (CliffordAlgebra (V.scalarExtensionQuadraticForm K)) r) :
    r ^ 2 = 1 := by
  apply (algebraMap K
    (CliffordAlgebra (V.scalarExtensionQuadraticForm K))).injective
  rw [map_pow, map_one, pow_two]
  calc
    algebraMap K (CliffordAlgebra (V.scalarExtensionQuadraticForm K)) r *
          algebraMap K (CliffordAlgebra (V.scalarExtensionQuadraticForm K)) r =
        star (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) *
          (x : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) := by
            rw [hx, CliffordAlgebra.star_algebraMap]
    _ = 1 := spinGroup.star_mul_self_of_mem x.property

theorem exists_isUnit_scalarExtensionQuadraticForm [NeZero n] :
    ∃ m : Fin n → K, IsUnit (V.scalarExtensionQuadraticForm K m) := by
  have hBne : (V.scalarExtensionQuadraticForm K).associated ≠ 0 :=
    LinearMap.BilinForm.Nondegenerate.ne_zero
      (V.scalarExtensionQuadraticForm_associated_nondegenerate K)
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    hBne ((V.scalarExtensionQuadraticForm K).associated_isSymm (S := ℕ))
  refine ⟨m, (isUnit_iff_ne_zero.mpr ?_)⟩
  rwa [← (V.scalarExtensionQuadraticForm K).associated_eq_self_apply ℕ m]

theorem neg_one_mem_scalarExtensionSpinGroup [NeZero n] :
    (-1 : CliffordAlgebra (V.scalarExtensionQuadraticForm K)) ∈
      spinGroup (V.scalarExtensionQuadraticForm K) :=
  spinGroup.neg_one_mem_of_exists_isUnit
    (V.exists_isUnit_scalarExtensionQuadraticForm K)

theorem algebraMap_mem_scalarExtensionSpinGroup_of_mem_rootsOfUnity_two
    [NeZero n] (z : rootsOfUnity 2 K) :
    algebraMap K (CliffordAlgebra (V.scalarExtensionQuadraticForm K))
        ((z : Kˣ) : K) ∈ spinGroup (V.scalarExtensionQuadraticForm K) := by
  have hz : (((z : Kˣ) : K) ^ 2) = 1 :=
    (mem_rootsOfUnity' 2 (z : Kˣ)).mp z.property
  rcases sq_eq_one_iff.mp hz with hz | hz
  · simp [hz]
  · simpa [hz] using V.neg_one_mem_scalarExtensionSpinGroup K

def scalarExtensionMuTwoToSpin [NeZero n] :
    rootsOfUnity 2 K →* spinGroup (V.scalarExtensionQuadraticForm K) where
  toFun z := ⟨algebraMap K
      (CliffordAlgebra (V.scalarExtensionQuadraticForm K)) ((z : Kˣ) : K),
    V.algebraMap_mem_scalarExtensionSpinGroup_of_mem_rootsOfUnity_two K z⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' z w := by
    apply Subtype.ext
    simp

end RationalQuadraticSpaceMatrix
