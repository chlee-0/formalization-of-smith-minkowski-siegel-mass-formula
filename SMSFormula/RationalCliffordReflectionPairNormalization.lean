import SMSFormula.RationalQuadraticFppfRootCover
import SMSFormula.RationalCliffordSpinCandidatePointData
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.Reflection

/-!
# Reflection-pair normalization over a quadratic fppf cover

This file gives the first explicit local lifting primitive for the affine
Clifford Spin candidate.  Over a commutative ring, a product of two Clifford
vectors acts as the composition of the two associated quadratic reflections.
After adjoining a square root of `(Q v * Q w)⁻¹`, scaling that even product
makes its Clifford norm one.

For the rational quadratic space stored by `RationalQuadraticSpaceMatrix`,
the normalized product is transported through Clifford base change.  When
`v` and `w` are rational vectors of unit quadratic value, it supplies an
actual point of the affine Spin candidate over the quadratic root cover.  Its
matrix coordinates are the scalar extension of the literal two-reflection
matrix, whose determinant is one.

This is a local two-reflection lift.  It does not prove that arbitrary
special-orthogonal points are fppf-locally products of such pairs; that still
requires a quadratic Cartan--Dieudonne or standard-open generation theorem.
-/

noncomputable section

open CliffordAlgebra
open scoped Matrix TensorProduct

namespace Matrix

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_toMatrix'_reflection_of_apply_eq_two
    (a : ι → R) (f : Module.Dual R (ι → R)) (hf : f a = 2) :
    (LinearMap.toMatrix' (LinearMap.id - f.smulRight a)).det = -1 := by
  let row : ι → R := fun j => f (Pi.single j 1)
  have hrank : LinearMap.toMatrix' (f.smulRight a) =
      Matrix.replicateCol Unit a * Matrix.replicateRow Unit row := by
    ext i j
    simp [row, LinearMap.toMatrix'_apply, Matrix.mul_apply, mul_comm]
  have hrow : ∑ j, row j * a j = f a := by
    have hsingle (j : ι) :
        f (Pi.single j (a j)) = row j * a j := by
      rw [show Pi.single j (a j) =
          a j • (Pi.single j (1 : R) : ι → R) by
        ext i
        simp [Pi.single_apply]]
      simp [row, mul_comm]
    calc
      ∑ j, row j * a j = ∑ j, f (Pi.single j (a j)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hsingle j).symm
      _ = f (∑ j, Pi.single j (a j)) := by rw [map_sum]
      _ = f a := by
        congr 1
        ext i
        simp [Pi.single_apply]
  rw [map_sub, LinearMap.toMatrix'_id, hrank,
    Matrix.det_one_sub_mul_comm, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, if_true]
  rw [hrow, hf]
  ring

end Matrix

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

def normalizedReflectionPair (s : R) (v w : M) : CliffordAlgebra Q :=
  s • (ι Q v * ι Q w)

theorem reverse_normalizedReflectionPair (s : R) (v w : M) :
    reverse (normalizedReflectionPair Q s v w) =
      s • (ι Q w * ι Q v) := by
  simp [normalizedReflectionPair, reverse.map_mul]

theorem involute_normalizedReflectionPair (s : R) (v w : M) :
    involute (normalizedReflectionPair Q s v w) =
      normalizedReflectionPair Q s v w := by
  simp [normalizedReflectionPair]

theorem normalizedReflectionPair_mul_reverse (s : R) (v w : M) :
    normalizedReflectionPair Q s v w *
        reverse (normalizedReflectionPair Q s v w) =
      algebraMap R (CliffordAlgebra Q) (s ^ 2 * Q v * Q w) := by
  rw [reverse_normalizedReflectionPair]
  simp only [normalizedReflectionPair]
  rw [smul_mul_smul]
  rw [show (ι Q v * ι Q w) * (ι Q w * ι Q v) =
      ι Q v * (ι Q w * ι Q w) * ι Q v by noncomm_ring]
  rw [ι_sq_scalar]
  rw [show ι Q v * algebraMap R (CliffordAlgebra Q) (Q w) * ι Q v =
      Q w • (ι Q v * ι Q v) by
    rw [Algebra.smul_def, Algebra.commutes]
    rw [← Algebra.commutes (Q w) (ι Q v)]
    rw [← Algebra.commutes (Q w) (ι Q v * ι Q v)]
    rw [mul_assoc]]
  rw [ι_sq_scalar, smul_smul]
  simp only [Algebra.smul_def, ← map_mul]
  congr 1
  ring

theorem normalizedReflectionPair_mul_reverse_eq_one
    (s : R) (v w : M) (h : s ^ 2 * Q v * Q w = 1) :
    normalizedReflectionPair Q s v w *
        reverse (normalizedReflectionPair Q s v w) = 1 := by
  rw [normalizedReflectionPair_mul_reverse, h, map_one]

def reflectionPairVector (s : R) (v w m : M) : M :=
  s ^ 2 •
    (QuadraticMap.polar Q v
          (QuadraticMap.polar Q w m • w - Q w • m) • v -
      Q v • (QuadraticMap.polar Q w m • w - Q w • m))

theorem normalizedReflectionPair_conjugation (s : R) (v w m : M) :
    normalizedReflectionPair Q s v w * ι Q m *
        reverse (normalizedReflectionPair Q s v w) =
      ι Q (reflectionPairVector Q s v w m) := by
  rw [reverse_normalizedReflectionPair]
  simp only [normalizedReflectionPair]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [show (ι Q v * ι Q w) * ι Q m * (ι Q w * ι Q v) =
      ι Q v * (ι Q w * ι Q m * ι Q w) * ι Q v by noncomm_ring]
  rw [ι_mul_ι_mul_ι, ι_mul_ι_mul_ι]
  rw [← map_smul]
  simp [reflectionPairVector, pow_two]

def quadraticReflectionDual (v : M) [Invertible (Q v)] : Module.Dual R M :=
  ⅟(Q v) • Q.polarBilin v

theorem quadraticReflectionDual_apply_self (v : M) [Invertible (Q v)] :
    quadraticReflectionDual Q v v = 2 := by
  simp [quadraticReflectionDual, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, smul_eq_mul]
  calc
    ⅟(Q v) * (2 * Q v) = 2 * (⅟(Q v) * Q v) := by ring
    _ = 2 := by rw [invOf_mul_self, mul_one]

def quadraticReflection (v : M) [Invertible (Q v)] : M ≃ₗ[R] M :=
  Module.reflection (quadraticReflectionDual_apply_self Q v)

theorem quadraticReflection_apply (v m : M) [Invertible (Q v)] :
    quadraticReflection Q v m =
      m - (⅟(Q v) * QuadraticMap.polar Q v m) • v := by
  rw [quadraticReflection, Module.reflection_apply]
  simp [quadraticReflectionDual, QuadraticMap.polarBilin_apply_apply,
    smul_eq_mul]

theorem quadraticReflection_map_app (v m : M) [Invertible (Q v)] :
    Q (quadraticReflection Q v m) = Q m := by
  rw [quadraticReflection_apply]
  let a := ⅟(Q v) * QuadraticMap.polar Q v m
  change Q (m - a • v) = Q m
  rw [sub_eq_add_neg, ← neg_smul]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul]
  simp only [neg_mul, neg_smul, QuadraticMap.polar_neg_right,
    QuadraticMap.polar_smul_right, smul_eq_mul]
  rw [QuadraticMap.polar_comm Q m v]
  have hv : ⅟(Q v) * Q v = 1 := invOf_mul_self (Q v)
  dsimp only [a]
  have hquadratic :
      ⅟(Q v) ^ 2 * (QuadraticMap.polar Q v m) ^ 2 * Q v =
        ⅟(Q v) * (QuadraticMap.polar Q v m) ^ 2 := by
    calc
      ⅟(Q v) ^ 2 * (QuadraticMap.polar Q v m) ^ 2 * Q v =
          (⅟(Q v) * Q v) *
            (⅟(Q v) * (QuadraticMap.polar Q v m) ^ 2) := by ring
      _ = _ := by rw [hv, one_mul]
  ring_nf
  rw [hquadratic]
  ring

theorem quadraticReflection_toMatrix'_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R (ι → R)) (v : ι → R)
    [Invertible (Q v)] :
    (LinearMap.toMatrix' (quadraticReflection Q v).toLinearMap).det = -1 := by
  change (LinearMap.toMatrix'
    (LinearMap.id - (quadraticReflectionDual Q v).smulRight v)).det = -1
  exact Matrix.det_toMatrix'_reflection_of_apply_eq_two v
    (quadraticReflectionDual Q v) (quadraticReflectionDual_apply_self Q v)

def quadraticReflectionPair (v w : M)
    [Invertible (Q v)] [Invertible (Q w)] : M ≃ₗ[R] M :=
  (quadraticReflection Q w).trans (quadraticReflection Q v)

@[simp]
theorem quadraticReflectionPair_apply (v w m : M)
    [Invertible (Q v)] [Invertible (Q w)] :
    quadraticReflectionPair Q v w m =
      quadraticReflection Q v (quadraticReflection Q w m) :=
  rfl

theorem quadraticReflectionPair_map_app (v w m : M)
    [Invertible (Q v)] [Invertible (Q w)] :
    Q (quadraticReflectionPair Q v w m) = Q m := by
  rw [quadraticReflectionPair_apply, quadraticReflection_map_app,
    quadraticReflection_map_app]

theorem quadraticReflectionPair_toMatrix'_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R (ι → R)) (v w : ι → R)
    [Invertible (Q v)] [Invertible (Q w)] :
    (LinearMap.toMatrix'
      (quadraticReflectionPair Q v w).toLinearMap).det = 1 := by
  rw [show (quadraticReflectionPair Q v w).toLinearMap =
      (quadraticReflection Q v).toLinearMap ∘ₗ
        (quadraticReflection Q w).toLinearMap by rfl]
  rw [LinearMap.toMatrix'_comp, Matrix.det_mul,
    quadraticReflection_toMatrix'_det,
    quadraticReflection_toMatrix'_det]
  ring

theorem reflectionPairVector_eq_reflections
    (s : R) (v w m : M) [Invertible (Q v)] [Invertible (Q w)]
    (h : s ^ 2 * Q v * Q w = 1) :
    reflectionPairVector Q s v w m =
      quadraticReflection Q v (quadraticReflection Q w m) := by
  have hs : s ^ 2 = ⅟(Q v) * ⅟(Q w) := by
    calc
      s ^ 2 = s ^ 2 * (Q v * ⅟(Q v)) * (Q w * ⅟(Q w)) := by
        rw [mul_invOf_self, mul_invOf_self, mul_one, mul_one]
      _ = (s ^ 2 * Q v * Q w) * (⅟(Q v) * ⅟(Q w)) := by ring
      _ = ⅟(Q v) * ⅟(Q w) := by rw [h, one_mul]
  have hp₁ : QuadraticMap.polar Q v
        (QuadraticMap.polar Q w m • w - Q w • m) =
      QuadraticMap.polar Q w m * QuadraticMap.polar Q v w -
        Q w * QuadraticMap.polar Q v m := by
    change Q.polarBilin v
        (QuadraticMap.polar Q w m • w - Q w • m) = _
    simp [QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  have hp₂ : QuadraticMap.polar Q v
        (m - (⅟(Q w) * QuadraticMap.polar Q w m) • w) =
      QuadraticMap.polar Q v m -
        (⅟(Q w) * QuadraticMap.polar Q w m) *
          QuadraticMap.polar Q v w := by
    change Q.polarBilin v
        (m - (⅟(Q w) * QuadraticMap.polar Q w m) • w) = _
    simp [QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  rw [reflectionPairVector, quadraticReflection_apply,
    quadraticReflection_apply, hs, hp₁, hp₂]
  have hv : ⅟(Q v) * Q v = 1 := invOf_mul_self (Q v)
  have hw : ⅟(Q w) * Q w = 1 := invOf_mul_self (Q w)
  match_scalars
  · simp only [mul_one]
    linear_combination -(⅟(Q v) * QuadraticMap.polar Q v m) * hw
  · simp only [mul_one]
    linear_combination -(⅟(Q w) * QuadraticMap.polar Q w m) * hv
  · simp only [mul_one]
    ring_nf
    calc
      ⅟(Q v) * ⅟(Q w) * Q v * Q w =
          (⅟(Q v) * Q v) * (⅟(Q w) * Q w) := by ring
      _ = 1 := by rw [hv, hw, one_mul]

section RootCover

variable [Invertible (2 : R)]
variable (v w : M) [Invertible (Q v)] [Invertible (Q w)]

abbrev ReflectionPairRootAlgebra :=
  RationalTamagawa.QuadraticRootAlgebra R (⅟(Q v) * ⅟(Q w))

def reflectionPairRoot : ReflectionPairRootAlgebra Q v w :=
  AdjoinRoot.root
    (RationalTamagawa.quadraticRootPolynomial R (⅟(Q v) * ⅟(Q w)))

def reflectionPairBaseVector (m : M) :
    ReflectionPairRootAlgebra Q v w ⊗[R] M :=
  1 ⊗ₜ[R] m

def reflectionPairBaseVectorInvertible (m : M) [Invertible (Q m)] :
    Invertible
      ((Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairBaseVector Q v w m)) :=
  Invertible.copy
    (Invertible.map
      (algebraMap R (ReflectionPairRootAlgebra Q v w)) (Q m)) _
    (by
      simp [reflectionPairBaseVector, QuadraticForm.baseChange_tmul,
        Algebra.smul_def])

attribute [local instance] reflectionPairBaseVectorInvertible

theorem polar_baseChange_reflectionPairBaseVector (m₁ m₂ : M) :
    QuadraticMap.polar
        (Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairBaseVector Q v w m₁)
        (reflectionPairBaseVector Q v w m₂) =
      algebraMap R (ReflectionPairRootAlgebra Q v w)
        (QuadraticMap.polar Q m₁ m₂) := by
  simp only [QuadraticMap.polar, reflectionPairBaseVector,
    ← TensorProduct.tmul_add, QuadraticForm.baseChange_tmul,
    Algebra.smul_def, mul_one, map_sub]

theorem quadraticReflection_baseChange_reflectionPairBaseVector
    (m₁ m₂ : M) [Invertible (Q m₁)] :
    quadraticReflection
        (Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairBaseVector Q v w m₁)
        (reflectionPairBaseVector Q v w m₂) =
      reflectionPairBaseVector Q v w (quadraticReflection Q m₁ m₂) := by
  rw [quadraticReflection_apply, quadraticReflection_apply]
  rw [polar_baseChange_reflectionPairBaseVector]
  letI : Invertible
      (algebraMap R (ReflectionPairRootAlgebra Q v w) (Q m₁)) :=
    Invertible.map
      (algebraMap R (ReflectionPairRootAlgebra Q v w)) (Q m₁)
  have hinv :
      ⅟((Q.baseChange (ReflectionPairRootAlgebra Q v w))
          (reflectionPairBaseVector Q v w m₁)) =
        algebraMap R (ReflectionPairRootAlgebra Q v w) ⅟(Q m₁) := by
    exact (map_invOf
      (algebraMap R (ReflectionPairRootAlgebra Q v w)) (Q m₁)).symm
  rw [hinv]
  simp only [reflectionPairBaseVector, ← map_mul]
  rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  congr 1
  change (algebraMap R (ReflectionPairRootAlgebra Q v w)
      (⅟(Q m₁) * QuadraticMap.polar Q m₁ m₂)) •
        (1 ⊗ₜ[R] m₁) =
      (⅟(Q m₁) * QuadraticMap.polar Q m₁ m₂) •
        (1 ⊗ₜ[R] m₁)
  exact IsScalarTower.algebraMap_smul
    (ReflectionPairRootAlgebra Q v w)
    (⅟(Q m₁) * QuadraticMap.polar Q m₁ m₂) (1 ⊗ₜ[R] m₁)

theorem reflectionPairRoot_normalizes :
    reflectionPairRoot Q v w ^ 2 *
          (Q.baseChange (ReflectionPairRootAlgebra Q v w))
            (reflectionPairBaseVector Q v w v) *
        (Q.baseChange (ReflectionPairRootAlgebra Q v w))
          (reflectionPairBaseVector Q v w w) = 1 := by
  rw [reflectionPairRoot, RationalTamagawa.quadraticRootAlgebra_root_sq]
  simp only [reflectionPairBaseVector, QuadraticForm.baseChange_tmul,
    one_mul, Algebra.smul_def]
  simp only [mul_one, ← map_mul]
  have hscalar :
    (⅟(Q v) * ⅟(Q w)) * Q v * Q w =
        1 := by
    calc
      (⅟(Q v) * ⅟(Q w)) * Q v * Q w =
          (⅟(Q v) * Q v) * (⅟(Q w) * Q w) := by ring
      _ = 1 := by rw [invOf_mul_self, invOf_mul_self, one_mul]
  rw [hscalar, map_one]

def rootNormalizedReflectionPair :
    CliffordAlgebra
      (Q.baseChange (ReflectionPairRootAlgebra Q v w)) :=
  normalizedReflectionPair
    (Q.baseChange (ReflectionPairRootAlgebra Q v w))
    (reflectionPairRoot Q v w)
    (reflectionPairBaseVector Q v w v)
    (reflectionPairBaseVector Q v w w)

theorem rootNormalizedReflectionPair_involute :
    involute (rootNormalizedReflectionPair Q v w) =
      rootNormalizedReflectionPair Q v w := by
  exact involute_normalizedReflectionPair _ _ _ _

theorem rootNormalizedReflectionPair_mul_reverse :
    rootNormalizedReflectionPair Q v w *
        reverse (rootNormalizedReflectionPair Q v w) = 1 := by
  exact normalizedReflectionPair_mul_reverse_eq_one _ _ _ _
    (reflectionPairRoot_normalizes Q v w)

theorem rootNormalizedReflectionPair_conjugation (m : M) :
    rootNormalizedReflectionPair Q v w *
          ι (Q.baseChange (ReflectionPairRootAlgebra Q v w))
            (reflectionPairBaseVector Q v w m) *
        reverse (rootNormalizedReflectionPair Q v w) =
      ι (Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairVector
          (Q.baseChange (ReflectionPairRootAlgebra Q v w))
          (reflectionPairRoot Q v w)
          (reflectionPairBaseVector Q v w v)
          (reflectionPairBaseVector Q v w w)
          (reflectionPairBaseVector Q v w m)) := by
  exact normalizedReflectionPair_conjugation _ _ _ _ _

theorem rootReflectionPairVector_eq_reflections (m : M) :
    reflectionPairVector
        (Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairRoot Q v w)
        (reflectionPairBaseVector Q v w v)
        (reflectionPairBaseVector Q v w w)
        (reflectionPairBaseVector Q v w m) =
      quadraticReflection
        (Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairBaseVector Q v w v)
        (quadraticReflection
          (Q.baseChange (ReflectionPairRootAlgebra Q v w))
          (reflectionPairBaseVector Q v w w)
          (reflectionPairBaseVector Q v w m)) := by
  exact reflectionPairVector_eq_reflections _ _ _ _ _
    (reflectionPairRoot_normalizes Q v w)

theorem rootReflectionPairVector_eq_baseVector (m : M) :
    reflectionPairVector
        (Q.baseChange (ReflectionPairRootAlgebra Q v w))
        (reflectionPairRoot Q v w)
        (reflectionPairBaseVector Q v w v)
        (reflectionPairBaseVector Q v w w)
        (reflectionPairBaseVector Q v w m) =
      reflectionPairBaseVector Q v w
        (quadraticReflectionPair Q v w m) := by
  rw [rootReflectionPairVector_eq_reflections,
    quadraticReflection_baseChange_reflectionPairBaseVector,
    quadraticReflection_baseChange_reflectionPairBaseVector]
  rfl

end RootCover

end CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (v w : Fin n → ℚ)
variable [Invertible (V.quadraticForm v)] [Invertible (V.quadraticForm w)]

def reflectionPairMatrix : Matrix (Fin n) (Fin n) ℚ :=
  LinearMap.toMatrix'
    (CliffordAlgebra.quadraticReflectionPair
      V.quadraticForm v w).toLinearMap

def reflectionPairSpecialOrthogonalMatrixPoint :
    V.specialOrthogonalMatrixPoint ℚ := by
  let e := CliffordAlgebra.quadraticReflectionPair V.quadraticForm v w
  refine ⟨V.reflectionPairMatrix v w, ?_, ?_⟩
  · have hcomp : V.quadraticForm.comp e.toLinearMap = V.quadraticForm := by
      apply QuadraticMap.ext
      intro m
      exact CliffordAlgebra.quadraticReflectionPair_map_app
        V.quadraticForm v w m
    have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
    rw [QuadraticForm.toMatrix'_comp, V.quadraticForm_toMatrix'] at hmatrix
    simpa [reflectionPairMatrix, e, specialOrthogonalMappedFormMatrix]
      using hmatrix
  · exact CliffordAlgebra.quadraticReflectionPair_toMatrix'_det
      V.quadraticForm v w

theorem quadraticReflectionPair_single_eq_sum_matrix (i : Fin n) :
    CliffordAlgebra.quadraticReflectionPair V.quadraticForm v w
        (Pi.single i (1 : ℚ) : Fin n → ℚ) =
      ∑ j, V.reflectionPairMatrix v w j i •
        (Pi.single j (1 : ℚ) : Fin n → ℚ) := by
  let e := CliffordAlgebra.quadraticReflectionPair V.quadraticForm v w
  have h := LinearMap.congr_fun
    (Matrix.toLin'_toMatrix' e.toLinearMap) (Pi.single i 1)
  ext k
  have hk := congrFun h k
  convert hk.symm using 1
  simp [reflectionPairMatrix, e, Pi.single_apply]

theorem ι_quadraticReflectionPair_single_eq_sum_matrix (i : Fin n) :
    CliffordAlgebra.ι V.quadraticForm
        (CliffordAlgebra.quadraticReflectionPair V.quadraticForm v w
          (Pi.single i 1)) =
      ∑ j, V.reflectionPairMatrix v w j i •
        CliffordAlgebra.ι V.quadraticForm
          (Pi.single j (1 : ℚ) : Fin n → ℚ) := by
  rw [V.quadraticReflectionPair_single_eq_sum_matrix v w i, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_smul (CliffordAlgebra.ι V.quadraticForm)
    (V.reflectionPairMatrix v w j i)
    (Pi.single j (1 : ℚ) : Fin n → ℚ)

abbrev reflectionPairRootAlgebra :=
  CliffordAlgebra.ReflectionPairRootAlgebra V.quadraticForm v w

def reflectionPairRootSpecialOrthogonalMatrixPoint :
    V.specialOrthogonalMatrixPoint (V.reflectionPairRootAlgebra v w) := by
  let P := V.reflectionPairSpecialOrthogonalMatrixPoint v w
  let f := algebraMap ℚ (V.reflectionPairRootAlgebra v w)
  refine ⟨P.1.map f, ?_, ?_⟩
  · have hP : P.1.transpose * V.pairingMatrix * P.1 = V.pairingMatrix := by
      simpa [specialOrthogonalMappedFormMatrix] using P.2.1
    change (P.1.map f).transpose *
        V.pairingMatrix.map f * P.1.map f = V.pairingMatrix.map f
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      hP]
  · change (f.mapMatrix P.1).det = 1
    rw [← RingHom.map_det, P.2.2, map_one]

@[simp]
theorem reflectionPairRootSpecialOrthogonalMatrixPoint_apply (i j : Fin n) :
    (V.reflectionPairRootSpecialOrthogonalMatrixPoint v w).1 i j =
      algebraMap ℚ (V.reflectionPairRootAlgebra v w)
        (V.reflectionPairMatrix v w i j) :=
  rfl

def reflectionPairRootClifford :
    V.cliffordCoordinateBaseChangeAlgebra
      (V.reflectionPairRootAlgebra v w) :=
  CliffordAlgebra.toBaseChange (V.reflectionPairRootAlgebra v w)
    V.quadraticForm
    (CliffordAlgebra.rootNormalizedReflectionPair V.quadraticForm v w)

theorem reflectionPairRootClifford_involute :
    V.cliffordCoordinateBaseChangeInvolute
        (V.reflectionPairRootAlgebra v w)
        (V.reflectionPairRootClifford v w) =
      V.reflectionPairRootClifford v w := by
  change (TensorProduct.map LinearMap.id
      CliffordAlgebra.involute.toLinearMap)
      (CliffordAlgebra.toBaseChange (V.reflectionPairRootAlgebra v w)
        V.quadraticForm
        (CliffordAlgebra.rootNormalizedReflectionPair
          V.quadraticForm v w)) = _
  rw [← CliffordAlgebra.toBaseChange_involute,
    CliffordAlgebra.rootNormalizedReflectionPair_involute]
  rfl

theorem reflectionPairRootClifford_reverse :
    V.cliffordCoordinateBaseChangeReverse
        (V.reflectionPairRootAlgebra v w)
        (V.reflectionPairRootClifford v w) =
      CliffordAlgebra.toBaseChange (V.reflectionPairRootAlgebra v w)
        V.quadraticForm
        (CliffordAlgebra.reverse
          (CliffordAlgebra.rootNormalizedReflectionPair
            V.quadraticForm v w)) := by
  exact (CliffordAlgebra.toBaseChange_reverse
    (V.reflectionPairRootAlgebra v w) V.quadraticForm
    (CliffordAlgebra.rootNormalizedReflectionPair
      V.quadraticForm v w)).symm

theorem reflectionPairRootClifford_mul_reverse :
    V.reflectionPairRootClifford v w *
        V.cliffordCoordinateBaseChangeReverse
          (V.reflectionPairRootAlgebra v w)
          (V.reflectionPairRootClifford v w) = 1 := by
  rw [reflectionPairRootClifford_reverse]
  rw [reflectionPairRootClifford]
  rw [← map_mul,
    CliffordAlgebra.rootNormalizedReflectionPair_mul_reverse, map_one]

theorem reflectionPairRootClifford_conjugation (m : Fin n → ℚ) :
    V.reflectionPairRootClifford v w *
          Algebra.TensorProduct.includeRight
            (CliffordAlgebra.ι V.quadraticForm m) *
        V.cliffordCoordinateBaseChangeReverse
          (V.reflectionPairRootAlgebra v w)
          (V.reflectionPairRootClifford v w) =
      Algebra.TensorProduct.includeRight
        (CliffordAlgebra.ι V.quadraticForm
          (CliffordAlgebra.quadraticReflectionPair
            V.quadraticForm v w m)) := by
  rw [reflectionPairRootClifford_reverse, reflectionPairRootClifford]
  change CliffordAlgebra.toBaseChange (V.reflectionPairRootAlgebra v w)
        V.quadraticForm
        (CliffordAlgebra.rootNormalizedReflectionPair
          V.quadraticForm v w) *
      (1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm m) *
      CliffordAlgebra.toBaseChange (V.reflectionPairRootAlgebra v w)
        V.quadraticForm
        (CliffordAlgebra.reverse
          (CliffordAlgebra.rootNormalizedReflectionPair
            V.quadraticForm v w)) =
    1 ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm
      (CliffordAlgebra.quadraticReflectionPair V.quadraticForm v w m)
  rw [← CliffordAlgebra.toBaseChange_ι
    (V.reflectionPairRootAlgebra v w) V.quadraticForm 1 m]
  rw [← map_mul, ← map_mul]
  have h := congrArg
    (CliffordAlgebra.toBaseChange (V.reflectionPairRootAlgebra v w)
      V.quadraticForm)
    (CliffordAlgebra.rootNormalizedReflectionPair_conjugation
      V.quadraticForm v w m)
  rw [CliffordAlgebra.rootReflectionPairVector_eq_baseVector] at h
  simpa [CliffordAlgebra.reflectionPairBaseVector] using h

theorem reflectionPairRootClifford_vectorGraph (i : Fin n) :
    V.reflectionPairRootClifford v w *
          V.cliffordCoordinateBaseChangeVector
            (V.reflectionPairRootAlgebra v w) i *
        V.cliffordCoordinateBaseChangeReverse
          (V.reflectionPairRootAlgebra v w)
          (V.reflectionPairRootClifford v w) =
      ∑ j,
        (V.reflectionPairRootSpecialOrthogonalMatrixPoint v w).1 j i •
          V.cliffordCoordinateBaseChangeVector
            (V.reflectionPairRootAlgebra v w) j := by
  rw [show V.cliffordCoordinateBaseChangeVector
      (V.reflectionPairRootAlgebra v w) i =
        Algebra.TensorProduct.includeRight
          (CliffordAlgebra.ι V.quadraticForm
            (Pi.single i (1 : ℚ) : Fin n → ℚ)) by rfl]
  rw [V.reflectionPairRootClifford_conjugation v w]
  have h := congrArg
    (Algebra.TensorProduct.includeRight :
      CliffordAlgebra V.quadraticForm →ₐ[ℚ]
        V.cliffordCoordinateBaseChangeAlgebra
          (V.reflectionPairRootAlgebra v w))
    (V.ι_quadraticReflectionPair_single_eq_sum_matrix v w i)
  rw [map_sum] at h
  simpa only [map_smul,
    V.reflectionPairRootSpecialOrthogonalMatrixPoint_apply,
    IsScalarTower.algebraMap_smul,
    cliffordCoordinateBaseChangeVector,
    cliffordCoordinateBaseChangeOfRational] using h

def reflectionPairRootCandidatePointData :
    V.CliffordSpinCandidatePointData
      (V.reflectionPairRootAlgebra v w) where
  clifford := V.reflectionPairRootClifford v w
  matrixPoint := V.reflectionPairRootSpecialOrthogonalMatrixPoint v w
  involute_eq := V.reflectionPairRootClifford_involute v w
  mul_reverse_eq_one := V.reflectionPairRootClifford_mul_reverse v w
  vectorGraph := V.reflectionPairRootClifford_vectorGraph v w

def reflectionPairRootCandidatePoint :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.reflectionPairRootAlgebra v w :=
  V.cliffordSpinCandidateCoordinateAlgHomOfPointData
    (V.reflectionPairRootAlgebra v w)
    (V.reflectionPairRootCandidatePointData v w)

@[simp]
theorem reflectionPairRootCandidatePoint_matrixCoordinate (i j : Fin n) :
    V.reflectionPairRootCandidatePoint v w
        (V.cliffordSpinCandidateMatrixCoordinate i j) =
      algebraMap ℚ (V.reflectionPairRootAlgebra v w)
        (V.reflectionPairMatrix v w i j) := by
  rw [reflectionPairRootCandidatePoint,
    V.cliffordSpinCandidateCoordinateAlgHomOfPointData_matrixCoordinate]
  exact V.reflectionPairRootSpecialOrthogonalMatrixPoint_apply v w i j

end RationalQuadraticSpaceMatrix
