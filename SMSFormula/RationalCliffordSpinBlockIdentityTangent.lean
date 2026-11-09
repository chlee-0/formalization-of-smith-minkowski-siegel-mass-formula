import SMSFormula.RationalCliffordSpinBlockOrthogonalComplement
import SMSFormula.SkewAdjointBaseChange

/-!
# The identity tangent of the nonisotropic block stabilizer

This file differentiates the certified fixed-last-coordinate block embedding.
At the identity, adjoining a fixed coordinate means adjoining a zero tangent
coordinate: the lower skew-adjoint matrix `X` maps to `diag(X, 0)`, not to the
group-level block `diag(g, 1)`.

Over every commutative rational algebra, this zero-last block identifies the
lower skew-adjoint tangent exactly with the submodule of the enlarged
skew-adjoint tangent whose final column vanishes.  The construction commutes
with arbitrary scalar extension.  Over `Q` it also transports top forms between
the two tangent presentations.  No Haar measure, quotient integral, or local
normalization is introduced here.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Adjoin a zero final coordinate to an infinitesimal matrix. -/
def zeroLastBlockMatrix
    {R : Type*} [CommRing R]
    (X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  nonisotropicLastBlockMatrix X 0

@[simp]
theorem zeroLastBlockMatrix_castSucc_castSucc
    {R : Type*} [CommRing R]
    (X : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    zeroLastBlockMatrix X i.castSucc j.castSucc = X i j := by
  simp [zeroLastBlockMatrix]

@[simp]
theorem zeroLastBlockMatrix_castSucc_last
    {R : Type*} [CommRing R]
    (X : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    zeroLastBlockMatrix X i.castSucc (Fin.last n) = 0 := by
  simp [zeroLastBlockMatrix]

@[simp]
theorem zeroLastBlockMatrix_last_castSucc
    {R : Type*} [CommRing R]
    (X : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    zeroLastBlockMatrix X (Fin.last n) j.castSucc = 0 := by
  simp [zeroLastBlockMatrix]

@[simp]
theorem zeroLastBlockMatrix_last_last
    {R : Type*} [CommRing R]
    (X : Matrix (Fin n) (Fin n) R) :
    zeroLastBlockMatrix X (Fin.last n) (Fin.last n) = 0 := by
  simp [zeroLastBlockMatrix]

@[simp]
theorem zeroLastBlockMatrix_zero
    {R : Type*} [CommRing R] :
    zeroLastBlockMatrix (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  ext i j
  cases i using Fin.lastCases with
  | last => cases j using Fin.lastCases <;> simp
  | cast i => cases j using Fin.lastCases <;> simp

@[simp]
theorem zeroLastBlockMatrix_add
    {R : Type*} [CommRing R]
    (X Y : Matrix (Fin n) (Fin n) R) :
    zeroLastBlockMatrix (X + Y) =
      zeroLastBlockMatrix X + zeroLastBlockMatrix Y := by
  ext i j
  cases i using Fin.lastCases with
  | last => cases j using Fin.lastCases <;> simp
  | cast i => cases j using Fin.lastCases <;> simp

@[simp]
theorem zeroLastBlockMatrix_smul
    {R : Type*} [CommRing R]
    (c : R) (X : Matrix (Fin n) (Fin n) R) :
    zeroLastBlockMatrix (c • X) = c • zeroLastBlockMatrix X := by
  ext i j
  cases i using Fin.lastCases with
  | last => cases j using Fin.lastCases <;> simp
  | cast i => cases j using Fin.lastCases <;> simp

@[simp]
theorem upperLeftBlock_zeroLastBlockMatrix
    {R : Type*} [CommRing R]
    (X : Matrix (Fin n) (Fin n) R) :
    upperLeftBlock (zeroLastBlockMatrix X) = X := by
  simp [zeroLastBlockMatrix]

@[simp]
theorem zeroLastBlockMatrix_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (X : Matrix (Fin n) (Fin n) R) :
    (zeroLastBlockMatrix X).map f = zeroLastBlockMatrix (X.map f) := by
  ext i j
  cases i using Fin.lastCases with
  | last => cases j using Fin.lastCases <;> simp
  | cast i => cases j using Fin.lastCases <;> simp

@[simp]
theorem upperLeftBlock_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    upperLeftBlock (X.map f) = (upperLeftBlock X).map f := by
  ext i j
  rfl

/-- The zero-last block construction as a linear map. -/
def zeroLastBlockMatrixLinearMap
    {R : Type*} [CommRing R] :
    Matrix (Fin n) (Fin n) R →ₗ[R]
      Matrix (Fin (n + 1)) (Fin (n + 1)) R where
  toFun := zeroLastBlockMatrix
  map_add' := zeroLastBlockMatrix_add
  map_smul' := zeroLastBlockMatrix_smul

/-- The skew-adjoint equation respects the zero-last block decomposition. -/
theorem skewAdjointOperator_zeroLastBlockMatrix
    {R : Type*} [CommRing R]
    (F X : Matrix (Fin n) (Fin n) R) (a : R) :
    skewAdjointOperator (nonisotropicLastBlockMatrix F a)
        (zeroLastBlockMatrix X) =
      zeroLastBlockMatrix (skewAdjointOperator F X) := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases <;>
        simp [skewAdjointOperator, Matrix.mul_apply,
          Fin.sum_univ_castSucc]
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simp [skewAdjointOperator, Matrix.mul_apply,
            Fin.sum_univ_castSucc]
      | cast j =>
          simp [skewAdjointOperator, Matrix.mul_apply,
            Fin.sum_univ_castSucc]

/-- The fixed-last-vector tangent fiber inside the enlarged skew-adjoint
tangent.  Its defining condition is the differentiated final-column equation. -/
def nonisotropicLastSkewAdjointFiber
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Submodule A
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A)) where
  carrier := {X | ∀ i, (X : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    i (Fin.last n) = 0}
  zero_mem' := by intro i; rfl
  add_mem' := by
    intro X Y hX hY i
    change X.1 i (Fin.last n) + Y.1 i (Fin.last n) = 0
    rw [hX i, hY i, add_zero]
  smul_mem' := by
    intro c X hX i
    change c * X.1 i (Fin.last n) = 0
    rw [hX i, mul_zero]

@[simp]
theorem mem_nonisotropicLastSkewAdjointFiber
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A)) :
    X ∈ W.nonisotropicLastSkewAdjointFiber a ha A ↔
      ∀ i, (X : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
        i (Fin.last n) = 0 :=
  Iff.rfl

/-- A lower skew-adjoint tangent vector gives an enlarged one by adjoining a
zero final infinitesimal coordinate. -/
def nonisotropicLastSkewAdjointEmbed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix A) →ₗ[A]
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A) := by
  let F := W.specialOrthogonalMappedFormMatrix A
  let c := algebraMap ℚ A a
  have hform := W.nonisotropicLastExtension_mappedFormMatrix a ha A
  refine
    { toFun := fun X => ⟨zeroLastBlockMatrix X.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · rw [hform, ← mem_ker_skewAdjointOperator_iff]
    change skewAdjointOperator (nonisotropicLastBlockMatrix F c)
      (zeroLastBlockMatrix X.1) = 0
    rw [skewAdjointOperator_zeroLastBlockMatrix]
    have hX : skewAdjointOperator F X.1 = 0 :=
      LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff F X.1).mpr X.2)
    rw [hX, zeroLastBlockMatrix_zero]
  · intro X Y
    apply Subtype.ext
    exact zeroLastBlockMatrix_add X.1 Y.1
  · intro c X
    apply Subtype.ext
    exact zeroLastBlockMatrix_smul c X.1

@[simp]
theorem coe_nonisotropicLastSkewAdjointEmbed_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix A)) :
    (W.nonisotropicLastSkewAdjointEmbed a ha A X :
      Matrix (Fin (n + 1)) (Fin (n + 1)) A) =
        zeroLastBlockMatrix X.1 :=
  rfl

theorem nonisotropicLastSkewAdjointEmbed_mem_fiber
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix A)) :
    W.nonisotropicLastSkewAdjointEmbed a ha A X ∈
      W.nonisotropicLastSkewAdjointFiber a ha A := by
  intro i
  cases i using Fin.lastCases <;> simp

/-- The differentiated block embedding with codomain restricted to the exact
fixed-last-coordinate tangent fiber. -/
def nonisotropicLastSkewAdjointFiberEmbed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix A) →ₗ[A]
      W.nonisotropicLastSkewAdjointFiber a ha A :=
  (W.nonisotropicLastSkewAdjointEmbed a ha A).codRestrict _
    (W.nonisotropicLastSkewAdjointEmbed_mem_fiber a ha A)

theorem nonisotropicLastSkewAdjointFiber_finalRow
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : W.nonisotropicLastSkewAdjointFiber a ha A)
    (j : Fin (n + 1)) :
    (X.1.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
      (Fin.last n) j = 0 := by
  let F := W.specialOrthogonalMappedFormMatrix A
  let c := algebraMap ℚ A a
  let FB := nonisotropicLastBlockMatrix F c
  have hform := W.nonisotropicLastExtension_mappedFormMatrix a ha A
  have hskew : X.1.1ᵀ * FB = FB * (-X.1.1) := by
    have h := X.1.2
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at h
    change X.1.1ᵀ *
        (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A =
      (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A *
        (-X.1.1) at h
    simpa [FB, hform] using h
  have hentry := congrArg
    (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
      M (Fin.last n) j) hskew
  have hcol : ∀ i,
      (X.1.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
        i (Fin.last n) = 0 := X.2
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hentry
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hentry
  simp_rw [hcol] at hentry
  have hc_zero : c * X.1.1 (Fin.last n) j = 0 := by
    have hc_neg : c * (-X.1.1 (Fin.last n) j) = 0 := by
      simpa [FB] using hentry.symm
    simpa [mul_neg] using hc_neg
  have hc : IsUnit c :=
    (isUnit_iff_ne_zero.mpr ha).map (algebraMap ℚ A)
  apply hc.mul_left_cancel
  simpa using hc_zero

/-- The upper-left block of a fixed enlarged tangent vector is lower-rank
skew-adjoint. -/
theorem upperLeftBlock_mem_skewAdjoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : W.nonisotropicLastSkewAdjointFiber a ha A) :
    upperLeftBlock X.1.1 ∈ skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix A) := by
  let F := W.specialOrthogonalMappedFormMatrix A
  let c := algebraMap ℚ A a
  let FB := nonisotropicLastBlockMatrix F c
  have hform := W.nonisotropicLastExtension_mappedFormMatrix a ha A
  have hskew : skewAdjointOperator FB X.1.1 = 0 := by
    apply LinearMap.mem_ker.mp
    rw [mem_ker_skewAdjointOperator_iff]
    simpa [FB, hform] using X.1.2
  rw [← mem_ker_skewAdjointOperator_iff, LinearMap.mem_ker]
  ext i j
  have hentry := congrArg
    (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
      M i.castSucc j.castSucc) hskew
  simpa [FB, F, skewAdjointOperator, upperLeftBlock,
    Matrix.mul_apply, Fin.sum_univ_castSucc] using hentry

/-- Extract the lower tangent vector from the fixed enlarged tangent fiber. -/
def nonisotropicLastSkewAdjointFiberExtract
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.nonisotropicLastSkewAdjointFiber a ha A →ₗ[A]
      skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix A) where
  toFun X := ⟨upperLeftBlock X.1.1,
    W.upperLeftBlock_mem_skewAdjoint a ha A X⟩
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    rfl
  map_smul' c X := by
    apply Subtype.ext
    ext i j
    rfl

@[simp]
theorem nonisotropicLastSkewAdjointFiberExtract_embed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix A)) :
    W.nonisotropicLastSkewAdjointFiberExtract a ha A
        (W.nonisotropicLastSkewAdjointFiberEmbed a ha A X) = X := by
  apply Subtype.ext
  exact upperLeftBlock_zeroLastBlockMatrix X.1

theorem nonisotropicLastSkewAdjointFiber_eq_zeroLastBlock
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : W.nonisotropicLastSkewAdjointFiber a ha A) :
    X.1.1 = zeroLastBlockMatrix (upperLeftBlock X.1.1) := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => simp [W.nonisotropicLastSkewAdjointFiber_finalRow a ha A X]
      | cast j => simp [W.nonisotropicLastSkewAdjointFiber_finalRow a ha A X]
  | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using X.2 i.castSucc
      | cast j => simp [upperLeftBlock]

@[simp]
theorem nonisotropicLastSkewAdjointFiberEmbed_extract
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : W.nonisotropicLastSkewAdjointFiber a ha A) :
    W.nonisotropicLastSkewAdjointFiberEmbed a ha A
        (W.nonisotropicLastSkewAdjointFiberExtract a ha A X) = X := by
  apply Subtype.ext
  apply Subtype.ext
  exact (W.nonisotropicLastSkewAdjointFiber_eq_zeroLastBlock a ha A X).symm

/-- Exact tangent equivalence induced by the complement stabilizer embedding. -/
def nonisotropicLastSkewAdjointFiberEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    skewAdjointMatricesLieSubalgebra
        (W.specialOrthogonalMappedFormMatrix A) ≃ₗ[A]
      W.nonisotropicLastSkewAdjointFiber a ha A where
  toLinearMap := W.nonisotropicLastSkewAdjointFiberEmbed a ha A
  invFun := W.nonisotropicLastSkewAdjointFiberExtract a ha A
  left_inv := W.nonisotropicLastSkewAdjointFiberExtract_embed a ha A
  right_inv := W.nonisotropicLastSkewAdjointFiberEmbed_extract a ha A

/-- Scalar extension commutes with the tangent block embedding in ambient
matrix coordinates. -/
theorem nonisotropicLastSkewAdjointEmbed_map
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (X : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix A)) :
    ((W.nonisotropicLastSkewAdjointEmbed a ha A X :
        Matrix (Fin (n + 1)) (Fin (n + 1)) A).map f) =
      zeroLastBlockMatrix ((X : Matrix (Fin n) (Fin n) A).map f) := by
  rw [coe_nonisotropicLastSkewAdjointEmbed_apply]
  simpa using zeroLastBlockMatrix_map (n := n) f.toRingHom X.1

/-- Over `Q`, the fixed tangent fiber has the same dimension as the lower
skew-adjoint tangent. -/
theorem nonisotropicLastSkewAdjointFiber_finrank_eq
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Module.finrank ℚ (W.nonisotropicLastSkewAdjointFiber a ha ℚ) =
      Module.finrank ℚ W.skewAdjointTangent :=
  LinearEquiv.finrank_eq (W.nonisotropicLastSkewAdjointFiberEquiv a ha ℚ).symm

/-- Transport rational top forms from the lower tangent to the exact
fixed-last-coordinate tangent fiber. -/
noncomputable def nonisotropicLastSkewAdjointFiberTopFormEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    (W.skewAdjointTangent
        [⋀^Fin (Module.finrank ℚ W.skewAdjointTangent)]→ₗ[ℚ] ℚ) ≃ₗ[ℚ]
      ((W.nonisotropicLastSkewAdjointFiber a ha ℚ)
        [⋀^Fin (Module.finrank ℚ
          (W.nonisotropicLastSkewAdjointFiber a ha ℚ))]→ₗ[ℚ] ℚ) :=
  (AlternatingMap.domLCongr ℚ ℚ
      (Fin (Module.finrank ℚ W.skewAdjointTangent)) ℚ
      (W.nonisotropicLastSkewAdjointFiberEquiv a ha ℚ)).trans
    (AlternatingMap.domDomCongrₗ ℚ
      (Equiv.cast (congrArg Fin
        (W.nonisotropicLastSkewAdjointFiber_finrank_eq a ha).symm)))

/-- The lower-rank invariant determinant form transported to the exact
fixed-last-coordinate tangent fiber.  This is the rational differential to be
compared placewise in the subsequent stabilizer-measure transport. -/
noncomputable def nonisotropicLastSkewAdjointFiberInvariantTopDifferential
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    (W.nonisotropicLastSkewAdjointFiber a ha ℚ)
      [⋀^Fin (Module.finrank ℚ
        (W.nonisotropicLastSkewAdjointFiber a ha ℚ))]→ₗ[ℚ] ℚ :=
  W.nonisotropicLastSkewAdjointFiberTopFormEquiv a ha
    W.invariantTopDifferential

/-- The transported stabilizer differential is nonzero. -/
theorem nonisotropicLastSkewAdjointFiberInvariantTopDifferential_ne_zero
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.nonisotropicLastSkewAdjointFiberInvariantTopDifferential a ha ≠ 0 := by
  exact (not_congr
    (W.nonisotropicLastSkewAdjointFiberTopFormEquiv a ha).map_eq_zero_iff).2
      W.invariantTopDifferential_ne_zero

end RationalQuadraticSpaceMatrix
