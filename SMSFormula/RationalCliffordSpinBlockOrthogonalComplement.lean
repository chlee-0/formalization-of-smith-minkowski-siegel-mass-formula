import SMSFormula.RationalSpecialOrthogonalGroupScheme

/-!
# The block orthogonal-complement stabilizer

This file supplies the first algebraic layer of the high-rank Spin-volume
induction.  Starting from a rational quadratic carrier `W`, it adjoins one
nonisotropic final coordinate.  Over every commutative rational algebra, the
special-orthogonal transformations of the enlarged carrier that fix that
coordinate are exactly the block embeddings of `SO(W)`.

The statement is intrinsic to the existing matrix carriers and is compatible
with arbitrary scalar extension.  It does not identify the corresponding
Spin or general-Spin stabilizers, and it introduces no Haar measure, cutoff,
or Fourier input.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Adjoin a final one-dimensional block to a square matrix. -/
def nonisotropicLastBlockMatrix
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks F 0 0 (fun _ _ : Fin 1 => a))

@[simp]
theorem nonisotropicLastBlockMatrix_castSucc_castSucc
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) (i j : Fin n) :
    nonisotropicLastBlockMatrix F a i.castSucc j.castSucc = F i j := by
  simp [nonisotropicLastBlockMatrix, Matrix.reindex_apply, Matrix.fromBlocks]

@[simp]
theorem nonisotropicLastBlockMatrix_castSucc_last
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) (i : Fin n) :
    nonisotropicLastBlockMatrix F a i.castSucc (Fin.last n) = 0 := by
  simp [nonisotropicLastBlockMatrix, Matrix.reindex_apply, Matrix.fromBlocks]

@[simp]
theorem nonisotropicLastBlockMatrix_last_castSucc
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) (j : Fin n) :
    nonisotropicLastBlockMatrix F a (Fin.last n) j.castSucc = 0 := by
  simp [nonisotropicLastBlockMatrix, Matrix.reindex_apply, Matrix.fromBlocks]

@[simp]
theorem nonisotropicLastBlockMatrix_last_last
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) :
    nonisotropicLastBlockMatrix F a (Fin.last n) (Fin.last n) = a := by
  simp [nonisotropicLastBlockMatrix, Matrix.reindex_apply, Matrix.fromBlocks]

theorem nonisotropicLastBlockMatrix_det
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) :
    (nonisotropicLastBlockMatrix F a).det = F.det * a := by
  rw [nonisotropicLastBlockMatrix, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁]
  simp

theorem nonisotropicLastBlockMatrix_isSymm
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) (hF : F.IsSymm) :
    (nonisotropicLastBlockMatrix F a).IsSymm := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases <;> simp
  | cast i =>
      cases j using Fin.lastCases with
      | last => simp
      | cast j => simpa using hF.apply i j

/-- The rational quadratic carrier obtained by adjoining a nonisotropic final
line of value `a`. -/
def nonisotropicLastExtension
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    RationalQuadraticSpaceMatrix (n + 1) where
  pairingMatrix := nonisotropicLastBlockMatrix W.pairingMatrix a
  form_symm := nonisotropicLastBlockMatrix_isSymm _ _ W.form_symm
  form_det_ne_zero := by
    rw [nonisotropicLastBlockMatrix_det]
    exact mul_ne_zero W.form_det_ne_zero ha

@[simp]
theorem nonisotropicLastExtension_pairingMatrix
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    (W.nonisotropicLastExtension a ha).pairingMatrix =
      nonisotropicLastBlockMatrix W.pairingMatrix a :=
  rfl

@[simp]
theorem nonisotropicLastExtension_mappedFormMatrix
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A =
      nonisotropicLastBlockMatrix
        (W.specialOrthogonalMappedFormMatrix A) (algebraMap ℚ A a) := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases <;>
        simp [specialOrthogonalMappedFormMatrix]
  | cast i =>
      cases j using Fin.lastCases <;>
        simp [specialOrthogonalMappedFormMatrix]

/-- The standard final coordinate vector. -/
def lastCoordinateVector {R : Type*} [Zero R] [One R] :
    Fin (n + 1) → R :=
  Pi.single (Fin.last n) 1

/-- A matrix fixes the final coordinate vector exactly when its final column
is the standard final coordinate. -/
def FixesLastCoordinate
    {R : Type*} [CommRing R]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Prop :=
  M *ᵥ lastCoordinateVector = lastCoordinateVector

theorem fixesLastCoordinate_iff_column
    {R : Type*} [CommRing R]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    FixesLastCoordinate M ↔
      ∀ i, M i (Fin.last n) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i (Fin.last n) := by
  constructor
  · intro h i
    have hi := congrFun h i
    simpa [FixesLastCoordinate, lastCoordinateVector, Matrix.mulVec,
      dotProduct, Pi.single_apply, Matrix.one_apply] using hi
  · intro h
    funext i
    simpa [FixesLastCoordinate, lastCoordinateVector, Matrix.mulVec,
      dotProduct, Pi.single_apply, Matrix.one_apply] using h i

/-- Upper-left block obtained after deleting the final coordinate. -/
def upperLeftBlock
    {R : Type*} [CommRing R]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  M.submatrix Fin.castSucc Fin.castSucc

@[simp]
theorem upperLeftBlock_nonisotropicLastBlockMatrix
    {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (a : R) :
    upperLeftBlock (nonisotropicLastBlockMatrix F a) = F := by
  ext i j
  simp [upperLeftBlock]

/-- Adjoin a fixed final coordinate to a matrix. -/
def fixLastBlockMatrix
    {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  nonisotropicLastBlockMatrix M 1

@[simp]
theorem upperLeftBlock_fixLastBlockMatrix
    {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    upperLeftBlock (fixLastBlockMatrix M) = M := by
  ext i j
  simp [upperLeftBlock, fixLastBlockMatrix]

@[simp]
theorem fixLastBlockMatrix_one
    {R : Type*} [CommRing R] :
    fixLastBlockMatrix (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => simp [fixLastBlockMatrix]
      | cast j =>
          simp [fixLastBlockMatrix,
            (Fin.castSucc_ne_last j).symm]
  | cast i =>
      cases j using Fin.lastCases <;> simp [fixLastBlockMatrix, Matrix.one_apply]

@[simp]
theorem fixLastBlockMatrix_mul
    {R : Type*} [CommRing R]
    (M N : Matrix (Fin n) (Fin n) R) :
    fixLastBlockMatrix (M * N) =
      fixLastBlockMatrix M * fixLastBlockMatrix N := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases <;>
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc] <;>
        simp [fixLastBlockMatrix]
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp [fixLastBlockMatrix]
      | cast j =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp [fixLastBlockMatrix, Matrix.mul_apply]

theorem fixLastBlockMatrix_det
    {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    (fixLastBlockMatrix M).det = M.det := by
  simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_det]

theorem fixLastBlockMatrix_transpose_mul_nonisotropicLastBlockMatrix_mul
    {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R)
    (F : Matrix (Fin n) (Fin n) R) (a : R) :
    (fixLastBlockMatrix M)ᵀ * nonisotropicLastBlockMatrix F a *
        fixLastBlockMatrix M =
      nonisotropicLastBlockMatrix (Mᵀ * F * M) a := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          simp [Matrix.mul_apply, Fin.sum_univ_castSucc,
            fixLastBlockMatrix]
      | cast j =>
          simp [Matrix.mul_apply, Fin.sum_univ_castSucc,
            fixLastBlockMatrix]
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simp [Matrix.mul_apply, Fin.sum_univ_castSucc,
            fixLastBlockMatrix]
      | cast j =>
          simp [Matrix.mul_apply, Fin.sum_univ_castSucc,
            fixLastBlockMatrix]

/-- The fixed-vector fiber in the enlarged special-orthogonal group. -/
def nonisotropicLastCoordinateFiber
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A) :=
  {g | FixesLastCoordinate g.1.1.1}

theorem nonisotropicLastCoordinateFiber_finalRow
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A)
    (hg : g ∈ W.nonisotropicLastCoordinateFiber a ha A)
    (j : Fin (n + 1)) :
    g.1.1.1 (Fin.last n) j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (Fin.last n) j := by
  let F := W.specialOrthogonalMappedFormMatrix A
  let c : A := algebraMap ℚ A a
  let FB := nonisotropicLastBlockMatrix F c
  have hform : g.1.1.1ᵀ * FB * g.1.1.1 = FB := by
    have hgform :=
      (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff _ g.1.1).mp
        g.1.2
    simpa [FB, F, c] using hgform
  have hcol : ∀ i, g.1.1.1 i (Fin.last n) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i (Fin.last n) :=
    (fixesLastCoordinate_iff_column g.1.1.1).1 hg
  have hleft (k : Fin (n + 1)) :
      (g.1.1.1ᵀ * FB) (Fin.last n) k = FB (Fin.last n) k := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply, hcol]
    simp [Matrix.one_apply]
  have hentry := congrArg
    (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
      M (Fin.last n) j) hform
  change (g.1.1.1ᵀ * FB * g.1.1.1) (Fin.last n) j =
    FB (Fin.last n) j at hentry
  rw [Matrix.mul_apply] at hentry
  simp_rw [hleft] at hentry
  rw [Fin.sum_univ_castSucc] at hentry
  have hc : IsUnit c := by
    exact (isUnit_iff_ne_zero.mpr ha).map (algebraMap ℚ A)
  apply hc.mul_left_cancel
  cases j using Fin.lastCases with
  | last => simpa [FB, c, Matrix.one_apply] using hentry
  | cast j =>
      simpa [FB, c, Matrix.one_apply,
        (Fin.castSucc_ne_last j).symm] using hentry

theorem nonisotropicLastCoordinateFiber_eq_fixLastBlockMatrix
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A)
    (hg : g ∈ W.nonisotropicLastCoordinateFiber a ha A) :
    g.1.1.1 = fixLastBlockMatrix (upperLeftBlock g.1.1.1) := by
  have hcol := (fixesLastCoordinate_iff_column g.1.1.1).1 hg
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          rw [W.nonisotropicLastCoordinateFiber_finalRow a ha A g hg]
          simp [fixLastBlockMatrix]
      | cast j =>
          rw [W.nonisotropicLastCoordinateFiber_finalRow a ha A g hg]
          simp [fixLastBlockMatrix,
            (Fin.castSucc_ne_last j).symm]
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [hcol]
          simp [fixLastBlockMatrix]
      | cast j => simp [upperLeftBlock, fixLastBlockMatrix]

theorem upperLeftBlock_preserves_form
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A)
    (hg : g ∈ W.nonisotropicLastCoordinateFiber a ha A) :
    (upperLeftBlock g.1.1.1)ᵀ * W.specialOrthogonalMappedFormMatrix A *
        upperLeftBlock g.1.1.1 = W.specialOrthogonalMappedFormMatrix A := by
  let M := upperLeftBlock g.1.1.1
  have hform :=
    (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff _ g.1.1).mp
      g.1.2
  have hFB := W.nonisotropicLastExtension_mappedFormMatrix a ha A
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) A := g.1.1.1
  have hform' : g.1.1.1ᵀ *
        nonisotropicLastBlockMatrix (W.specialOrthogonalMappedFormMatrix A)
          (algebraMap ℚ A a) * g.1.1.1 =
      nonisotropicLastBlockMatrix (W.specialOrthogonalMappedFormMatrix A)
        (algebraMap ℚ A a) := by
    calc
      g.1.1.1ᵀ *
            nonisotropicLastBlockMatrix (W.specialOrthogonalMappedFormMatrix A)
              (algebraMap ℚ A a) * g.1.1.1 =
          g.1.1.1ᵀ *
            (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A *
              g.1.1.1 := by
        change Gᵀ * nonisotropicLastBlockMatrix
            (W.specialOrthogonalMappedFormMatrix A) (algebraMap ℚ A a) * G =
          Gᵀ *
            (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A * G
        exact congrArg (fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
          Gᵀ * X * G) hFB.symm
      _ = (W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A :=
        hform
      _ = nonisotropicLastBlockMatrix
          (W.specialOrthogonalMappedFormMatrix A) (algebraMap ℚ A a) := hFB
  rw [W.nonisotropicLastCoordinateFiber_eq_fixLastBlockMatrix a ha A g hg,
    fixLastBlockMatrix_transpose_mul_nonisotropicLastBlockMatrix_mul] at hform'
  simpa only [upperLeftBlock_nonisotropicLastBlockMatrix] using
    congrArg upperLeftBlock hform'

theorem upperLeftBlock_det
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A)
    (hg : g ∈ W.nonisotropicLastCoordinateFiber a ha A) :
    (upperLeftBlock g.1.1.1).det = 1 := by
  calc
    (upperLeftBlock g.1.1.1).det =
        (fixLastBlockMatrix (upperLeftBlock g.1.1.1)).det :=
      (fixLastBlockMatrix_det _).symm
    _ = g.1.1.1.det := congrArg Matrix.det
      (W.nonisotropicLastCoordinateFiber_eq_fixLastBlockMatrix a ha A g hg).symm
    _ = 1 :=
      (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff _ g.1).mp g.2

/-- Extract the lower-rank special-orthogonal point from the fixed-vector
fiber. -/
def nonisotropicLastCoordinateFiberExtract
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A}) :
    W.specialOrthogonalMatrixGroup A := by
  let M := upperLeftBlock g.1.1.1.1
  let Mpoint : W.specialOrthogonalMatrixPoint A :=
    ⟨M, W.upperLeftBlock_preserves_form a ha A g.1 g.2,
      W.upperLeftBlock_det a ha A g.1 g.2⟩
  exact W.specialOrthogonalMatrixPointToGroup A Mpoint

@[simp]
theorem coe_nonisotropicLastCoordinateFiberExtract
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A}) :
    (W.nonisotropicLastCoordinateFiberExtract a ha A g).1.1.1 =
      upperLeftBlock g.1.1.1.1 :=
  rfl

/-- Embed a lower-rank special-orthogonal point by adjoining a fixed final
coordinate. -/
def nonisotropicLastCoordinateFiberEmbedGroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (h : W.specialOrthogonalMatrixGroup A) :
    (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A := by
  let M := fixLastBlockMatrix h.1.1.1
  have hsmall : h.1.1.1ᵀ * W.specialOrthogonalMappedFormMatrix A *
      h.1.1.1 = W.specialOrthogonalMappedFormMatrix A :=
    (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff _ h.1.1).mp h.1.2
  let Mpoint :
      (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPoint A :=
    ⟨M, by
      rw [W.nonisotropicLastExtension_mappedFormMatrix a ha]
      simpa [M, hsmall] using
        fixLastBlockMatrix_transpose_mul_nonisotropicLastBlockMatrix_mul
          h.1.1.1 (W.specialOrthogonalMappedFormMatrix A) (algebraMap ℚ A a),
      by simpa [M, fixLastBlockMatrix_det] using
        (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff _ h.1).mp h.2⟩
  exact (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixPointToGroup A Mpoint

@[simp]
theorem coe_nonisotropicLastCoordinateFiberEmbedGroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (h : W.specialOrthogonalMatrixGroup A) :
    (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h).1.1.1 =
      fixLastBlockMatrix h.1.1.1 :=
  rfl

theorem nonisotropicLastCoordinateFiberEmbedGroup_mem
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (h : W.specialOrthogonalMatrixGroup A) :
    W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h ∈
      W.nonisotropicLastCoordinateFiber a ha A := by
  change FixesLastCoordinate
    (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h).1.1.1
  rw [fixesLastCoordinate_iff_column]
  intro i
  cases i using Fin.lastCases with
  | last => simp [fixLastBlockMatrix]
  | cast i => simp [fixLastBlockMatrix]

def nonisotropicLastCoordinateFiberEmbed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (h : W.specialOrthogonalMatrixGroup A) :
    {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A} :=
  ⟨W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h,
    W.nonisotropicLastCoordinateFiberEmbedGroup_mem a ha A h⟩

theorem nonisotropicLastCoordinateFiberExtract_embed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (h : W.specialOrthogonalMatrixGroup A) :
    W.nonisotropicLastCoordinateFiberExtract a ha A
      (W.nonisotropicLastCoordinateFiberEmbed a ha A h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact upperLeftBlock_fixLastBlockMatrix h.1.1.1

theorem nonisotropicLastCoordinateFiberEmbed_extract
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
      g ∈ W.nonisotropicLastCoordinateFiber a ha A}) :
    W.nonisotropicLastCoordinateFiberEmbed a ha A
      (W.nonisotropicLastCoordinateFiberExtract a ha A g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact (W.nonisotropicLastCoordinateFiber_eq_fixLastBlockMatrix
    a ha A g.1 g.2).symm

/-- Over every commutative rational algebra, the lower-rank special-
orthogonal carrier is equivalent to the fixed-vector fiber in the block
extension. -/
def nonisotropicLastCoordinateFiberEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.specialOrthogonalMatrixGroup A ≃
      {g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A //
        g ∈ W.nonisotropicLastCoordinateFiber a ha A} where
  toFun := W.nonisotropicLastCoordinateFiberEmbed a ha A
  invFun := W.nonisotropicLastCoordinateFiberExtract a ha A
  left_inv := W.nonisotropicLastCoordinateFiberExtract_embed a ha A
  right_inv := W.nonisotropicLastCoordinateFiberEmbed_extract a ha A

/-- The fixed-vector block embedding is multiplicative. -/
def nonisotropicLastCoordinateFiberEmbedHom
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.specialOrthogonalMatrixGroup A →*
      (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A where
  toFun := W.nonisotropicLastCoordinateFiberEmbedGroup a ha A
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' h k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp

theorem nonisotropicLastCoordinateFiberEmbedHom_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective (W.nonisotropicLastCoordinateFiberEmbedHom a ha A) := by
  intro h k hhk
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmatrix := congrArg
    (fun g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A =>
      upperLeftBlock g.1.1.1) hhk
  change upperLeftBlock (fixLastBlockMatrix h.1.1.1) =
    upperLeftBlock (fixLastBlockMatrix k.1.1.1) at hmatrix
  simpa using hmatrix

/-- The block-embedded complement group as a subgroup of the enlarged
special-orthogonal group. -/
def nonisotropicLastCoordinateStabilizerSubgroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A) :=
  (W.nonisotropicLastCoordinateFiberEmbedHom a ha A).range

theorem mem_nonisotropicLastCoordinateStabilizerSubgroup_iff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A) :
    g ∈ W.nonisotropicLastCoordinateStabilizerSubgroup a ha A ↔
      g ∈ W.nonisotropicLastCoordinateFiber a ha A := by
  constructor
  · rintro ⟨h, rfl⟩
    exact W.nonisotropicLastCoordinateFiberEmbedGroup_mem a ha A h
  · intro hg
    refine ⟨W.nonisotropicLastCoordinateFiberExtract a ha A ⟨g, hg⟩, ?_⟩
    exact congrArg Subtype.val
      (W.nonisotropicLastCoordinateFiberEmbed_extract a ha A ⟨g, hg⟩)

/-- The exact multiplicative block-stabilizer equivalence. -/
def nonisotropicLastCoordinateStabilizerMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.specialOrthogonalMatrixGroup A ≃*
      W.nonisotropicLastCoordinateStabilizerSubgroup a ha A :=
  MonoidHom.ofInjective
    (f := W.nonisotropicLastCoordinateFiberEmbedHom a ha A)
    (W.nonisotropicLastCoordinateFiberEmbedHom_injective a ha A)

@[simp]
theorem fixLastBlockMatrix_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    (fixLastBlockMatrix M).map f = fixLastBlockMatrix (M.map f) := by
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases <;> simp [fixLastBlockMatrix]
  | cast i =>
      cases j using Fin.lastCases <;> simp [fixLastBlockMatrix]

/-- The block embedding commutes with every scalar extension of commutative
rational algebras. -/
theorem nonisotropicLastCoordinateFiberEmbedGroup_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (h : W.specialOrthogonalMatrixGroup A) :
    (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupMap f
        (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h) =
      W.nonisotropicLastCoordinateFiberEmbedGroup a ha B
        (W.specialOrthogonalMatrixGroupMap f h) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [specialOrthogonalMatrixGroupMap_apply_matrix,
    coe_nonisotropicLastCoordinateFiberEmbedGroup,
    coe_nonisotropicLastCoordinateFiberEmbedGroup,
    specialOrthogonalMatrixGroupMap_apply_matrix, fixLastBlockMatrix_map]

end RationalQuadraticSpaceMatrix
