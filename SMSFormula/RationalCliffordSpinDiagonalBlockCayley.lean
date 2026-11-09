import SMSFormula.RationalCliffordSpinDiagonalBlockGroup
import SMSFormula.BlockCayleyCoordinates

/-!
# Clifford--Cayley points of the block Spin groups

Over a field `K ⊇ ℚ`, every norm-one quaternion coordinate vector `c` of the diagonal ternary space
`T` gives the intrinsic Spin point with Clifford element `h₀ + h₁e₀e₁ + h₂e₀e₂ + h₃e₁e₂`; its
special-orthogonal matrix is the upper-left block of the explicit conjugation matrix `M(c, c)`,
and the block point `Φ(c, c')` has matrix `M(c, c')`.  The represented point map to `SO` reads off
the intrinsic matrix.  Nothing is chosen.
-/

noncomputable section

open CliffordAlgebra Matrix PositiveDefiniteIntegralLattice
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

attribute [local instance] rationalAlgebraInvertibleTwo

/-- The represented point map to `SO` reads off the intrinsic matrix. -/
theorem cliffordSpinCandidateGroupToSpecialOrthogonal_coe_eq_intrinsic {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (A : Type*) [CommRing A] [Algebra ℚ A] (F : V.CliffordSpinCandidateGroup A) :
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal A F).1.1.1 =
      (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A F).matrixPoint.1 := by
  change (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).matrixGroup.1.1.1 = _
  rw [CliffordSpinCandidatePointData.matrixGroup_coe]
  congr 1
  symm
  apply CliffordSpinIntrinsicPoint.matrixPoint_eq
  intro i
  rw [cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_apply_coe]
  exact (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A F).vectorGraph i

section Ternary

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (A : Type*) [CommRing A] [Algebra ℚ A]

local notation "QT" => commutativeScalarExtensionQuadraticForm T A

omit [Algebra ℚ A] in
theorem ternary_evenElem_mem_even [Algebra ℚ A] (c : Fin 4 → A) :
    OrthogonalTriple.evenElem QT (stdVec 3 A) c ∈ even QT := by
  rw [← CliffordAlgebra.mem_evenOdd_zero_iff_mem_even]
  unfold OrthogonalTriple.evenElem
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact SetLike.algebraMap_mem_graded _ _
  all_goals exact Submodule.smul_mem _ _ (ι_mul_ι_mem_evenOdd_zero QT _ _)

include hT in
theorem ternary_evenElem_mul_reverse {c : Fin 4 → A} (hc : diagonalBlockNorm f A c = 1) :
    OrthogonalTriple.evenElem QT (stdVec 3 A) c * reverse (OrthogonalTriple.evenElem QT (stdVec 3 A) c) = 1 := by
  rw [OrthogonalTriple.evenElem_mul_reverse QT _ (T.diagonalBlock_orthoT hT A), T.diagonalBlock_evenNorm hT A, hc,
    map_one]

/-- The ternary Spin point with norm-one quaternion coordinates `c`. -/
def diagonalBlockTernaryPoint {c : Fin 4 → A} (hc : diagonalBlockNorm f A c = 1) : T.CliffordSpinIntrinsicPoint A :=
  ⟨(T.commutativeTensorCliffordEquiv A).symm (OrthogonalTriple.evenElem QT (stdVec 3 A) c),
    T.isCliffordSpinIntrinsicPoint_symm_of_even hT hδ A (T.ternary_evenElem_mem_even A c)
      (T.ternary_evenElem_mul_reverse hT A hc)⟩

@[simp]
theorem commutativeTensorCliffordEquiv_diagonalBlockTernaryPoint {c : Fin 4 → A}
    (hc : diagonalBlockNorm f A c = 1) :
    T.commutativeTensorCliffordEquiv A (T.diagonalBlockTernaryPoint hT hδ A hc).1 =
      OrthogonalTriple.evenElem QT (stdVec 3 A) c :=
  AlgEquiv.apply_symm_apply _ _

/-- The block point `Φ(c, c')` has the explicit conjugation matrix `M(c, c')`. -/
theorem diagonalBlockSpinMulEquiv_ternaryPoint_matrixPoint {c c' : Fin 4 → A}
    (hc : diagonalBlockNorm f A c = 1) (hc' : diagonalBlockNorm f A c' = 1) :
    (T.diagonalBlockSpinMulEquiv hT hδ A
        (T.diagonalBlockTernaryPoint hT hδ A hc, T.diagonalBlockTernaryPoint hT hδ A hc')).matrixPoint.1 =
      diagonalBlockConjMatrix f A c c' := by
  have h := CliffordSpinIntrinsicPoint.matrixPoint_eq _ A
    (T.diagonalBlockSpinMulEquiv hT hδ A
      (T.diagonalBlockTernaryPoint hT hδ A hc, T.diagonalBlockTernaryPoint hT hδ A hc'))
    ⟨diagonalBlockConjMatrix f A c c', T.diagonalBlockConjMatrix_mem hT hδ A hc hc'⟩ (by
      intro i
      rw [diagonalBlockSpinMulEquiv_apply_coe, commutativeTensorCliffordEquiv_diagonalBlockTernaryPoint,
        commutativeTensorCliffordEquiv_diagonalBlockTernaryPoint]
      exact T.diagonalBlock_vectorGraph hT hδ A c c' i)
  rw [h]

/-- The ternary point has the upper-left block of `M(c, c)` as matrix. -/
theorem diagonalBlockTernaryPoint_matrixPoint {c : Fin 4 → A} (hc : diagonalBlockNorm f A c = 1) :
    (T.diagonalBlockTernaryPoint hT hδ A hc).matrixPoint.1 = upperLeftBlock (diagonalBlockConjMatrix f A c c) := by
  let x := T.diagonalBlockTernaryPoint hT hδ A hc
  have hz : T.nonisotropicLastComplementSpinPoint (f 0 * f 1 * f 2) hδ A x =
      T.diagonalBlockSpinMulEquiv hT hδ A (x, x) := by
    apply CliffordSpinIntrinsicPoint.ext
    apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A).injective
    rw [nonisotropicLastComplementSpinPoint_coe,
      commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
      diagonalBlockSpinMulEquiv_apply_coe, commutativeTensorCliffordEquiv_diagonalBlockPointClifford,
      T.diagonalBlockClifford_self hδ A]
  have hm := congrArg (fun z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A ↦
    z.matrixPoint.1) hz
  simp only [nonisotropicLastComplementSpinPoint_matrixPoint, nonisotropicLastComplementSpinMatrixPoint_coe] at hm
  rw [T.diagonalBlockSpinMulEquiv_ternaryPoint_matrixPoint hT hδ A hc hc] at hm
  rw [← hm, upperLeftBlock_fixLastBlockMatrix]

include T hT hδ in
theorem diagonalBlockConjMatrix_self_eq_fixLast {c : Fin 4 → A} (hc : diagonalBlockNorm f A c = 1) :
    diagonalBlockConjMatrix f A c c = fixLastBlockMatrix (upperLeftBlock (diagonalBlockConjMatrix f A c c)) := by
  let x := T.diagonalBlockTernaryPoint hT hδ A hc
  have hz : T.nonisotropicLastComplementSpinPoint (f 0 * f 1 * f 2) hδ A x =
      T.diagonalBlockSpinMulEquiv hT hδ A (x, x) := by
    apply CliffordSpinIntrinsicPoint.ext
    apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).commutativeTensorCliffordEquiv A).injective
    rw [nonisotropicLastComplementSpinPoint_coe,
      commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap,
      diagonalBlockSpinMulEquiv_apply_coe, commutativeTensorCliffordEquiv_diagonalBlockPointClifford,
      T.diagonalBlockClifford_self hδ A]
  have hm := congrArg (fun z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinIntrinsicPoint A ↦
    z.matrixPoint.1) hz
  simp only [nonisotropicLastComplementSpinPoint_matrixPoint, nonisotropicLastComplementSpinMatrixPoint_coe] at hm
  rw [T.diagonalBlockSpinMulEquiv_ternaryPoint_matrixPoint hT hδ A hc hc] at hm
  rw [← T.diagonalBlockTernaryPoint_matrixPoint hT hδ A hc, hm]

end Ternary

/-! ## Clifford--Cayley points over a field -/

section Cayley

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (K : Type*) [Field K] [Algebra ℚ K]

/-- The pure quaternion norm in the weights `fᵢ`. -/
abbrev blockPureNorm (f : Fin 3 → ℚ) (K : Type*) [Field K] [Algebra ℚ K] (u : Fin 3 → K) : K :=
  BlockConjugationCoordinates.pureNorm (algebraMap ℚ K (f 0)) (algebraMap ℚ K (f 1)) (algebraMap ℚ K (f 2)) u

/-- The quaternion coordinates of `κ(u) = (1 + u)(1 − u)⁻¹`. -/
abbrev blockCayleyCoords (f : Fin 3 → ℚ) (K : Type*) [Field K] [Algebra ℚ K] (u : Fin 3 → K) : Fin 4 → K :=
  BlockConjugationCoordinates.cayleyCoords (algebraMap ℚ K (f 0)) (algebraMap ℚ K (f 1)) (algebraMap ℚ K (f 2)) u

theorem blockCayleyCoords_norm {u : Fin 3 → K} (hu : 1 + blockPureNorm f K u ≠ 0) :
    diagonalBlockNorm f K (blockCayleyCoords f K u) = 1 := by
  have hq : ∀ (s : K) (c : Fin 4 → K), diagonalBlockNorm f K (s • c) = s ^ 2 * diagonalBlockNorm f K c := by
    intro s c
    simp only [diagonalBlockNorm, BlockConjugationCoordinates.qnorm, Pi.smul_apply, smul_eq_mul]
    ring
  have hn : diagonalBlockNorm f K (BlockConjugationCoordinates.cayleyNum (algebraMap ℚ K (f 0))
      (algebraMap ℚ K (f 1)) (algebraMap ℚ K (f 2)) u) = (1 + blockPureNorm f K u) ^ 2 := by
    simp only [diagonalBlockNorm, BlockConjugationCoordinates.qnorm, BlockConjugationCoordinates.cayleyNum,
      blockPureNorm, BlockConjugationCoordinates.pureNorm, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [blockCayleyCoords, BlockConjugationCoordinates.cayleyCoords, hq, hn, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hu)]

/-- The Cayley coordinate `X(u, v)` in the weights `fᵢ`. -/
abbrev blockCayleyX (f : Fin 3 → ℚ) (K : Type*) [Field K] [Algebra ℚ K] (u v : Fin 3 → K) :
    Matrix (Fin 4) (Fin 4) K :=
  BlockConjugationCoordinates.blockCayleyInverse (algebraMap ℚ K (f 0)) (algebraMap ℚ K (f 1))
    (algebraMap ℚ K (f 2)) u v

include hδ in
theorem diagonalBlockConjMatrix_cayley_mul {u v : Fin 3 → K} (hu : 1 + blockPureNorm f K u ≠ 0)
    (hv : 1 + blockPureNorm f K v ≠ 0) (huv : 1 - blockPureNorm f K u * blockPureNorm f K v ≠ 0) :
    diagonalBlockConjMatrix f K (blockCayleyCoords f K u) (blockCayleyCoords f K v) * (1 - blockCayleyX f K u v) =
      1 + blockCayleyX f K u v := by
  have h0 : algebraMap ℚ K (f 0) ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 0)
  have h1 : algebraMap ℚ K (f 1) ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 1)
  have h2 : algebraMap ℚ K (f 2) ≠ 0 := (map_ne_zero _).2 (diagonalBlock_f_ne_zero hδ 2)
  have hconj : diagonalBlockConjMatrix f K = BlockConjugationCoordinates.conjMatrix (algebraMap ℚ K (f 0))
      (algebraMap ℚ K (f 1)) (algebraMap ℚ K (f 2)) (algebraMap ℚ K (f 0))⁻¹ (algebraMap ℚ K (f 1))⁻¹
      (algebraMap ℚ K (f 2))⁻¹ (algebraMap ℚ K (f 0) * algebraMap ℚ K (f 1) * algebraMap ℚ K (f 2))⁻¹ := by
    funext h k
    simp only [diagonalBlockConjMatrix, diagonalBlockScalar, map_inv₀, map_mul]
  rw [hconj]
  exact BlockConjugationCoordinates.conjMatrix_cayleyCoords_mul _ _ _ h0 h1 h2 hu hv huv

/-- A matrix Cayley identity determines the inverse Cayley value. -/
theorem cayleyInverse_eq_of_mul {m : ℕ} {M X : Matrix (Fin m) (Fin m) K} (h : M * (1 - X) = 1 + X)
    (hX : IsUnit (1 - X).det) : (M + 1)⁻¹ * (M - 1) = X := by
  have hM : M = (1 + X) * (1 - X)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
  have hM1 : M + 1 = ((1 + X) + (1 - X)) * (1 - X)⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_nonsing_inv _ hX, ← hM]
  have h2 : (1 + X) + (1 - X) = (2 : K) • (1 : Matrix (Fin m) (Fin m) K) := by
    rw [two_smul]; abel
  rw [h2, Matrix.smul_mul, Matrix.one_mul] at hM1
  have hMX : M - 1 = (M + 1) * X := by
    calc M - 1 = M * (1 - X) + M * X - 1 := by rw [Matrix.mul_sub, Matrix.mul_one]; abel
      _ = (1 + X) + M * X - 1 := by rw [h]
      _ = (M + 1) * X := by rw [Matrix.add_mul, Matrix.one_mul]; abel
  have hu : IsUnit (M + 1).det := by
    rw [hM1, Matrix.det_smul]
    refine (IsUnit.mul (IsUnit.pow _ ?_) (Matrix.isUnit_nonsing_inv_det _ hX))
    exact isUnit_iff_ne_zero.2 (two_ne_zero' K)
  rw [hMX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- A matrix Cayley identity determines the inverse Cayley value when `M + 1` is invertible. -/
theorem cayleyInverse_eq_of_mul' {m : ℕ} {M X : Matrix (Fin m) (Fin m) K} (h : M * (1 - X) = 1 + X)
    (hM : IsUnit (M + 1).det) : (M + 1)⁻¹ * (M - 1) = X := by
  have hMX : M - 1 = (M + 1) * X := by
    calc M - 1 = M * (1 - X) + M * X - 1 := by rw [Matrix.mul_sub, Matrix.mul_one]; abel
      _ = (1 + X) + M * X - 1 := by rw [h]
      _ = (M + 1) * X := by rw [Matrix.add_mul, Matrix.one_mul]; abel
  rw [hMX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

end Cayley

/-! ## Block structure on the diagonal -/

section BlockStructure

variable {K : Type*} [CommRing K]

theorem upperLeftBlock_fixLastBlockMatrix_mul {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    upperLeftBlock (fixLastBlockMatrix M * B) = M * upperLeftBlock B := by
  ext i j
  simp only [upperLeftBlock, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
    fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_castSucc, nonisotropicLastBlockMatrix_castSucc_last,
    zero_mul, add_zero]

theorem upperLeftBlock_one {m : ℕ} : upperLeftBlock (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
  ext i j
  simp [upperLeftBlock, Matrix.one_apply, Fin.castSucc_inj]

theorem upperLeftBlock_add {m : ℕ} (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    upperLeftBlock (A + B) = upperLeftBlock A + upperLeftBlock B := rfl

theorem upperLeftBlock_sub {m : ℕ} (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    upperLeftBlock (A - B) = upperLeftBlock A - upperLeftBlock B := rfl

end BlockStructure


/-! ## The ternary Cayley coordinate -/

section TernaryCayley

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (K : Type*) [Field K] [Algebra ℚ K]

/-- The ternary Cayley coordinate `X_T(u) = X(u, u)` restricted to `T`. -/
abbrev ternaryCayleyX (f : Fin 3 → ℚ) (K : Type*) [Field K] [Algebra ℚ K] (u : Fin 3 → K) :
    Matrix (Fin 3) (Fin 3) K :=
  upperLeftBlock (blockCayleyX f K u u)

include hT hδ in
theorem ternaryConjMatrix_cayley_mul {u : Fin 3 → K} (hu : 1 + blockPureNorm f K u ≠ 0)
    (huu : 1 - blockPureNorm f K u * blockPureNorm f K u ≠ 0) :
    upperLeftBlock (diagonalBlockConjMatrix f K (blockCayleyCoords f K u) (blockCayleyCoords f K u)) *
        (1 - ternaryCayleyX f K u) = 1 + ternaryCayleyX f K u := by
  have h := diagonalBlockConjMatrix_cayley_mul hδ K hu hu huu
  rw [T.diagonalBlockConjMatrix_self_eq_fixLast hT hδ K (blockCayleyCoords_norm K hu)] at h
  have h' := congrArg upperLeftBlock h
  rwa [upperLeftBlock_fixLastBlockMatrix_mul, upperLeftBlock_sub, upperLeftBlock_add, upperLeftBlock_one] at h'

end TernaryCayley

end RationalQuadraticSpaceMatrix
