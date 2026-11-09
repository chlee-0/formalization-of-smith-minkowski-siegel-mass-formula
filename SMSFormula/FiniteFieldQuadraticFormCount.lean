import SMSFormula.FiniteFieldDiagonalQuadraticCount
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The finite-field count of a nondegenerate symmetric Gram matrix. Over a finite
field `K` of odd characteristic, a symmetric `M` with `det M ≠ 0` is isometric to
a diagonal form `∑ wᵢ yᵢ²` (mathlib's orthogonal-basis diagonalization) with
`det M = c² ∏ wᵢ`, `c ≠ 0`. Hence `#{r : rᵀ M r = a}` is the diagonal count with
`χ(∏ wᵢ) = χ(det M)`:

* `N = 2m + 1`: `#{rᵀ M r = a} = q^{2m} + q^m χ((-1)^m det M · a)`;
* `N = 2m + 2`: `#{rᵀ M r = a} = q^{2m+1} + q^m χ((-1)^{m+1} det M)(q·[a = 0] − 1)`.

The diagonalization is only an existence statement inside the proof; nothing
enters the statements. -/
noncomputable section
open Finset Matrix QuadraticMap

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The number of solutions of `rᵀ M r = a`. -/
def matrixQuadraticCount {N : ℕ} (M : Matrix (Fin N) (Fin N) K) (a : K) : ℕ :=
  (univ.filter fun r : Fin N → K ↦ r ⬝ᵥ M *ᵥ r = a).card

omit [Fintype K] [DecidableEq K] in
theorem toQuadraticMap'_apply {N : ℕ} (M : Matrix (Fin N) (Fin N) K) (x : Fin N → K) :
    M.toQuadraticMap' x = x ⬝ᵥ M *ᵥ x := by
  change Matrix.toQuadraticForm' M x = _
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

omit [Fintype K] in
/-- For symmetric `M`, the matrix of `x ↦ xᵀ M x` is `M`. -/
theorem toMatrix'_toQuadraticMap' [Invertible (2 : K)] {N : ℕ} (M : Matrix (Fin N) (Fin N) K)
    (hM : M.IsSymm) : M.toQuadraticMap'.toMatrix' = M := by
  ext i j
  rw [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply, QuadraticMap.associated_apply]
  simp only [toQuadraticMap'_apply, add_dotProduct, mulVec_add, dotProduct_add,
    mulVec_single_one, single_one_dotProduct]
  have hx : M.col i i + M.col i j + (M.col j i + M.col j j) - M.col i i - M.col j j =
      (2 : Module.End K K) • M i j := by
    rw [Module.End.smul_def]
    simp only [col_apply, hM.apply i j]
    simp
    ring
  rw [hx, smul_smul, invOf_mul_self, one_smul]

omit [Fintype K] in
theorem weightedSumSquares_eq_toQuadraticMap' {N : ℕ} (w : Fin N → Kˣ) :
    weightedSumSquares K w = (Matrix.diagonal fun i ↦ (w i : K)).toQuadraticMap' := by
  ext x
  rw [toQuadraticMap'_apply, weightedSumSquares_apply]
  simp only [dotProduct, mulVec_diagonal, Units.smul_def, smul_eq_mul]
  exact sum_congr rfl fun i _ ↦ by ring

/-- Diagonalization: a nondegenerate symmetric `M` has the count of a diagonal form
with nonzero weights `w` and `det M = c² ∏ wᵢ`, `c ≠ 0`. -/
theorem exists_diagonal_of_det_ne_zero (hK : ringChar K ≠ 2) {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    ∃ w : Fin N → K, (∀ i, w i ≠ 0) ∧
      (∀ a, matrixQuadraticCount M a = diagonalQuadraticCount w a) ∧
      ∃ c : K, c ≠ 0 ∧ M.det = c ^ 2 * ∏ i, w i := by
  haveI : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
  have hQM : (M.toQuadraticMap').toMatrix' = M := toMatrix'_toQuadraticMap' M hM
  have hsep : (associated (R := K) (M.toQuadraticMap')).SeparatingLeft := by
    rw [← LinearMap.separatingLeft_toMatrix₂'_iff]
    change ((M.toQuadraticMap').toMatrix').SeparatingLeft
    rw [hQM]
    exact Matrix.separatingLeft_iff_det_ne_zero.mpr hdet
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' (M.toQuadraticMap') hsep
  have hr := Module.finrank_fin_fun K (n := N)
  generalize Module.finrank K (Fin N → K) = r at w e hr
  subst hr
  have hval : ∀ x, x ⬝ᵥ M *ᵥ x = ∑ i, (w i : K) * (e x) i ^ 2 := by
    intro x
    rw [← toQuadraticMap'_apply, ← e.map_app x, weightedSumSquares_apply]
    simp only [Units.smul_def, smul_eq_mul, pow_two]
  have hcomp : M.toQuadraticMap' = (weightedSumSquares K w).comp e.toLinearEquiv.toLinearMap := by
    ext x
    exact (e.map_app x).symm
  have hdisc := QuadraticForm.discr'_comp (Q := weightedSumSquares K w) e.toLinearEquiv.toLinearMap
  rw [← hcomp] at hdisc
  unfold QuadraticForm.discr' at hdisc
  have hW : (QuadraticForm.toMatrix' (weightedSumSquares K w)).det = ∏ i, (w i : K) := by
    rw [weightedSumSquares_eq_toQuadraticMap', toMatrix'_toQuadraticMap' _ (isSymm_diagonal _),
      det_diagonal]
  rw [hQM, hW] at hdisc
  refine ⟨fun i ↦ w i, fun i ↦ (w i).ne_zero, fun a ↦ ?_, ?_⟩
  · unfold matrixQuadraticCount diagonalQuadraticCount
    refine Finset.card_equiv e.toLinearEquiv.toEquiv fun x ↦ ?_
    simp only [mem_filter, mem_univ, true_and]
    rw [hval]
    rfl
  · refine ⟨(LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det, ?_, by rw [hdisc]; ring⟩
    intro h0
    rw [h0, zero_mul, zero_mul] at hdisc
    exact hdet hdisc

/-- Odd rank `N = 2m + 1`: `#{rᵀ M r = a} = q^{2m} + q^m χ((-1)^m det M · a)`. -/
theorem matrixQuadraticCount_odd (hK : ringChar K ≠ 2) (m : ℕ)
    (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K) (hM : M.IsSymm) (hdet : M.det ≠ 0)
    (a : K) :
    (matrixQuadraticCount M a : ℤ) = (Fintype.card K : ℤ) ^ (2 * m) +
      (Fintype.card K : ℤ) ^ m * quadraticChar K ((-1) ^ m * M.det * a) := by
  obtain ⟨w, hw, hcount, c, hc, hdetw⟩ := exists_diagonal_of_det_ne_zero hK M hM hdet
  rw [hcount, diagonalQuadraticCount_odd hK m w hw a, hdetw]
  simp only [map_mul, map_pow, quadraticChar_sq_one hc, one_mul]

/-- Even rank `N = 2m + 2`:
`#{rᵀ M r = a} = q^{2m+1} + q^m χ((-1)^{m+1} det M)(q·[a = 0] − 1)`. -/
theorem matrixQuadraticCount_even (hK : ringChar K ≠ 2) (m : ℕ)
    (M : Matrix (Fin (2 * m + 2)) (Fin (2 * m + 2)) K) (hM : M.IsSymm) (hdet : M.det ≠ 0)
    (a : K) :
    (matrixQuadraticCount M a : ℤ) = (Fintype.card K : ℤ) ^ (2 * m + 1) +
      (Fintype.card K : ℤ) ^ m * quadraticChar K ((-1) ^ (m + 1) * M.det) *
        ((if a = 0 then (Fintype.card K : ℤ) else 0) - 1) := by
  obtain ⟨w, hw, hcount, c, hc, hdetw⟩ := exists_diagonal_of_det_ne_zero hK M hM hdet
  rw [hcount, diagonalQuadraticCount_even hK m w hw a, hdetw]
  simp only [map_mul, map_pow, quadraticChar_sq_one hc, one_mul]

end FiniteField
