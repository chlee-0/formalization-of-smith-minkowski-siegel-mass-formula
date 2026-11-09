import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive-definite integral bilinear lattices over ℤ

This file defines the basic objects for the Smith–Minkowski–Siegel mass formula:

* `PositiveDefiniteIntegralLattice n` — the integer-matrix presentation of a
  positive-definite integral quadratic lattice of rank `n`, where the
  symmetric quadratic matrix `F` itself has integral entries and
  `q(x) = xᵀ F x`.

This is a useful special case, but not the most general matrix presentation of
an integral quadratic form: in general the symmetric quadratic matrix may be
half-integral while its polar Gram matrix is integral with even diagonal.
* The quadratic form as a Mathlib `QuadraticForm`, together with its polar
  bilinear form.
* The bilinear Gram matrix `A = 2F` and its determinant.
* Integral isometries `O(L)` and proper integral isometries `SO(L)`.

## Matrix convention

After choosing a ℤ-basis the quadratic form is `q(x) = xᵀ F x` with
`F ∈ Mₙ(ℤ)`.  We store this quadratic matrix `F`, and use Mathlib's
`Matrix.toQuadraticMap'` for the corresponding `QuadraticForm`.  The bilinear
Gram matrix for the polar form is then `A = F + Fᵀ`, which is `2F` in the
symmetric case.

## References

* R. Schulze-Pillot, *Lecture Notes on Quadratic Forms and their Arithmetic*.
-/

open Matrix

noncomputable section

/-! ### The lattice structure -/

/-- The integer-matrix model of a positive-definite integral
bilinear lattice on the based module `ℤ^n`, represented by a symmetric
`F ∈ Mₙ(ℤ)` with `q(x) = xᵀ F x`.

An integral lattice has an integral bilinear form `b` with `q(x) = b(x, x)`; an
integral quadratic form only takes integral values.  For integral quadratic
forms whose symmetric matrix is only half-integral, use `PositiveDefiniteIntegralQuadraticForm`.
-/
structure PositiveDefiniteIntegralLattice (n : ℕ) where
  /-- The integral pairing matrix G; the norm is `q(x) = xᵀ G x`. -/
  pairingMatrix : Matrix (Fin n) (Fin n) ℤ
  /-- `F` is symmetric. -/
  form_symm : pairingMatrix.IsSymm
  /-- `F`, viewed over `ℝ`, is positive definite. -/
  form_posDef : (pairingMatrix.map (Int.cast : ℤ → ℝ)).PosDef

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-! ### Pairing, norm and polarization -/

/-- The integral lattice pairing with stored matrix G. This is a based
presentation on `ℤ^n`; it is not the polar form of its norm. -/
def pairing : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
  Matrix.toLinearMap₂' ℤ L.pairingMatrix

/-- The pairing is the matrix expression `xᵀ G y`. -/
theorem pairing_eq_dotProduct (x y : Fin n → ℤ) :
    L.pairing x y = dotProduct x (L.pairingMatrix.mulVec y) := by
  simpa [pairing] using Matrix.toLinearMap₂'_apply' L.pairingMatrix x y

/-- Symmetry of the actual integral pairing. -/
theorem pairing_comm (x y : Fin n → ℤ) : L.pairing x y = L.pairing y x := by
  simp only [pairing_eq_dotProduct, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L.form_symm.apply i j]
  ring

/-- The quadratic form `q(x) = xᵀ F x`, using Mathlib's quadratic-form API. -/
def quadraticForm : QuadraticForm ℤ (Fin n → ℤ) :=
  L.pairingMatrix.toQuadraticMap'

/-- The polar Gram matrix `A = F + Fᵀ`, the Gram matrix of the polar bilinear
form `polar(q)(x,y) = q(x+y) - q(x) - q(y)`.  Since `F` is symmetric this is `2F`
(`polarGramMatrix_eq_two_smul_pairingMatrix`).  Same name and meaning as
`PositiveDefiniteIntegralQuadraticForm.polarGramMatrix`. -/
def polarGramMatrix : Matrix (Fin n) (Fin n) ℤ :=
  L.pairingMatrix + L.pairingMatrixᵀ

/-- The polar bilinear form associated to `q`. -/
def polarBilin : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
  L.quadraticForm.polarBilin

/-- Evaluation of the quadratic form. -/
def quadForm (x : Fin n → ℤ) : ℤ :=
  L.quadraticForm x

/-- Evaluation of the stored quadratic form is the matrix expression
`xᵀ F x`. -/
lemma quadForm_eq_dotProduct (x : Fin n → ℤ) :
    L.quadForm x = dotProduct x (L.pairingMatrix.mulVec x) := by
  simpa [quadForm, quadraticForm, Matrix.toQuadraticMap']
    using Matrix.toLinearMap₂'_apply' L.pairingMatrix x x

/-- The quadratic form is the norm of the integral pairing. -/
theorem quadraticForm_eq_pairing_self (x : Fin n → ℤ) :
    L.quadraticForm x = L.pairing x x := by
  exact L.quadForm_eq_dotProduct x |>.trans (L.pairing_eq_dotProduct x x).symm

/-- Polarization doubles the pairing; it does not change its definition. -/
theorem polarBilin_eq_two_smul_pairing : L.polarBilin = (2 : ℤ) • L.pairing := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change QuadraticMap.polar L.quadraticForm x y = 2 * L.pairing x y
  rw [QuadraticMap.polar]
  simp only [quadraticForm_eq_pairing_self, map_add, LinearMap.add_apply]
  rw [L.pairing_comm y x]
  ring

/-- The norm polarization has the literal factor two. -/
theorem polar_quadraticForm_eq_two_mul_pairing (x y : Fin n → ℤ) :
    QuadraticMap.polar L.quadraticForm x y = 2 * L.pairing x y := by
  change L.polarBilin x y = _
  rw [L.polarBilin_eq_two_smul_pairing]
  rfl

/-- The stored quadratic form is homogeneous of degree two. -/
lemma quadForm_smul (a : ℤ) (x : Fin n → ℤ) :
    L.quadForm (a • x) = a ^ 2 * L.quadForm x := by
  simpa [quadForm, pow_two] using L.quadraticForm.map_smul a x

/-- The stored quadratic form is positive on every nonzero integral vector. -/
lemma quadForm_pos {x : Fin n → ℤ} (hx : x ≠ 0) : 0 < L.quadForm x := by
  let xℝ : Fin n → ℝ := fun i => (x i : ℝ)
  have hxℝ : xℝ ≠ 0 := by
    intro h
    apply hx
    ext i
    exact Int.cast_eq_zero.mp (congr_fun h i)
  have hpos := L.form_posDef.dotProduct_mulVec_pos (x := xℝ) hxℝ
  have hcast :
      (L.quadForm x : ℝ) =
        xℝ ⬝ᵥ (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).mulVec xℝ := by
    simp [quadForm_eq_dotProduct, xℝ, Matrix.mulVec, dotProduct]
  have hpos_cast : 0 < (L.quadForm x : ℝ) := by
    rw [hcast]
    simpa [xℝ] using hpos
  exact Int.cast_pos.mp hpos_cast

/-! ### Determinants -/

/-- The quadratic determinant `det(F)` of the stored quadratic matrix `F`.

This is the determinant `det_B(L)` of the symmetric bilinear form
`B(x,y) = (q(x+y)-q(x)-q(y))/2`, whose matrix is `F` in this convention (the
normalization of Schulze--Pillot's survey).  Classical unimodularity is
`pairingDeterminant = 1`. -/
def pairingDeterminant : ℤ := L.pairingMatrix.det

/-- The Schulze--Pillot determinant `det_B(L) = det(F)` is positive for a
positive-definite integral lattice. -/
theorem pairingDeterminant_pos : 0 < L.pairingDeterminant := by
  have h : 0 < (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).det := L.form_posDef.det_pos
  rw [← Int.cast_det] at h
  exact Int.cast_pos.mp (by simpa [pairingDeterminant] using h)

/-- The polar discriminant `det(A)` of the polar Gram matrix `A = 2F`; it equals
`2^n · pairingDeterminant` (so it is `2^n`, not `1`, for a unimodular
lattice).  Same name and meaning as `PositiveDefiniteIntegralQuadraticForm.polarDeterminant`. -/
def polarDeterminant : ℤ := L.polarGramMatrix.det

/-- Since the stored quadratic matrix is symmetric, the polar Gram matrix is
`2 • F`. -/
lemma polarGramMatrix_eq_two_smul_pairingMatrix :
    L.polarGramMatrix = (2 : ℤ) • L.pairingMatrix := by
  ext i j
  simp [polarGramMatrix, Matrix.transpose_apply, L.form_symm.apply, two_mul]

/-- The bilinear discriminant is `2^n` times Schulze--Pillot's determinant
`det_B = det(F)`.

The fixed-determinant finiteness theorem is stated for `pairingDeterminant`, not for this
scaled discriminant. -/
lemma polarDeterminant_eq_two_pow_mul_pairingDeterminant : L.polarDeterminant = (2 : ℤ) ^ n * L.pairingDeterminant := by
  rw [polarDeterminant, polarGramMatrix_eq_two_smul_pairingMatrix, Matrix.det_smul]
  simp [pairingDeterminant]

/-- The bilinear Gram determinant is positive for a positive-definite
integral lattice. -/
theorem polarDeterminant_pos : 0 < L.polarDeterminant := by
  rw [polarDeterminant_eq_two_pow_mul_pairingDeterminant]
  exact mul_pos (pow_pos (by norm_num : 0 < (2 : ℤ)) n) L.pairingDeterminant_pos

/-! ### Isometry groups -/

/-- `U` is an integral isometry of `L` when `U` is invertible over `ℤ`
and `Uᵀ F U = F`. -/
def IsIsometry (U : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsUnit U ∧ Uᵀ * L.pairingMatrix * U = L.pairingMatrix

/-- The ordinary integral isometry group `O(L)`. -/
def IsometryGroup : Type :=
  { U : Matrix (Fin n) (Fin n) ℤ // L.IsIsometry U }

/-- `U` is a *proper* integral isometry of `L` when it is an isometry of
determinant `1`. -/
def IsProperIsometry (U : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  L.IsIsometry U ∧ U.det = 1

/-- The proper integral isometry group `SO(L)`. -/
def ProperIsometryGroup : Type :=
  { U : Matrix (Fin n) (Fin n) ℤ // L.IsProperIsometry U }

/-! ### Global integral isometry between two lattices -/

/-- Two integral lattices of the same rank are (globally, integrally) isometric
when there exists an invertible integer matrix `U` with `Uᵀ F' U = F`. -/
def IsGlobalIsometry (L' : PositiveDefiniteIntegralLattice n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ,
    IsUnit U ∧ Uᵀ * L'.pairingMatrix * U = L.pairingMatrix

/-- A global integral isometry preserves Schulze--Pillot's determinant
`det_B = det(F)`. -/
lemma pairingDeterminant_eq_of_isGlobalIsometry {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsGlobalIsometry L') : L.pairingDeterminant = L'.pairingDeterminant := by
  obtain ⟨U, hU_unit, hU⟩ := h
  have hdet := congrArg Matrix.det hU
  have hdet' : L.pairingDeterminant = U.det * L'.pairingDeterminant * U.det := by
    simpa [pairingDeterminant, Matrix.det_mul, Matrix.det_transpose]
      using hdet.symm
  have hUdet_unit : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit
  have hUdet_sq : U.det ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hUdet_unit with hUdet | hUdet <;> simp [hUdet]
  calc
    L.pairingDeterminant = U.det * L'.pairingDeterminant * U.det := hdet'
    _ = U.det ^ 2 * L'.pairingDeterminant := by ring
    _ = L'.pairingDeterminant := by rw [hUdet_sq, one_mul]

/-- A global integral isometry preserves the bilinear Gram determinant
`polarDeterminant = det(F + Fᵀ)`. -/
lemma polarDeterminant_eq_of_isGlobalIsometry {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsGlobalIsometry L') : L.polarDeterminant = L'.polarDeterminant := by
  rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant, L'.polarDeterminant_eq_two_pow_mul_pairingDeterminant,
    pairingDeterminant_eq_of_isGlobalIsometry h]

end PositiveDefiniteIntegralLattice

end
