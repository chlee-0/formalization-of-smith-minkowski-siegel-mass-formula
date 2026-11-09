import SMSFormula.Lattice

/-!
# Positive-definite integral quadratic forms

An *integral quadratic form* `Q` on `ℤⁿ` takes integral values, `Q(ℤⁿ) ⊆ ℤ`.  An
*integral lattice* (`PositiveDefiniteIntegralLattice`) is the narrower case of an integral bilinear
form `b` with `q(x) = b(x, x)`.  The symmetric rational matrix `T` with
`Q(x) = xᵀ T x` is half-integral; the form itself is integral.  The stored
matrix is the integral polar Gram matrix `A = 2T`; its diagonal is even,
while its off-diagonal entries may be odd.  Thus `T` is a symmetric
half-integral rational matrix and

`Q(x) = xᵀ T x = (1 / 2) xᵀ A x`

is integral on `ℤⁿ`.  The integral upper-triangular coefficient matrix below
defines `Q` without extracting rational denominators.
-/

open Matrix

noncomputable section

namespace Matrix

/-- A rational symmetric matrix is half-integral when its diagonal entries
are integral and twice every entry is integral. -/
def IsHalfIntegral {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℚ) : Prop :=
  T.IsSymm ∧
    (∀ i, ∃ a : ℤ, T i i = (a : ℚ)) ∧
    (∀ i j, ∃ a : ℤ, 2 * T i j = (a : ℚ))

end Matrix

/-- A positive-definite integral quadratic form `Q` on `ℤⁿ` (`Q(ℤⁿ) ⊆ ℤ`), stored through its
integral polar Gram matrix `A = 2T` on the based module `ℤ^n`. This record is not
an arbitrary abstract module presentation. The half-integral symmetric matrix `T` satisfies
`Q(x) = xᵀ T x`.  An integral quadratic form takes integral values; an integral lattice
(`PositiveDefiniteIntegralLattice`) has an integral bilinear form `b` with `q(x) = b(x, x)`. -/
structure PositiveDefiniteIntegralQuadraticForm (n : ℕ) where
  /-- The integral Gram matrix of the polar bilinear form. -/
  polarGramMatrix : Matrix (Fin n) (Fin n) ℤ
  /-- The polar Gram matrix is symmetric. -/
  polarGram_symm : polarGramMatrix.IsSymm
  /-- Its diagonal is even, exactly the integrality condition for `Q`. -/
  polarGram_even_diag : ∀ i, Even (polarGramMatrix i i)
  /-- The polar Gram matrix is positive definite over `ℝ`. -/
  polarGram_posDef :
    (polarGramMatrix.map (Int.cast : ℤ → ℝ)).PosDef

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## Integral and rational quadratic matrices -/

/-- The integral upper-triangular coefficient matrix of `Q`.  Its diagonal is
`Aᵢᵢ / 2`, its strict upper triangle is copied from `A`, and its strict lower
triangle is zero. -/
def quadraticCoefficientMatrix : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦
    if i = j then H.polarGramMatrix i i / 2
    else if i < j then H.polarGramMatrix i j else 0

/-- The coefficient matrix symmetrizes to the stored polar Gram matrix. -/
theorem quadraticCoefficientMatrix_add_transpose :
    H.quadraticCoefficientMatrix + H.quadraticCoefficientMatrixᵀ =
      H.polarGramMatrix := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [quadraticCoefficientMatrix, hij, hij.ne,
      hij.ne', not_lt_of_ge hij.le]
  · subst j
    have heven := H.polarGram_even_diag i
    simp only [quadraticCoefficientMatrix, Matrix.add_apply,
      Matrix.transpose_apply, if_pos]
    simpa [two_mul] using Int.two_mul_ediv_two_of_even heven
  · have hji : j < i := hij
    have hsymm : H.polarGramMatrix j i = H.polarGramMatrix i j :=
      (H.polarGram_symm.apply j i).symm
    simp [quadraticCoefficientMatrix, hji, hji.ne, hji.ne',
      (not_lt_of_ge hji.le), hsymm]

/-- The symmetric half-integral matrix `T = A / 2` representing the integral
quadratic form, `Q(x) = xᵀTx`. -/
def quadraticMatrix : Matrix (Fin n) (Fin n) ℚ :=
  (2 : ℚ)⁻¹ • H.polarGramMatrix.map (Int.cast : ℤ → ℚ)

/-- The attached rational matrix really is symmetric half-integral. -/
theorem quadraticMatrix_isHalfIntegral :
    H.quadraticMatrix.IsHalfIntegral := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [quadraticMatrix, Matrix.transpose_apply,
      H.polarGram_symm.apply]
  · intro i
    obtain ⟨a, ha⟩ := H.polarGram_even_diag i
    refine ⟨a, ?_⟩
    rw [quadraticMatrix]
    simp only [Matrix.smul_apply, Matrix.map_apply]
    rw [ha]
    push_cast
    change (2 : ℚ)⁻¹ * ((a : ℚ) + a) = a
    norm_num
    ring
  · intro i j
    refine ⟨H.polarGramMatrix i j, ?_⟩
    simp [quadraticMatrix]

/-! ## Quadratic and bilinear forms -/

/-- The integral quadratic form represented by the upper-triangular
coefficient matrix. -/
def quadraticForm : QuadraticForm ℤ (Fin n → ℤ) :=
  H.quadraticCoefficientMatrix.toQuadraticMap'

/-- Evaluation of the integral quadratic form. -/
def quadForm (x : Fin n → ℤ) : ℤ :=
  H.quadraticForm x

/-- The polar bilinear form attached to `Q`. -/
def polarBilin : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
  H.quadraticForm.polarBilin

/-- Evaluation of `Q` is the matrix polynomial `xᵀ C x`. -/
theorem quadForm_eq_dotProduct (x : Fin n → ℤ) :
    H.quadForm x =
      dotProduct x (H.quadraticCoefficientMatrix.mulVec x) := by
  simpa [quadForm, quadraticForm, Matrix.toQuadraticMap']
    using Matrix.toLinearMap₂'_apply' H.quadraticCoefficientMatrix x x

/-- Expanded integral matrix polynomial.  The conditional coefficient is
exactly `Aᵢᵢ/2` on the diagonal, `Aᵢⱼ` above it, and zero below it. -/
theorem quadForm_eq_matrixPolynomial (x : Fin n → ℤ) :
    H.quadForm x =
      ∑ i, ∑ j,
        x i * (if i = j then H.polarGramMatrix i i / 2
          else if i < j then H.polarGramMatrix i j else 0) * x j := by
  simp [H.quadForm_eq_dotProduct, dotProduct, Matrix.mulVec,
    quadraticCoefficientMatrix, Finset.mul_sum, mul_assoc]

/-- The usual integral polynomial: half the even diagonal coefficients and
one copy of every strict-upper-triangular polar coefficient. -/
theorem quadForm_eq_diagonal_sum_add_strictUpperSum (x : Fin n → ℤ) :
    H.quadForm x =
      (∑ i, (H.polarGramMatrix i i / 2) * x i ^ 2) +
        ∑ i, ∑ j ∈ Finset.Ioi i, H.polarGramMatrix i j * x i * x j := by
  rw [H.quadForm_eq_matrixPolynomial]
  calc
    (∑ i, ∑ j,
        x i * (if i = j then H.polarGramMatrix i i / 2
          else if i < j then H.polarGramMatrix i j else 0) * x j) =
        ∑ i, ((H.polarGramMatrix i i / 2) * x i ^ 2 +
          ∑ j ∈ Finset.Ioi i, H.polarGramMatrix i j * x i * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [mul_ite, ite_mul, mul_zero, zero_mul]
      have hsingle :
          Finset.univ.filter (fun j : Fin n ↦ i = j) = {i} := by
        ext j
        simp [eq_comm]
      have hupper :
          (Finset.univ.filter (fun j : Fin n ↦ ¬ i = j)).filter
              (fun j ↦ i < j) = Finset.Ioi i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Ioi]
        constructor
        · exact fun h ↦ h.2
        · intro hij
          exact ⟨fun hEq ↦ by subst j; exact (lt_irrefl i hij), hij⟩
      rw [Finset.sum_ite, hsingle, Finset.sum_ite, hupper]
      simp [mul_comm, mul_left_comm, mul_assoc, pow_two]
    _ = _ := by
      rw [Finset.sum_add_distrib]

/-- The polar form has the stored integral Gram matrix `A`. -/
theorem polar_eq_dotProduct (x y : Fin n → ℤ) :
    QuadraticMap.polar H.quadraticForm x y =
      dotProduct x (H.polarGramMatrix.mulVec y) := by
  rw [show H.polarGramMatrix =
      H.quadraticCoefficientMatrix + H.quadraticCoefficientMatrixᵀ from
    H.quadraticCoefficientMatrix_add_transpose.symm]
  change QuadraticMap.polar
      (Matrix.toQuadraticForm' H.quadraticCoefficientMatrix) x y = _
  simp only [Matrix.toQuadraticForm',
    LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply', Matrix.add_mulVec, dotProduct_add]
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec]
  simp only [Matrix.vecMul_transpose]
  congr 1
  calc
    (y ᵥ* H.quadraticCoefficientMatrix) ⬝ᵥ x =
        dotProduct y (H.quadraticCoefficientMatrix.mulVec x) :=
      (Matrix.dotProduct_mulVec y H.quadraticCoefficientMatrix x).symm
    _ = dotProduct (H.quadraticCoefficientMatrix.mulVec x) y :=
      dotProduct_comm _ _

/-- Evaluation of the polar bilinear form is `xᵀ A y`. -/
theorem polarBilin_eq_dotProduct (x y : Fin n → ℤ) :
    H.polarBilin x y = dotProduct x (H.polarGramMatrix.mulVec y) := by
  simpa [polarBilin, QuadraticMap.polarBilin_apply_apply] using
    H.polar_eq_dotProduct x y

/-- The integral identity `2Q(x) = xᵀAx`. -/
theorem two_mul_quadForm_eq_polarGram (x : Fin n → ℤ) :
    2 * H.quadForm x = dotProduct x (H.polarGramMatrix.mulVec x) := by
  rw [← H.polar_eq_dotProduct x x]
  simp [quadForm, two_mul, QuadraticMap.polar_self]

/-- After casting to `ℚ`, the integral form is `xᵀTx`. -/
theorem quadForm_cast_eq_quadraticMatrix (x : Fin n → ℤ) :
    (H.quadForm x : ℚ) =
      dotProduct (fun i ↦ (x i : ℚ))
        (H.quadraticMatrix.mulVec (fun i ↦ (x i : ℚ))) := by
  have h := congrArg (fun z : ℤ ↦ (z : ℚ))
    (H.two_mul_quadForm_eq_polarGram x)
  simp only [Int.cast_mul, Int.cast_ofNat] at h
  have hcast :
      ((dotProduct x (H.polarGramMatrix.mulVec x) : ℤ) : ℚ) =
        dotProduct (fun i ↦ (x i : ℚ))
          ((H.polarGramMatrix.map (Int.cast : ℤ → ℚ)).mulVec
            (fun i ↦ (x i : ℚ))) := by
    simp [dotProduct, Matrix.mulVec]
  rw [hcast] at h
  rw [quadraticMatrix]
  have hscale :
      dotProduct (fun i ↦ (x i : ℚ))
          (((2 : ℚ)⁻¹ • H.polarGramMatrix.map (Int.cast : ℤ → ℚ)).mulVec
            (fun i ↦ (x i : ℚ))) =
        (2 : ℚ)⁻¹ *
          dotProduct (fun i ↦ (x i : ℚ))
            ((H.polarGramMatrix.map (Int.cast : ℤ → ℚ)).mulVec
              (fun i ↦ (x i : ℚ))) := by
    rw [Matrix.smul_mulVec, dotProduct_smul]
    rfl
  rw [hscale]
  norm_num at h ⊢
  linarith

/-! ## Positivity and determinants -/

/-- The integral quadratic form is positive on every nonzero integral
vector. -/
theorem quadForm_pos {x : Fin n → ℤ} (hx : x ≠ 0) :
    0 < H.quadForm x := by
  let xℝ : Fin n → ℝ := fun i ↦ (x i : ℝ)
  have hxℝ : xℝ ≠ 0 := by
    intro h
    apply hx
    ext i
    exact Int.cast_eq_zero.mp (congr_fun h i)
  have hpos := H.polarGram_posDef.dotProduct_mulVec_pos (x := xℝ) hxℝ
  have hcast :
      ((dotProduct x (H.polarGramMatrix.mulVec x) : ℤ) : ℝ) =
        dotProduct xℝ
          ((H.polarGramMatrix.map (Int.cast : ℤ → ℝ)).mulVec xℝ) := by
    simp [xℝ, dotProduct, Matrix.mulVec]
  have htwo : 0 < (2 * H.quadForm x : ℤ) := by
    exact Int.cast_pos.mp (by
      rw [H.two_mul_quadForm_eq_polarGram, hcast]
      exact hpos)
  omega

/-- The determinant of the integral polar Gram matrix. -/
def polarDeterminant : ℤ := H.polarGramMatrix.det

/-- The determinant `det(T)` of the half-integral matrix `T` representing `Q`. -/
def quadraticDeterminant : ℚ := H.quadraticMatrix.det

/-- The polar discriminant is positive. -/
theorem polarDeterminant_pos : 0 < H.polarDeterminant := by
  have hdet :
      0 < (H.polarGramMatrix.map (Int.cast : ℤ → ℝ)).det :=
    H.polarGram_posDef.det_pos
  rw [← Int.cast_det] at hdet
  exact Int.cast_pos.mp (by simpa [polarDeterminant] using hdet)

/-- Determinant scaling for `A = 2T`, in rational orientation. -/
theorem polarDeterminant_cast_eq_two_pow_mul_quadraticDeterminant :
    (H.polarDeterminant : ℚ) =
      (2 : ℚ) ^ n * H.quadraticDeterminant := by
  rw [polarDeterminant, quadraticDeterminant, quadraticMatrix,
    Matrix.det_smul]
  simp only [Fintype.card_fin, Int.cast_det]
  have hp : (2 : ℚ) ^ n * (2 : ℚ)⁻¹ ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hp, one_mul]

end PositiveDefiniteIntegralQuadraticForm

end
