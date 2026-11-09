import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# The coordinate algebra of the block conjugation

For scalars `f₀, f₁, f₂` of a commutative ring (the block space `⟨f₀, f₁, f₂⟩ ⊥ ⟨f₀f₁f₂⟩`):
* `qmul`, `qconj`, `qnorm`: the quaternion multiplication, conjugation and norm in the basis `1, e₀e₁, e₀e₂, e₁e₂`,
  with `qnorm (qmul h k) = qnorm h * qnorm k`;
* `theta c = (f₀f₁f₂c₃, −f₂c₂, f₁c₁, −f₀c₀)` with `qnorm (theta c) = f₀f₁f₂ · q_U(c)`;
* `thetaInv` (supplied inverses) with `q_U(thetaInv y) = f₀f₁f₂⁻¹ · qnorm y`;
* the conjugation coordinates `conjCoords h k c = θ⁻¹(h θ(c) k̄)` scale the norm by `qnorm h · qnorm k`
  (`qU_conjCoords`), and their matrix factors as `Θ⁻¹ R_{k̄} L_h Θ` with `det L_h = qnorm h ²`,
  `det R_k = qnorm k ²` (`det_conjMatrix`: `det M = qnorm h ² · qnorm k ²`).
Nothing is chosen.
-/

noncomputable section

namespace BlockConjugationCoordinates

open Matrix

variable {R : Type*} [CommRing R] (f0 f1 f2 : R)

/-- The quaternion multiplication in the basis `1, e₀e₁, e₀e₂, e₁e₂`. -/
def qmul (h k : Fin 4 → R) : Fin 4 → R :=
  ![h 0 * k 0 - f0 * f1 * h 1 * k 1 - f0 * f2 * h 2 * k 2 - f1 * f2 * h 3 * k 3,
    h 0 * k 1 + h 1 * k 0 - f2 * h 2 * k 3 + f2 * h 3 * k 2,
    h 0 * k 2 + h 2 * k 0 + f1 * h 1 * k 3 - f1 * h 3 * k 1,
    h 0 * k 3 + h 3 * k 0 - f0 * h 1 * k 2 + f0 * h 2 * k 1]

/-- The conjugation. -/
def qconj (h : Fin 4 → R) : Fin 4 → R := ![h 0, -h 1, -h 2, -h 3]

/-- The norm. -/
def qnorm (h : Fin 4 → R) : R :=
  h 0 ^ 2 + f0 * f1 * h 1 ^ 2 + f0 * f2 * h 2 ^ 2 + f1 * f2 * h 3 ^ 2

/-- The block quadratic form `q_U(c) = f₀c₀² + f₁c₁² + f₂c₂² + f₀f₁f₂c₃²`. -/
def qU (c : Fin 4 → R) : R := f0 * c 0 ^ 2 + f1 * c 1 ^ 2 + f2 * c 2 ^ 2 + f0 * f1 * f2 * c 3 ^ 2

/-- `θ(c) = (f₀f₁f₂c₃, −f₂c₂, f₁c₁, −f₀c₀)`. -/
def theta (c : Fin 4 → R) : Fin 4 → R := ![f0 * f1 * f2 * c 3, -(f2 * c 2), f1 * c 1, -(f0 * c 0)]

/-- `θ⁻¹(y) = (−u₀y₃, u₁y₂, −u₂y₁, δ y₀)` with supplied inverses `uᵢ = fᵢ⁻¹`, `δ = (f₀f₁f₂)⁻¹`. -/
def thetaInv (u0 u1 u2 dinv : R) (y : Fin 4 → R) : Fin 4 → R :=
  ![-(u0 * y 3), u1 * y 2, -(u2 * y 1), dinv * y 0]

/-- The conjugation coordinates `θ⁻¹(h θ(c) k̄)`. -/
def conjCoords (u0 u1 u2 dinv : R) (h k c : Fin 4 → R) : Fin 4 → R :=
  thetaInv u0 u1 u2 dinv (qmul f0 f1 f2 (qmul f0 f1 f2 h (theta f0 f1 f2 c)) (qconj k))

theorem qnorm_qmul (h k : Fin 4 → R) :
    qnorm f0 f1 f2 (qmul f0 f1 f2 h k) = qnorm f0 f1 f2 h * qnorm f0 f1 f2 k := by
  simp only [qnorm, qmul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem qnorm_qconj (h : Fin 4 → R) : qnorm f0 f1 f2 (qconj h) = qnorm f0 f1 f2 h := by
  simp only [qnorm, qconj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem qnorm_theta (c : Fin 4 → R) : qnorm f0 f1 f2 (theta f0 f1 f2 c) = f0 * f1 * f2 * qU f0 f1 f2 c := by
  simp only [qnorm, theta, qU, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

variable {f0 f1 f2} {u0 u1 u2 dinv : R}

theorem qU_thetaInv (hu0 : u0 * f0 = 1) (hu1 : u1 * f1 = 1) (hu2 : u2 * f2 = 1)
    (hdinv : dinv * (f0 * f1 * f2) = 1) (y : Fin 4 → R) :
    qU f0 f1 f2 (thetaInv u0 u1 u2 dinv y) = dinv * qnorm f0 f1 f2 y := by
  simp only [qnorm, thetaInv, qU, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (dinv * y 0 ^ 2 - y 1 ^ 2 * u2 - y 2 ^ 2 * u1 - y 3 ^ 2 * u0) * hdinv +
    y 1 ^ 2 * (u2 + dinv * f0 * f1) * hu2 + y 2 ^ 2 * (u1 + dinv * f0 * f2) * hu1 +
    y 3 ^ 2 * (u0 + dinv * f1 * f2) * hu0

/-- The norm scaling of the conjugation: `q_U(θ⁻¹(h θ(c) k̄)) = N(h) N(k) q_U(c)`. -/
theorem qU_conjCoords (hu0 : u0 * f0 = 1) (hu1 : u1 * f1 = 1) (hu2 : u2 * f2 = 1)
    (hdinv : dinv * (f0 * f1 * f2) = 1) (h k c : Fin 4 → R) :
    qU f0 f1 f2 (conjCoords f0 f1 f2 u0 u1 u2 dinv h k c) =
      qnorm f0 f1 f2 h * qnorm f0 f1 f2 k * qU f0 f1 f2 c := by
  rw [conjCoords, qU_thetaInv hu0 hu1 hu2 hdinv, qnorm_qmul, qnorm_qmul, qnorm_theta, qnorm_qconj]
  linear_combination (qnorm f0 f1 f2 h * qnorm f0 f1 f2 k * qU f0 f1 f2 c) * hdinv

/-! ## The conjugation matrix and its determinant -/

variable (f0 f1 f2)

/-- The left multiplication matrix `L_h`. -/
def lmat (h : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R := Matrix.of fun i j ↦ qmul f0 f1 f2 h (Pi.single j 1) i

/-- The right multiplication matrix `R_k`. -/
def rmat (k : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R := Matrix.of fun i j ↦ qmul f0 f1 f2 (Pi.single j 1) k i

theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.det = A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
        A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 +
        A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 +
        A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 +
        A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def]
  ring

theorem det_lmat (h : Fin 4 → R) : (lmat f0 f1 f2 h).det = qnorm f0 f1 f2 h ^ 2 := by
  rw [det_fin_four]
  simp [lmat, qmul, qnorm, Pi.single_apply]
  ring

theorem det_rmat (k : Fin 4 → R) : (rmat f0 f1 f2 k).det = qnorm f0 f1 f2 k ^ 2 := by
  rw [det_fin_four]
  simp [rmat, qmul, qnorm, Pi.single_apply]
  ring

/-- The matrix of `θ`. -/
def thetaMat : Matrix (Fin 4) (Fin 4) R := Matrix.of fun i j ↦ theta f0 f1 f2 (Pi.single j 1) i

/-- The matrix of `θ⁻¹`. -/
def thetaInvMat (u0 u1 u2 dinv : R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j ↦ thetaInv u0 u1 u2 dinv (Pi.single j 1) i

theorem qmul_eq_lmat_mulVec (h k : Fin 4 → R) : qmul f0 f1 f2 h k = lmat f0 f1 f2 h *ᵥ k := by
  funext i
  fin_cases i <;> simp [lmat, qmul, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply] <;> ring

theorem qmul_eq_rmat_mulVec (h k : Fin 4 → R) : qmul f0 f1 f2 h k = rmat f0 f1 f2 k *ᵥ h := by
  funext i
  fin_cases i <;> simp [rmat, qmul, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply] <;> ring

theorem theta_eq_mulVec (c : Fin 4 → R) : theta f0 f1 f2 c = thetaMat f0 f1 f2 *ᵥ c := by
  funext i
  fin_cases i <;> simp [thetaMat, theta, Matrix.mulVec, dotProduct, Pi.single_apply] <;> ring

theorem thetaInv_eq_mulVec (u0 u1 u2 dinv : R) (y : Fin 4 → R) :
    thetaInv u0 u1 u2 dinv y = thetaInvMat u0 u1 u2 dinv *ᵥ y := by
  funext i
  fin_cases i <;> simp [thetaInvMat, thetaInv, Matrix.mulVec, dotProduct, Pi.single_apply] <;>
    ring

/-- The conjugation matrix `M(h, k) = Θ⁻¹ R_{k̄} L_h Θ`. -/
def conjMatrix (u0 u1 u2 dinv : R) (h k : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  thetaInvMat u0 u1 u2 dinv * rmat f0 f1 f2 (qconj k) * lmat f0 f1 f2 h * thetaMat f0 f1 f2

theorem conjCoords_eq_mulVec (u0 u1 u2 dinv : R) (h k c : Fin 4 → R) :
    conjCoords f0 f1 f2 u0 u1 u2 dinv h k c = conjMatrix f0 f1 f2 u0 u1 u2 dinv h k *ᵥ c := by
  rw [conjCoords, conjMatrix, qmul_eq_rmat_mulVec f0 f1 f2 (qmul f0 f1 f2 h _), qmul_eq_lmat_mulVec f0 f1 f2 h,
    theta_eq_mulVec, thetaInv_eq_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem conjMatrix_apply (u0 u1 u2 dinv : R) (h k : Fin 4 → R) (i j : Fin 4) :
    conjMatrix f0 f1 f2 u0 u1 u2 dinv h k i j = conjCoords f0 f1 f2 u0 u1 u2 dinv h k (Pi.single j 1) i := by
  rw [conjCoords_eq_mulVec, Matrix.mulVec_single_one]
  rfl

variable {f0 f1 f2}

theorem det_thetaInvMat_mul_det_thetaMat (hu0 : u0 * f0 = 1) (hu1 : u1 * f1 = 1) (hu2 : u2 * f2 = 1)
    (hdinv : dinv * (f0 * f1 * f2) = 1) :
    (thetaInvMat u0 u1 u2 dinv).det * (thetaMat f0 f1 f2).det = 1 := by
  rw [det_fin_four, det_fin_four]
  simp [thetaInvMat, thetaMat, theta, thetaInv, Pi.single_apply]
  linear_combination (u0 * f0 * u1 * f1 * u2 * f2) * hdinv + (u0 * f0 * u1 * f1) * hu2 + (u0 * f0) * hu1 + hu0

/-- The determinant of the conjugation matrix: `det M(h, k) = N(h)² N(k)²`. -/
theorem det_conjMatrix (hu0 : u0 * f0 = 1) (hu1 : u1 * f1 = 1) (hu2 : u2 * f2 = 1)
    (hdinv : dinv * (f0 * f1 * f2) = 1) (h k : Fin 4 → R) :
    (conjMatrix f0 f1 f2 u0 u1 u2 dinv h k).det = qnorm f0 f1 f2 h ^ 2 * qnorm f0 f1 f2 k ^ 2 := by
  rw [conjMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_rmat, det_lmat, qnorm_qconj]
  linear_combination (qnorm f0 f1 f2 h ^ 2 * qnorm f0 f1 f2 k ^ 2) *
    det_thetaInvMat_mul_det_thetaMat hu0 hu1 hu2 hdinv

/-! ## Polarization -/

/-- A matrix preserving a diagonal quadratic form (with `2` invertible) preserves the diagonal Gram matrix. -/
theorem transpose_mul_diagonal_mul_eq_of_forall [Invertible (2 : R)] (w : Fin 4 → R)
    (M : Matrix (Fin 4) (Fin 4) R)
    (hM : ∀ c : Fin 4 → R, (M *ᵥ c) ⬝ᵥ (Matrix.diagonal w *ᵥ (M *ᵥ c)) = c ⬝ᵥ (Matrix.diagonal w *ᵥ c)) :
    Mᵀ * Matrix.diagonal w * M = Matrix.diagonal w := by
  set B := Mᵀ * Matrix.diagonal w * M with hB
  have hBsymm : ∀ i j, B i j = B j i := by
    intro i j
    simp only [hB, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun x _ ↦ by ring
  have hq : ∀ c : Fin 4 → R, c ⬝ᵥ (B *ᵥ c) = c ⬝ᵥ (Matrix.diagonal w *ᵥ c) := by
    intro c
    rw [← hM c, hB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  ext i j
  have hii := hq (Pi.single i 1)
  have hjj := hq (Pi.single j 1)
  have hij := hq (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single_one,
    single_one_dotProduct] at hii hjj hij
  simp only [Matrix.col_apply] at hii hjj hij
  by_cases hij' : i = j
  · subst hij'
    exact hii
  · have h2 : (2 : R) * B i j = 2 * Matrix.diagonal w i j := by
      rw [hBsymm j i, Matrix.diagonal_apply_ne w (Ne.symm hij'), Matrix.diagonal_apply_ne w hij'] at hij
      rw [Matrix.diagonal_apply_ne w hij']
      linear_combination hij - hii - hjj
    have := congrArg (⅟(2 : R) * ·) h2
    simpa [← mul_assoc] using this

theorem qU_eq_dotProduct (c : Fin 4 → R) :
    qU f0 f1 f2 c = c ⬝ᵥ (Matrix.diagonal ![f0, f1, f2, f0 * f1 * f2] *ᵥ c) := by
  simp [qU, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four]
  ring

/-- The conjugation matrix is orthogonal for unit-norm `h, k`. -/
theorem conjMatrix_orthogonal [Invertible (2 : R)] (hu0 : u0 * f0 = 1) (hu1 : u1 * f1 = 1) (hu2 : u2 * f2 = 1)
    (hdinv : dinv * (f0 * f1 * f2) = 1) {h k : Fin 4 → R} (hh : qnorm f0 f1 f2 h = 1)
    (hk : qnorm f0 f1 f2 k = 1) :
    (conjMatrix f0 f1 f2 u0 u1 u2 dinv h k)ᵀ * Matrix.diagonal ![f0, f1, f2, f0 * f1 * f2] *
        conjMatrix f0 f1 f2 u0 u1 u2 dinv h k = Matrix.diagonal ![f0, f1, f2, f0 * f1 * f2] := by
  refine transpose_mul_diagonal_mul_eq_of_forall _ _ fun c ↦ ?_
  rw [← qU_eq_dotProduct, ← qU_eq_dotProduct, ← conjCoords_eq_mulVec,
    qU_conjCoords hu0 hu1 hu2 hdinv, hh, hk, one_mul, one_mul]

theorem det_conjMatrix_eq_one (hu0 : u0 * f0 = 1) (hu1 : u1 * f1 = 1) (hu2 : u2 * f2 = 1)
    (hdinv : dinv * (f0 * f1 * f2) = 1) {h k : Fin 4 → R} (hh : qnorm f0 f1 f2 h = 1)
    (hk : qnorm f0 f1 f2 k = 1) : (conjMatrix f0 f1 f2 u0 u1 u2 dinv h k).det = 1 := by
  rw [det_conjMatrix hu0 hu1 hu2 hdinv, hh, hk]
  ring

/-- The diagonal element `Φ(h, h)` fixes the last coordinate vector. -/
theorem conjCoords_self_last (hdinv : dinv * (f0 * f1 * f2) = 1) {h : Fin 4 → R}
    (hh : qnorm f0 f1 f2 h = 1) : conjCoords f0 f1 f2 u0 u1 u2 dinv h h (Pi.single 3 1) = Pi.single 3 1 := by
  unfold qnorm at hh
  funext j
  fin_cases j <;> simp [conjCoords, thetaInv, qmul, theta, qconj] <;>
    first
    | ring1
    | linear_combination (f0 * f1 * f2 * dinv) * hh + hdinv

end BlockConjugationCoordinates
