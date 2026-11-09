import SMSFormula.BlockConjugationCoordinates
import Mathlib.Tactic.FieldSimp

/-!
# The Clifford--Cayley parametrization of the block Spin group in coordinates

For a pure quaternion `u` (coordinates of `u₁e₀e₁ + u₂e₀e₂ + u₃e₁e₂`) with norm `N(u)`, the Clifford
Cayley element `κ(u) = (1 + u)(1 − u)⁻¹` has quaternion coordinates `(1 − N(u), 2u)/(1 + N(u))`.
The special-orthogonal matrix of `Φ(κ(u), κ(v))` is the matrix Cayley transform of

`X(u, v) = ((1 + N(v)) A₊(u) + (1 + N(u)) A₋(v)) / (1 − N(u)N(v))`,

with explicit linear skew-adjoint matrices `A₊`, `A₋` (the differentials of the two factors).  This
is the identity `M (1 − X) = 1 + X`, a polynomial identity after clearing denominators; it is
proved here entrywise.  Nothing is chosen.
-/

noncomputable section

open Matrix

namespace BlockConjugationCoordinates

variable {K : Type*} [Field K] (f0 f1 f2 : K)

/-- The norm `N(u)` of the pure quaternion with coordinates `u`. -/
def pureNorm (u : Fin 3 → K) : K := f0 * f1 * u 0 ^ 2 + f0 * f2 * u 1 ^ 2 + f1 * f2 * u 2 ^ 2

/-- The pure quaternion with coordinates `u`. -/
def pureQuat (u : Fin 3 → K) : Fin 4 → K := ![0, u 0, u 1, u 2]

/-- The numerator `(1 + u)² = (1 − N(u), 2u)` of the Clifford Cayley element. -/
def cayleyNum (u : Fin 3 → K) : Fin 4 → K := ![1 - pureNorm f0 f1 f2 u, 2 * u 0, 2 * u 1, 2 * u 2]

/-- The quaternion coordinates of the Clifford Cayley element `κ(u) = (1 + u)(1 − u)⁻¹`. -/
def cayleyCoords (u : Fin 3 → K) : Fin 4 → K := (1 + pureNorm f0 f1 f2 u)⁻¹ • cayleyNum f0 f1 f2 u

/-- The θ-coordinate block generator `P(y) = (1 + N(v)) u y − (1 + N(u)) y v`. -/
def blockCayleyGen (u v : Fin 3 → K) (y : Fin 4 → K) : Fin 4 → K :=
  (1 + pureNorm f0 f1 f2 v) • qmul f0 f1 f2 (pureQuat u) y - (1 + pureNorm f0 f1 f2 u) • qmul f0 f1 f2 y (pureQuat v)

/-- The quaternion Cayley identity (polynomial, no denominators). -/
theorem cayley_quat_identity (u v : Fin 3 → K) (y : Fin 4 → K) :
    qmul f0 f1 f2 (qmul f0 f1 f2 (cayleyNum f0 f1 f2 u)
        ((1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v) • y - blockCayleyGen f0 f1 f2 u v y))
      (qconj (cayleyNum f0 f1 f2 v)) =
    ((1 + pureNorm f0 f1 f2 u) * (1 + pureNorm f0 f1 f2 v)) •
      ((1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v) • y + blockCayleyGen f0 f1 f2 u v y) := by
  funext i
  fin_cases i <;>
    simp only [qmul, qconj, cayleyNum, pureQuat, blockCayleyGen, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    unfold pureNorm <;> ring

/-! ## Bilinearity -/

theorem qmul_smul_left (a : K) (h k : Fin 4 → K) : qmul f0 f1 f2 (a • h) k = a • qmul f0 f1 f2 h k := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

theorem qmul_smul_right (a : K) (h k : Fin 4 → K) : qmul f0 f1 f2 h (a • k) = a • qmul f0 f1 f2 h k := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

theorem qmul_add_right (h k k' : Fin 4 → K) :
    qmul f0 f1 f2 h (k + k') = qmul f0 f1 f2 h k + qmul f0 f1 f2 h k' := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

theorem qmul_sub_right (h k k' : Fin 4 → K) :
    qmul f0 f1 f2 h (k - k') = qmul f0 f1 f2 h k - qmul f0 f1 f2 h k' := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

omit [Field K] in
theorem qconj_smul' {R : Type*} [CommRing R] (a : R) (h : Fin 4 → R) : qconj (a • h) = a • qconj h := by
  funext i
  fin_cases i <;> simp [qconj]

/-! ## θ-conjugation -/

theorem thetaInv_theta (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (c : Fin 4 → K) :
    thetaInv f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (theta f0 f1 f2 c) = c := by
  funext i
  fin_cases i <;> simp [thetaInv, theta] <;> field_simp

theorem theta_thetaInv' (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (y : Fin 4 → K) :
    theta f0 f1 f2 (thetaInv f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ y) = y := by
  funext i
  fin_cases i <;> simp [thetaInv, theta] <;> field_simp

omit [Field K] in
theorem theta_add' {R : Type*} [CommRing R] (g0 g1 g2 : R) (c c' : Fin 4 → R) :
    theta g0 g1 g2 (c + c') = theta g0 g1 g2 c + theta g0 g1 g2 c' := by
  funext i
  fin_cases i <;> simp [theta] <;> ring

omit [Field K] in
theorem theta_sub' {R : Type*} [CommRing R] (g0 g1 g2 : R) (c c' : Fin 4 → R) :
    theta g0 g1 g2 (c - c') = theta g0 g1 g2 c - theta g0 g1 g2 c' := by
  funext i
  fin_cases i <;> simp [theta] <;> ring

omit [Field K] in
theorem thetaInv_add' {R : Type*} [CommRing R] (a0 a1 a2 a3 : R) (y y' : Fin 4 → R) :
    thetaInv a0 a1 a2 a3 (y + y') = thetaInv a0 a1 a2 a3 y + thetaInv a0 a1 a2 a3 y' := by
  funext i
  fin_cases i <;> simp [thetaInv] <;> ring

/-- The θ-conjugated left multiplication by the pure quaternion `u`. -/
def blockAdLeft (u : Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  thetaInvMat f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ * lmat f0 f1 f2 (pureQuat u) * thetaMat f0 f1 f2

/-- The θ-conjugated negative right multiplication by the pure quaternion `v`. -/
def blockAdRight (v : Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  -(thetaInvMat f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ * rmat f0 f1 f2 (pureQuat v) * thetaMat f0 f1 f2)

/-- The Cayley coordinate `X(u, v)` of `Φ(κ(u), κ(v))`. -/
def blockCayleyInverse (u v : Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  (1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v)⁻¹ •
    ((1 + pureNorm f0 f1 f2 v) • blockAdLeft f0 f1 f2 u + (1 + pureNorm f0 f1 f2 u) • blockAdRight f0 f1 f2 v)

theorem blockCayleyInverse_mulVec (u v : Fin 3 → K) (c : Fin 4 → K) :
    blockCayleyInverse f0 f1 f2 u v *ᵥ c =
      (1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v)⁻¹ •
        thetaInv f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (blockCayleyGen f0 f1 f2 u v (theta f0 f1 f2 c)) := by
  have hL : blockAdLeft f0 f1 f2 u *ᵥ c =
      thetaInv f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (qmul f0 f1 f2 (pureQuat u) (theta f0 f1 f2 c)) := by
    rw [blockAdLeft, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← theta_eq_mulVec,
      ← qmul_eq_lmat_mulVec, ← thetaInv_eq_mulVec]
  have hR : blockAdRight f0 f1 f2 v *ᵥ c =
      -thetaInv f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (qmul f0 f1 f2 (theta f0 f1 f2 c) (pureQuat v)) := by
    rw [blockAdRight, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← theta_eq_mulVec,
      ← qmul_eq_rmat_mulVec, ← thetaInv_eq_mulVec]
  rw [blockCayleyInverse, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hL, hR]
  congr 1
  funext i
  fin_cases i <;> simp [blockCayleyGen, thetaInv] <;> ring

omit [Field K] in
theorem theta_smul' {R : Type*} [CommRing R] (g0 g1 g2 a : R) (c : Fin 4 → R) :
    theta g0 g1 g2 (a • c) = a • theta g0 g1 g2 c := by
  funext i
  fin_cases i <;> simp [theta] <;> ring

omit [Field K] in
theorem thetaInv_smul' {R : Type*} [CommRing R] (a0 a1 a2 a3 a : R) (y : Fin 4 → R) :
    thetaInv a0 a1 a2 a3 (a • y) = a • thetaInv a0 a1 a2 a3 y := by
  funext i
  fin_cases i <;> simp [thetaInv] <;> ring

/-- The Cayley identity `M (1 − X) = 1 + X` for the matrix `M` of `Φ(κ(u), κ(v))`. -/
theorem conjMatrix_cayleyCoords_mul (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) {u v : Fin 3 → K}
    (hu : 1 + pureNorm f0 f1 f2 u ≠ 0) (hv : 1 + pureNorm f0 f1 f2 v ≠ 0)
    (huv : 1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v ≠ 0) :
    conjMatrix f0 f1 f2 f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (cayleyCoords f0 f1 f2 u) (cayleyCoords f0 f1 f2 v) *
        (1 - blockCayleyInverse f0 f1 f2 u v) =
      1 + blockCayleyInverse f0 f1 f2 u v := by
  suffices hmv : ∀ c, (conjMatrix f0 f1 f2 f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (cayleyCoords f0 f1 f2 u)
      (cayleyCoords f0 f1 f2 v) * (1 - blockCayleyInverse f0 f1 f2 u v)) *ᵥ c =
      (1 + blockCayleyInverse f0 f1 f2 u v) *ᵥ c by
    ext i j
    have := congrFun (hmv (Pi.single j 1)) i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using this
  intro c
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    ← conjCoords_eq_mulVec, blockCayleyInverse_mulVec]
  unfold conjCoords
  rw [theta_sub', theta_smul', theta_thetaInv' f0 f1 f2 hf0 hf1 hf2]
  set s := (1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v)⁻¹ with hs
  set y := theta f0 f1 f2 c with hy
  have key : y - s • blockCayleyGen f0 f1 f2 u v y =
      s • ((1 - pureNorm f0 f1 f2 u * pureNorm f0 f1 f2 v) • y - blockCayleyGen f0 f1 f2 u v y) := by
    rw [smul_sub, smul_smul, hs, inv_mul_cancel₀ huv, one_smul]
  rw [key, cayleyCoords, cayleyCoords]
  simp only [qmul_smul_left, qmul_smul_right, qconj_smul']
  rw [cayley_quat_identity]
  simp only [smul_smul, thetaInv_smul', smul_add, thetaInv_add']
  rw [hy, thetaInv_theta f0 f1 f2 hf0 hf1 hf2]
  congr 1
  · have huv' : 1 - pureNorm f0 f1 f2 v * pureNorm f0 f1 f2 u ≠ 0 := by rwa [mul_comm]
    convert one_smul K c using 2
    rw [hs]
    field_simp
  · congr 1
    field_simp

/-! ## Explicit entries and skew-adjointness -/

theorem blockAdLeft_eq (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (u : Fin 3 → K) :
    blockAdLeft f0 f1 f2 u =
      !![0, f1 * u 0, f2 * u 1, -(f1 * f2 * u 2);
        -(f0 * u 0), 0, f2 * u 2, f0 * f2 * u 1;
        -(f0 * u 1), -(f1 * u 2), 0, -(f0 * f1 * u 0);
        u 2, -(u 1), u 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockAdLeft, thetaInvMat, thetaMat, lmat, thetaInv, theta, qmul, pureQuat, Matrix.mul_apply,
      Fin.sum_univ_four, Pi.single_apply] <;> field_simp

theorem blockAdRight_eq (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (v : Fin 3 → K) :
    blockAdRight f0 f1 f2 v =
      !![0, f1 * v 0, f2 * v 1, f1 * f2 * v 2;
        -(f0 * v 0), 0, f2 * v 2, -(f0 * f2 * v 1);
        -(f0 * v 1), -(f1 * v 2), 0, f0 * f1 * v 0;
        -(v 2), v 1, -(v 0), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockAdRight, thetaInvMat, thetaMat, rmat, thetaInv, theta, qmul, pureQuat, Matrix.mul_apply,
      Fin.sum_univ_four, Pi.single_apply] <;> field_simp

omit [Field K] in
/-- The block form `D = diag(f₀, f₁, f₂, f₀f₁f₂)`. -/
abbrev blockFormDiag {R : Type*} [CommRing R] (g0 g1 g2 : R) : Matrix (Fin 4) (Fin 4) R :=
  diagonal ![g0, g1, g2, g0 * g1 * g2]

theorem blockAdLeft_skew (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (u : Fin 3 → K) :
    (blockAdLeft f0 f1 f2 u)ᵀ * blockFormDiag f0 f1 f2 = -(blockFormDiag f0 f1 f2 * blockAdLeft f0 f1 f2 u) := by
  rw [blockAdLeft_eq f0 f1 f2 hf0 hf1 hf2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blockAdRight_skew (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (v : Fin 3 → K) :
    (blockAdRight f0 f1 f2 v)ᵀ * blockFormDiag f0 f1 f2 = -(blockFormDiag f0 f1 f2 * blockAdRight f0 f1 f2 v) := by
  rw [blockAdRight_eq f0 f1 f2 hf0 hf1 hf2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blockCayleyInverse_skew (hf0 : f0 ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (u v : Fin 3 → K) :
    (blockCayleyInverse f0 f1 f2 u v)ᵀ * blockFormDiag f0 f1 f2 =
      -(blockFormDiag f0 f1 f2 * blockCayleyInverse f0 f1 f2 u v) := by
  unfold blockCayleyInverse
  simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_smul,
    Matrix.mul_add, blockAdLeft_skew f0 f1 f2 hf0 hf1 hf2, blockAdRight_skew f0 f1 f2 hf0 hf1 hf2, smul_neg]
  rw [← neg_add, smul_neg]

end BlockConjugationCoordinates
