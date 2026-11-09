import SMSFormula.SkewAdjointBaseChange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Algebraic p-adic Cayley coordinates

This file defines the ambient p-adic Cayley transform

`X ↦ (1 + X) * (1 - X)⁻¹`

and its inverse formula

`g ↦ (g + 1)⁻¹ * (g - 1)`.

The source and inverse domains explicitly require `1 - X` and `g + 1` to be
matrix units. Characteristic zero makes the scalar matrix `2` a unit, which
gives both domain transfers and the exact forward/inverse identities. The
forward formula is also exposed on the rationally transported skew-adjoint
model.

No claim is made here that the forward image is orthogonal or determinant
one, and no p-adic group chart or group measure is constructed.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ambient source on which `1 - X` is invertible. -/
def padicCayleySource (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix ι ι ℚ_[p]) :=
  {X | IsUnit (1 - X)}

/-- The source condition restricted to the transported skew-adjoint model. -/
def skewAdjointPadicCayleySource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
  {X | (X : Matrix ι ι ℚ_[p]) ∈ padicCayleySource p}

/-- The ambient inverse domain on which `g + 1` is invertible. -/
def padicCayleyInverseDomain (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix ι ι ℚ_[p]) :=
  {g | IsUnit (g + 1)}

/-- The ambient p-adic Cayley forward formula. -/
def padicCayleyForwardMatrix (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix ι ι ℚ_[p]) : Matrix ι ι ℚ_[p] :=
  (1 + X) * (1 - X)⁻¹

/-- The Cayley forward formula on the transported skew-adjoint model. -/
def skewAdjointPadicCayleyForwardMatrix
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Matrix ι ι ℚ_[p] :=
  padicCayleyForwardMatrix p X

/-- The ambient p-adic Cayley inverse formula. -/
def padicCayleyInverseMatrix (p : ℕ) [Fact (Nat.Prime p)]
    (g : Matrix ι ι ℚ_[p]) : Matrix ι ι ℚ_[p] :=
  (g + 1)⁻¹ * (g - 1)

/-- The central scalar matrix `2`, retained explicitly in the domain
identities. -/
def padicCayleyTwoMatrix (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix ι ι ℚ_[p] :=
  Matrix.scalar ι 2

private theorem padicCayley_two_isUnit (p : ℕ) [Fact (Nat.Prime p)] :
    IsUnit (padicCayleyTwoMatrix (ι := ι) p) := by
  have htwo : IsUnit (2 : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  exact htwo.map (Matrix.scalar ι)

private theorem padicCayley_nonsing_inv_commute
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    (1 - X)⁻¹ * X = X * (1 - X)⁻¹ := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  apply hX.mul_left_cancel
  calc
    A * (A⁻¹ * X) = X := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAdet, one_mul]
    _ = A * (X * A⁻¹) := by
      rw [← Matrix.mul_assoc]
      have hcomm : A * X = X * A := by
        dsimp [A]
        noncomm_ring
      rw [hcomm, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAdet, mul_one]

/-- The forward inverse-domain matrix is twice the inverse source matrix. -/
theorem padicCayleyForwardMatrix_add_one
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    padicCayleyForwardMatrix p X + 1 =
      padicCayleyTwoMatrix (ι := ι) p * (1 - X)⁻¹ := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  change B * A⁻¹ + 1 = padicCayleyTwoMatrix p * A⁻¹
  have hBA : B + A = padicCayleyTwoMatrix (ι := ι) p := by
    calc
      B + A = (2 : ℚ_[p]) • (1 : Matrix ι ι ℚ_[p]) := by
        dsimp [A, B]
        module
      _ = padicCayleyTwoMatrix (ι := ι) p := by
        rw [smul_eq_diagonal_mul, Matrix.mul_one]
        rfl
  calc
    B * A⁻¹ + 1 = B * A⁻¹ + A * A⁻¹ := by
      rw [Matrix.mul_nonsing_inv A hAdet]
    _ = (B + A) * A⁻¹ := (add_mul B A A⁻¹).symm
    _ = padicCayleyTwoMatrix p * A⁻¹ := by rw [hBA]

/-- The corresponding numerator identity for the forward map. -/
theorem padicCayleyForwardMatrix_sub_one
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    padicCayleyForwardMatrix p X - 1 =
      padicCayleyTwoMatrix (ι := ι) p * X * (1 - X)⁻¹ := by
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  change B * A⁻¹ - 1 = padicCayleyTwoMatrix p * X * A⁻¹
  have hBA : B - A = padicCayleyTwoMatrix (ι := ι) p * X := by
    calc
      B - A = (2 : ℚ_[p]) • X := by
        dsimp [A, B]
        module
      _ = padicCayleyTwoMatrix (ι := ι) p * X := by
        rw [smul_eq_diagonal_mul]
        rfl
  calc
    B * A⁻¹ - 1 = B * A⁻¹ - A * A⁻¹ := by
      rw [Matrix.mul_nonsing_inv A hAdet]
    _ = (B - A) * A⁻¹ := (sub_mul B A A⁻¹).symm
    _ = padicCayleyTwoMatrix p * X * A⁻¹ := by rw [hBA]

/-- The forward image satisfies the cross-multiplied inverse identity. -/
theorem padicCayleyForwardMatrix_cross
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    (padicCayleyForwardMatrix p X + 1) * X =
      padicCayleyForwardMatrix p X - 1 := by
  rw [padicCayleyForwardMatrix_add_one p X hX,
    padicCayleyForwardMatrix_sub_one p X hX]
  rw [Matrix.mul_assoc, padicCayley_nonsing_inv_commute p X hX,
    ← Matrix.mul_assoc]

/-- The forward map carries its source into the inverse domain. -/
theorem padicCayleyForwardMatrix_mem_inverseDomain
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    padicCayleyForwardMatrix p X ∈ padicCayleyInverseDomain p := by
  change IsUnit (padicCayleyForwardMatrix p X + 1)
  rw [padicCayleyForwardMatrix_add_one p X hX]
  exact (padicCayley_two_isUnit p).mul
    (Matrix.isUnit_nonsing_inv_iff.mpr hX)

/-- Applying the inverse formula after the forward formula recovers `X`. -/
theorem padicCayleyInverseMatrix_forward
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    padicCayleyInverseMatrix p (padicCayleyForwardMatrix p X) = X := by
  have hC := padicCayleyForwardMatrix_mem_inverseDomain p X hX
  have hCdet : IsUnit (padicCayleyForwardMatrix p X + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hC
  rw [padicCayleyInverseMatrix, ← padicCayleyForwardMatrix_cross p X hX,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCdet, one_mul]

/-- The inverse formula's source matrix is the inverse target matrix times
the scalar matrix `2`. -/
theorem one_sub_padicCayleyInverseMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    1 - padicCayleyInverseMatrix p g =
      (g + 1)⁻¹ * padicCayleyTwoMatrix (ι := ι) p := by
  have hCdet : IsUnit (g + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hg
  rw [padicCayleyInverseMatrix]
  calc
    1 - (g + 1)⁻¹ * (g - 1) =
        (g + 1)⁻¹ * (g + 1) - (g + 1)⁻¹ * (g - 1) := by
      rw [Matrix.nonsing_inv_mul _ hCdet]
    _ = (g + 1)⁻¹ * ((g + 1) - (g - 1)) :=
      (mul_sub (g + 1)⁻¹ (g + 1) (g - 1)).symm
    _ = (g + 1)⁻¹ * padicCayleyTwoMatrix p := by
      congr 1
      calc
        (g + 1) - (g - 1) =
            (2 : ℚ_[p]) • (1 : Matrix ι ι ℚ_[p]) := by module
        _ = padicCayleyTwoMatrix (ι := ι) p := by
          rw [smul_eq_diagonal_mul, Matrix.mul_one]
          rfl

/-- The inverse formula carries the inverse domain back into the source. -/
theorem padicCayleyInverseMatrix_mem_source
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    padicCayleyInverseMatrix p g ∈ padicCayleySource p := by
  change IsUnit (1 - padicCayleyInverseMatrix p g)
  rw [one_sub_padicCayleyInverseMatrix p g hg]
  exact (Matrix.isUnit_nonsing_inv_iff.mpr hg).mul
    (padicCayley_two_isUnit p)

/-- The inverse formula satisfies the cross-multiplied forward identity. -/
theorem padicCayleyInverseMatrix_cross
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    (g + 1) * padicCayleyInverseMatrix p g = g - 1 := by
  have hCdet : IsUnit (g + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hg
  rw [padicCayleyInverseMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hCdet, one_mul]

/-- Applying the forward formula after the inverse formula recovers `g`. -/
theorem padicCayleyForwardMatrix_inverse
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    padicCayleyForwardMatrix p (padicCayleyInverseMatrix p g) = g := by
  let X := padicCayleyInverseMatrix p g
  let A : Matrix ι ι ℚ_[p] := 1 - X
  let B : Matrix ι ι ℚ_[p] := 1 + X
  have hX : X ∈ padicCayleySource p :=
    padicCayleyInverseMatrix_mem_source p g hg
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hcross : (g + 1) * X = g - 1 :=
    padicCayleyInverseMatrix_cross p g hg
  have hgX : g * X = g - 1 - X := by
    calc
      g * X = (g + 1) * X - X := by noncomm_ring
      _ = g - 1 - X := by rw [hcross]
  have hrel : g * A = B := by
    dsimp [A, B]
    rw [mul_sub, mul_one, hgX]
    noncomm_ring
  change B * A⁻¹ = g
  rw [← hrel]
  exact Matrix.mul_nonsing_inv_cancel_right A g hAdet

@[simp]
theorem skewAdjointPadicCayleyForwardMatrix_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyForwardMatrix F p X =
      padicCayleyForwardMatrix p (X : Matrix ι ι ℚ_[p]) :=
  rfl

end Matrix
