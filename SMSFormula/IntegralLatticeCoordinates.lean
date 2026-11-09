import SMSFormula.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The Schulze--Pillot symmetric bilinear value
`B(x,y) = xᵀ F y`, whose diagonal value is the stored quadratic form.

This is half of the polar bilinear form attached to `q(x) = xᵀ F x`; it is the
bilinear form whose determinant is `pairingDeterminant = det(F) = det_B`. -/
def bilinearFormValue (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ) : ℤ :=
  dotProduct x (L.pairingMatrix.mulVec y)

/-- Schulze--Pillot's bilinear form is symmetric. -/
lemma bilinearFormValue_comm (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ) :
    L.bilinearFormValue x y = L.bilinearFormValue y x := by
  calc
    L.bilinearFormValue x y =
        ∑ i, ∑ j, x i * L.pairingMatrix i j * y j := by
          simp [bilinearFormValue, dotProduct, Matrix.mulVec,
            Finset.mul_sum, mul_assoc]
    _ = ∑ j, ∑ i, x i * L.pairingMatrix i j * y j := by
          rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, y j * L.pairingMatrix j i * x i := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [← L.form_symm.apply i j]
          ring
    _ = L.bilinearFormValue y x := by
          simp [bilinearFormValue, dotProduct, Matrix.mulVec,
            Finset.mul_sum, mul_assoc]

/-- A unimodular integer matrix acts as a linear equivalence on the ambient
coordinate lattice. -/
noncomputable def intMatrixLinearEquivOfIsUnit
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) := by
  have hdet : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hU
  refine LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' U⁻¹) ?_ ?_
  · rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv U hdet]
    ext v i
    simp
  · rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul U hdet]
    ext v i
    simp

/-- The quotient of the full coordinate lattice by the top submodule has one
element. -/
lemma nat_card_quotient_top_integral_coordinates :
    Nat.card ((Fin n → ℤ) ⧸ (⊤ : Submodule ℤ (Fin n → ℤ))) = 1 := by
  haveI : Subsingleton ((Fin n → ℤ) ⧸ (⊤ : Submodule ℤ (Fin n → ℤ))) := by
    refine ⟨?_⟩
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    change (Submodule.Quotient.mk x :
        (Fin n → ℤ) ⧸ (⊤ : Submodule ℤ (Fin n → ℤ))) =
      Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq]
    simp
  haveI : Fintype ((Fin n → ℤ) ⧸ (⊤ : Submodule ℤ (Fin n → ℤ))) :=
    Fintype.ofSubsingleton 0
  simp [Nat.card_eq_fintype_card]

end PositiveDefiniteIntegralLattice

end
