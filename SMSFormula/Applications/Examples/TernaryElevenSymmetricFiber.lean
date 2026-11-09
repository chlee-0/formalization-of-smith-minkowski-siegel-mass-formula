import SMSFormula.Applications.Examples.Inputs
import SMSFormula.StandardAxiomsGuard

/-! The symmetric derivative fiber used by the ternary block lift at 11. -/

noncomputable section

namespace MassFormulaReleaseExamples

open Matrix

abbrev TernaryElevenMatrix := Matrix (Fin 2) (Fin 2) (ZMod 11)

def ternaryElevenSymmetricFiber (S : TernaryElevenMatrix) :=
  {Y : TernaryElevenMatrix // Y + Y.transpose = S}

def ternaryElevenSymmetricLift (S : TernaryElevenMatrix) (t : ZMod 11) :
    TernaryElevenMatrix :=
  !![S 0 0 * 6, t; S 0 1 - t, S 1 1 * 6]

theorem ternaryElevenSymmetricLift_mem (S : TernaryElevenMatrix) (hS : S.IsSymm)
    (t : ZMod 11) :
    ternaryElevenSymmetricLift S t + (ternaryElevenSymmetricLift S t).transpose = S := by
  have hs : S 1 0 = S 0 1 := congrArg (fun M : TernaryElevenMatrix => M 0 1) hS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ternaryElevenSymmetricLift, hs] <;> ring_nf <;>
    rw [show (12 : ZMod 11) = 1 by decide, mul_one]

def ternaryElevenSymmetricFiberEquiv (S : TernaryElevenMatrix) (hS : S.IsSymm) :
    ternaryElevenSymmetricFiber S ≃ ZMod 11 where
  toFun Y := Y.1 0 1
  invFun t := ⟨ternaryElevenSymmetricLift S t, ternaryElevenSymmetricLift_mem S hS t⟩
  left_inv Y := by
    apply Subtype.ext
    have h00 := congrArg (fun M : TernaryElevenMatrix => M 0 0) Y.2
    have h01 := congrArg (fun M : TernaryElevenMatrix => M 0 1) Y.2
    have h11 := congrArg (fun M : TernaryElevenMatrix => M 1 1) Y.2
    change Y.1 0 0 + Y.1 0 0 = S 0 0 at h00
    change Y.1 0 1 + Y.1 1 0 = S 0 1 at h01
    change Y.1 1 1 + Y.1 1 1 = S 1 1 at h11
    have h6 : (2 : ZMod 11) * 6 = 1 := by decide
    ext i j
    fin_cases i <;> fin_cases j
    · change S 0 0 * 6 = Y.1 0 0
      linear_combination -6 * h00 + Y.1 0 0 * h6
    · rfl
    · change S 0 1 - Y.1 0 1 = Y.1 1 0
      linear_combination -h01
    · change S 1 1 * 6 = Y.1 1 1
      linear_combination -6 * h11 + Y.1 1 1 * h6
  right_inv _ := rfl

theorem ternaryElevenSymmetricFiber_card (S : TernaryElevenMatrix) (hS : S.IsSymm) :
    Nat.card (ternaryElevenSymmetricFiber S) = 11 := by
  rw [Nat.card_congr (ternaryElevenSymmetricFiberEquiv S hS), Nat.card_eq_fintype_card]
  exact ZMod.card 11

def ternaryElevenDerivativeFiber (C : TernaryElevenMatrixˣ) (S : TernaryElevenMatrix) :=
  {X : TernaryElevenMatrix // (C : TernaryElevenMatrix) * X +
    ((C : TernaryElevenMatrix) * X).transpose = S}

def ternaryElevenDerivativeFiberEquiv (C : TernaryElevenMatrixˣ)
    (S : TernaryElevenMatrix) :
    ternaryElevenDerivativeFiber C S ≃ ternaryElevenSymmetricFiber S where
  toFun X := ⟨(C : TernaryElevenMatrix) * X.1, X.2⟩
  invFun Y := ⟨((C⁻¹ : TernaryElevenMatrixˣ) : TernaryElevenMatrix) * Y.1, by
    simpa [← Matrix.mul_assoc] using Y.2⟩
  left_inv X := by
    apply Subtype.ext
    change ((C⁻¹ : TernaryElevenMatrixˣ) : TernaryElevenMatrix) *
      ((C : TernaryElevenMatrix) * X.1) = X.1
    simp [← Matrix.mul_assoc]
  right_inv Y := by
    apply Subtype.ext
    change (C : TernaryElevenMatrix) *
      (((C⁻¹ : TernaryElevenMatrixˣ) : TernaryElevenMatrix) * Y.1) = Y.1
    simp [← Matrix.mul_assoc]

theorem ternaryElevenDerivativeFiber_card (C : TernaryElevenMatrixˣ)
    (S : TernaryElevenMatrix) (hS : S.IsSymm) :
    Nat.card (ternaryElevenDerivativeFiber C S) = 11 := by
  rw [Nat.card_congr (ternaryElevenDerivativeFiberEquiv C S)]
  exact ternaryElevenSymmetricFiber_card S hS

end MassFormulaReleaseExamples
