import SMSFormula.Applications.Examples.A4FiveSetup
import SMSFormula.FiniteOrthogonalGroupIdentityOrder

/-! Actual nondegenerate block and symmetric derivative fibers for A4 at five. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance a4FiveBlockPrime : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev A4FiveMatrix := Matrix (Fin 3) (Fin 3) (ZMod 5)

def a4FiveGram : A4FiveMatrix := Matrix.diagonal ![2,6,12]

def a4FiveOrthogonalChangeMatrix : A4FiveMatrix := !![2,0,2; 0,1,0; 2,0,-2]

theorem a4FiveOrthogonalChangeMatrix_unit : IsUnit a4FiveOrthogonalChangeMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (by decide)

def a4FiveOrthogonalChange : Matrix.GeneralLinearGroup (Fin 3) (ZMod 5) :=
  a4FiveOrthogonalChangeMatrix_unit.unit

theorem a4FiveOrthogonalChange_coe :
    (a4FiveOrthogonalChange : A4FiveMatrix) = a4FiveOrthogonalChangeMatrix :=
  a4FiveOrthogonalChangeMatrix_unit.unit_spec

theorem a4FiveGram_congr_identity :
    (a4FiveOrthogonalChange : A4FiveMatrix).transpose * a4FiveGram *
      (a4FiveOrthogonalChange : A4FiveMatrix) = 1 := by
  rw [a4FiveOrthogonalChange_coe]
  decide

theorem a4Five_orthogonal_group_card : Nat.card (finiteGramOrthogonalGroup a4FiveGram) = 240 := by
  rw [natCard_finiteGramOrthogonalGroup_eq_of_congr a4FiveGram 1 a4FiveOrthogonalChange
    a4FiveGram_congr_identity]
  have h := natCard_oddIdentityOrthogonalGroup_eq_closedExpression
    (K := ZMod 5) (by rw [ZMod.ringChar_zmod_n]; decide) (by norm_num [Nat.card_eq_fintype_card]) 1 (by decide)
  simpa [oddIdentityOrthogonalOrderExpression, finiteOrthogonalOrderEulerProduct,
    Nat.card_eq_fintype_card] using h

def a4FiveSymmetricFiber (S : A4FiveMatrix) :=
  {E : A4FiveMatrix // E + E.transpose = S}

def a4FiveSymmetricLift (S : A4FiveMatrix) (t : ZMod 5 × ZMod 5 × ZMod 5) : A4FiveMatrix :=
  !![3*S 0 0, t.1, t.2.1;
    S 1 0-t.1, 3*S 1 1, t.2.2;
    S 2 0-t.2.1, S 2 1-t.2.2, 3*S 2 2]

theorem a4FiveSymmetricLift_mem (S : A4FiveMatrix) (hS : S.IsSymm)
    (t : ZMod 5 × ZMod 5 × ZMod 5) :
    a4FiveSymmetricLift S t + (a4FiveSymmetricLift S t).transpose = S := by
  have h01 : S 0 1 = S 1 0 := (hS.apply 0 1).symm
  have h02 : S 0 2 = S 2 0 := (hS.apply 0 2).symm
  have h12 : S 1 2 = S 2 1 := (hS.apply 1 2).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a4FiveSymmetricLift, Matrix.transpose_apply, h01, h02, h12] <;>
    ring_nf <;> simp only [show (6 : ZMod 5) = 1 by decide, mul_one]

def a4FiveSymmetricFiberEquiv (S : A4FiveMatrix) (hS : S.IsSymm) :
    a4FiveSymmetricFiber S ≃ (ZMod 5 × ZMod 5 × ZMod 5) where
  toFun E := (E.1 0 1,E.1 0 2,E.1 1 2)
  invFun t := ⟨a4FiveSymmetricLift S t,a4FiveSymmetricLift_mem S hS t⟩
  left_inv E := by
    apply Subtype.ext
    have he (i j : Fin 3) : E.1 i j + E.1 j i = S i j := congrFun (congrFun E.2 i) j
    have hd (i : Fin 3) : 3*S i i = E.1 i i := by
      calc
        _ = 3*(E.1 i i + E.1 i i) := by rw [he i i]
        _ = E.1 i i := by
          ring_nf
          rw [show (6 : ZMod 5) = 1 by decide, mul_one]
    ext i j
    fin_cases i <;> fin_cases j
    · exact hd 0
    · rfl
    · rfl
    · change S 1 0 - E.1 0 1 = E.1 1 0
      linear_combination -he 1 0
    · exact hd 1
    · rfl
    · change S 2 0 - E.1 0 2 = E.1 2 0
      linear_combination -he 2 0
    · change S 2 1 - E.1 1 2 = E.1 2 1
      linear_combination -he 2 1
    · exact hd 2
  right_inv t := by
    simp [a4FiveSymmetricLift]

theorem a4FiveSymmetricFiber_card (S : A4FiveMatrix) (hS : S.IsSymm) :
    Nat.card (a4FiveSymmetricFiber S) = 125 := by
  rw [Nat.card_congr (a4FiveSymmetricFiberEquiv S hS)]
  simp [Nat.card_eq_fintype_card]


def a4FiveDerivativeFiber (C : A4FiveMatrixˣ) (S : A4FiveMatrix) :=
  {E : A4FiveMatrix // (C : A4FiveMatrix)*E + ((C : A4FiveMatrix)*E).transpose = S}

def a4FiveDerivativeFiberEquiv (C : A4FiveMatrixˣ) (S : A4FiveMatrix) :
    a4FiveDerivativeFiber C S ≃ a4FiveSymmetricFiber S where
  toFun E := ⟨(C : A4FiveMatrix)*E.1,E.2⟩
  invFun Y := ⟨((C⁻¹ : A4FiveMatrixˣ) : A4FiveMatrix)*Y.1,by
    simpa [← Matrix.mul_assoc] using Y.2⟩
  left_inv E := by
    apply Subtype.ext
    change ((C⁻¹ : A4FiveMatrixˣ) : A4FiveMatrix)*((C : A4FiveMatrix)*E.1) = E.1
    simp [← Matrix.mul_assoc]
  right_inv Y := by
    apply Subtype.ext
    change (C : A4FiveMatrix)*(((C⁻¹ : A4FiveMatrixˣ) : A4FiveMatrix)*Y.1) = Y.1
    simp [← Matrix.mul_assoc]

theorem a4FiveDerivativeFiber_card (C : A4FiveMatrixˣ) (S : A4FiveMatrix) (hS : S.IsSymm) :
    Nat.card (a4FiveDerivativeFiber C S) = 125 := by
  rw [Nat.card_congr (a4FiveDerivativeFiberEquiv C S)]
  exact a4FiveSymmetricFiber_card S hS

theorem a4FiveDerivativeCoefficient_unit (A : finiteGramOrthogonalGroup a4FiveGram) :
    IsUnit ((A.1 : A4FiveMatrix).transpose * a4FiveGram) := by
  have hA : IsUnit (A.1 : A4FiveMatrix) := A.1.isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
  rw [Matrix.det_mul, Matrix.det_transpose]
  exact hA.mul (isUnit_iff_ne_zero.mpr (by decide))

def a4FiveDerivativeCoefficient (A : finiteGramOrthogonalGroup a4FiveGram) : A4FiveMatrixˣ :=
  (a4FiveDerivativeCoefficient_unit A).unit

theorem a4FiveDerivativeCoefficient_coe (A : finiteGramOrthogonalGroup a4FiveGram) :
    (a4FiveDerivativeCoefficient A : A4FiveMatrix) =
      (A.1 : A4FiveMatrix).transpose * a4FiveGram :=
  (a4FiveDerivativeCoefficient_unit A).unit_spec


def a4FiveIntegerGram : Matrix (Fin 3) (Fin 3) ℤ := Matrix.diagonal ![2,6,12]

def a4FiveIntegerBlock (A : finiteGramOrthogonalGroup a4FiveGram) :
    Matrix (Fin 3) (Fin 3) ℤ := (A.1 : A4FiveMatrix).map (fun z => (z.val : ℤ))

def a4FiveLiftError (A : finiteGramOrthogonalGroup a4FiveGram) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  a4FiveIntegerGram - (a4FiveIntegerBlock A).transpose * a4FiveIntegerGram * a4FiveIntegerBlock A

theorem a4FiveIntegerBlock_reduces (A : finiteGramOrthogonalGroup a4FiveGram) :
    (a4FiveIntegerBlock A).map (Int.castRingHom (ZMod 5)) = (A.1 : A4FiveMatrix) := by
  ext i j
  change (((((A.1 : A4FiveMatrix) i j).val : ℤ)) : ZMod 5) = _
  simp

theorem a4FiveLiftError_dvd (A : finiteGramOrthogonalGroup a4FiveGram) (i j : Fin 3) :
    (5 : ℤ) ∣ a4FiveLiftError A i j := by
  have ha : (A.1 : A4FiveMatrix).transpose * a4FiveGram * (A.1 : A4FiveMatrix) =
      a4FiveGram := A.2
  have h : (a4FiveLiftError A).map (Int.castRingHom (ZMod 5)) = 0 := by
    have hG : a4FiveIntegerGram.map (Int.castRingHom (ZMod 5)) = a4FiveGram := by decide
    rw [a4FiveLiftError, Matrix.map_sub _ (by
      intro a b
      exact map_sub (Int.castRingHom (ZMod 5)) a b)]
    simp only [Matrix.map_mul, Matrix.transpose_map, a4FiveIntegerBlock_reduces,
      hG, ha, sub_self]
  have hij := congrArg (fun M : A4FiveMatrix => M i j) h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hij

def a4FiveLiftTarget (A : finiteGramOrthogonalGroup a4FiveGram) (g : Fin 3 → ZMod 5) :
    A4FiveMatrix :=
  (a4FiveLiftError A).map (fun z => ((z/5 : ℤ) : ZMod 5)) -
    (Matrix.of fun i j => 4*g i*g j)

theorem a4FiveLiftTarget_symm (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) : (a4FiveLiftTarget A g).IsSymm := by
  have hG : a4FiveIntegerGram.transpose = a4FiveIntegerGram := by decide
  have he : (a4FiveLiftError A).transpose = a4FiveLiftError A := by
    simp only [a4FiveLiftError, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hG, Matrix.mul_assoc]
  change (a4FiveLiftTarget A g).transpose = a4FiveLiftTarget A g
  rw [a4FiveLiftTarget, Matrix.transpose_sub, ← Matrix.transpose_map, he]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  ring

def a4FiveAffineLiftData :=
  Σ A : finiteGramOrthogonalGroup a4FiveGram,
    Σ g : Fin 3 → ZMod 5, Σ _w : {w : ZMod 5 // w^2=1},
      a4FiveDerivativeFiber (a4FiveDerivativeCoefficient A) (a4FiveLiftTarget A g)

def a4FiveAffineFiberEquiv (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) :
    a4FiveDerivativeFiber (a4FiveDerivativeCoefficient A) (a4FiveLiftTarget A g) ≃
      (ZMod 5 × ZMod 5 × ZMod 5) :=
  (a4FiveDerivativeFiberEquiv _ _).trans
    (a4FiveSymmetricFiberEquiv _ (a4FiveLiftTarget_symm A g))

def a4FiveAffineLiftDataEquiv : a4FiveAffineLiftData ≃
    finiteGramOrthogonalGroup a4FiveGram × (Fin 3 → ZMod 5) ×
      {w : ZMod 5 // w^2=1} × (ZMod 5 × ZMod 5 × ZMod 5) where
  toFun t := (t.1,t.2.1,t.2.2.1,a4FiveAffineFiberEquiv t.1 t.2.1 t.2.2.2)
  invFun t := ⟨t.1,t.2.1,t.2.2.1,(a4FiveAffineFiberEquiv t.1 t.2.1).symm t.2.2.2⟩
  left_inv t := by
    rcases t with ⟨A,g,w,E⟩
    change (⟨A,g,w,(a4FiveAffineFiberEquiv A g).symm
      (a4FiveAffineFiberEquiv A g E)⟩ : a4FiveAffineLiftData) = ⟨A,g,w,E⟩
    rw [Equiv.symm_apply_apply]
  right_inv t := by
    rcases t with ⟨A,g,w,e⟩
    change (A,g,w,a4FiveAffineFiberEquiv A g ((a4FiveAffineFiberEquiv A g).symm e)) = (A,g,w,e)
    rw [Equiv.apply_symm_apply]

theorem a4Five_last_roots_card : Nat.card {w : ZMod 5 // w^2=1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Parameter count only. The native family equivalence remains a separate proof. -/
theorem a4FiveAffineLiftData_card : Nat.card a4FiveAffineLiftData = 7500000 := by
  rw [Nat.card_congr a4FiveAffineLiftDataEquiv]
  simp only [Nat.card_prod, a4Five_orthogonal_group_card, a4Five_last_roots_card]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end MassFormulaReleaseExamples
