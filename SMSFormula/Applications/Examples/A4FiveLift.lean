import SMSFormula.Applications.Examples.A4FiveResidueLayer

/-! The actual affine matrix lift for the diagonal A4 model at five. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance a4FiveLiftPrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def a4FiveWorkingGram : Matrix (Fin 4) (Fin 4) (ZMod 25) := Matrix.diagonal ![2,6,12,20]

def a4FiveWeightedPair (v w : Fin 3 → ZMod 25) : ZMod 25 :=
  2*v 0*w 0 + 6*v 1*w 1 + 12*v 2*w 2

theorem a4FiveWeightedPair_affine (a b x y : Fin 3 → ZMod 5) :
    a4FiveWeightedPair (fun i => a4FiveLift (a i)+a4FiveEmbed (x i))
      (fun i => a4FiveLift (b i)+a4FiveEmbed (y i)) =
    a4FiveWeightedPair (fun i => a4FiveLift (a i)) (fun i => a4FiveLift (b i)) +
      a4FiveEmbed (2*(a 0*y 0+x 0*b 0) + 6*(a 1*y 1+x 1*b 1) +
        12*(a 2*y 2+x 2*b 2)) := by
  have h2 := a4Five_weighted_affine_pair 2 (a 0) (b 0) (x 0) (y 0)
  have h6 := a4Five_weighted_affine_pair 6 (a 1) (b 1) (x 1) (y 1)
  have h12 := a4Five_weighted_affine_pair 12 (a 2) (b 2) (x 2) (y 2)
  norm_num only [Int.cast_ofNat] at h2 h6 h12
  unfold a4FiveWeightedPair
  rw [h2,h6,h12]
  simp only [map_add]
  ring

theorem a4Five_base_pair (A : finiteGramOrthogonalGroup a4FiveGram) (i j : Fin 3) :
    a4FiveWeightedPair (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k i))
      (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k j)) =
    (a4FiveIntegerGram i j : ZMod 25) -
      a4FiveEmbed ((a4FiveLiftError A i j/5 : ℤ) : ZMod 5) := by
  have hi : a4FiveLiftError A i j = a4FiveIntegerGram i j -
      (2*a4FiveIntegerBlock A 0 i*a4FiveIntegerBlock A 0 j +
       6*a4FiveIntegerBlock A 1 i*a4FiveIntegerBlock A 1 j +
       12*a4FiveIntegerBlock A 2 i*a4FiveIntegerBlock A 2 j) := by
    simp [a4FiveLiftError,a4FiveIntegerGram,Matrix.mul_apply,Fin.sum_univ_succ]
    ring_nf
  have hc := congrArg (Int.cast : ℤ → ZMod 25) hi
  push_cast at hc
  have hc' : (a4FiveLiftError A i j : ZMod 25) =
      (a4FiveIntegerGram i j : ZMod 25) -
      a4FiveWeightedPair (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k i))
        (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k j)) := hc
  rw [a4Five_dvd_cast _ (a4FiveLiftError_dvd A i j)] at hc'
  linear_combination hc'

theorem a4Five_derivative_entry (A : finiteGramOrthogonalGroup a4FiveGram)
    (E : A4FiveMatrix) (i j : Fin 3) :
    (((a4FiveDerivativeCoefficient A : A4FiveMatrix)*E) +
      ((a4FiveDerivativeCoefficient A : A4FiveMatrix)*E).transpose) i j =
    2*((A.1 : A4FiveMatrix) 0 i*E 0 j+E 0 i*(A.1 : A4FiveMatrix) 0 j) +
    6*((A.1 : A4FiveMatrix) 1 i*E 1 j+E 1 i*(A.1 : A4FiveMatrix) 1 j) +
    12*((A.1 : A4FiveMatrix) 2 i*E 2 j+E 2 i*(A.1 : A4FiveMatrix) 2 j) := by
  simp [a4FiveDerivativeCoefficient_coe,a4FiveGram,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

theorem a4Five_derivative_condition (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5)
    (E : a4FiveDerivativeFiber (a4FiveDerivativeCoefficient A) (a4FiveLiftTarget A g))
    (i j : Fin 3) :
    2*((A.1 : A4FiveMatrix) 0 i*E.1 0 j+E.1 0 i*(A.1 : A4FiveMatrix) 0 j) +
    6*((A.1 : A4FiveMatrix) 1 i*E.1 1 j+E.1 1 i*(A.1 : A4FiveMatrix) 1 j) +
    12*((A.1 : A4FiveMatrix) 2 i*E.1 2 j+E.1 2 i*(A.1 : A4FiveMatrix) 2 j) =
    ((a4FiveLiftError A i j/5 : ℤ) : ZMod 5)-4*g i*g j := by
  rw [← a4Five_derivative_entry, E.2]
  rfl

theorem a4Five_scaled_weight_pair (a b : ZMod 5) :
    (20 : ZMod 25)*a4FiveLift a*a4FiveLift b = a4FiveEmbed (4*a*b) := by
  have h : (20 : ZMod 25) = 4*5 := by decide
  rw [h]
  calc
    _ = 4*((5 : ZMod 25)*a4FiveLift a*a4FiveLift b) := by ring
    _ = 4*a4FiveEmbed (a*b) := by
      rw [a4Five_scaled_pair,a4FiveLift_reduces,a4FiveLift_reduces]
    _ = _ := by
      rw [a4Five_mul_Embed]
      have hr : a4FiveReduction (4 : ZMod 25) = 4 := by decide
      rw [hr]
      congr 1
      ring

theorem a4Five_lift_top_pair (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5)
    (E : a4FiveDerivativeFiber (a4FiveDerivativeCoefficient A) (a4FiveLiftTarget A g))
    (i j : Fin 3) :
    a4FiveWeightedPair
      (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k i)+a4FiveEmbed (E.1 k i))
      (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k j)+a4FiveEmbed (E.1 k j)) +
      20*a4FiveLift (g i)*a4FiveLift (g j) = (a4FiveIntegerGram i j : ZMod 25) := by
  rw [a4FiveWeightedPair_affine,a4Five_base_pair,a4Five_derivative_condition,
    a4Five_scaled_weight_pair,map_sub]
  ring

def a4FiveCrossColumn (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) (w : ZMod 5) : Fin 3 → ZMod 5 :=
  (((a4FiveDerivativeCoefficient A)⁻¹ : A4FiveMatrixˣ) : A4FiveMatrix).mulVec ((-4*w) • g)

theorem a4FiveCrossColumn_spec (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) (w : ZMod 5) :
    ((A.1 : A4FiveMatrix).transpose*a4FiveGram).mulVec (a4FiveCrossColumn A g w) =
      (-4*w) • g := by
  rw [← a4FiveDerivativeCoefficient_coe]
  simp [a4FiveCrossColumn,Matrix.mulVec_mulVec]

theorem a4Five_affine_embed_pair (a x u : ZMod 5) :
    (a4FiveLift a+a4FiveEmbed x)*a4FiveEmbed u = a4FiveEmbed (a*u) := by
  rw [a4Five_mul_Embed,map_add,a4FiveLift_reduces,a4FiveEmbed_reduces,add_zero]

theorem a4Five_embed_pair_zero (u v : ZMod 5) : a4FiveEmbed u*a4FiveEmbed v = 0 := by
  rw [a4FiveEmbed_mul,a4FiveEmbed_reduces,mul_zero,map_zero]


theorem a4FiveWeightedPair_embed (a x u : Fin 3 → ZMod 5) :
    a4FiveWeightedPair (fun i => a4FiveLift (a i)+a4FiveEmbed (x i))
      (fun i => a4FiveEmbed (u i)) =
      a4FiveEmbed (2*a 0*u 0+6*a 1*u 1+12*a 2*u 2) := by
  have h := a4FiveWeightedPair_affine a (fun _ => 0) x u
  have h0 : a4FiveLift 0 = 0 := by decide
  simpa [h0,a4FiveWeightedPair,mul_assoc] using h

theorem a4Five_lift_cross_pair (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) (w : ZMod 5) (E : A4FiveMatrix) (i : Fin 3) :
    a4FiveWeightedPair
      (fun k => a4FiveLift ((A.1 : A4FiveMatrix) k i)+a4FiveEmbed (E k i))
      (fun k => a4FiveEmbed (a4FiveCrossColumn A g w k)) +
      20*a4FiveLift (g i)*a4FiveLift w = 0 := by
  have hc := congr_fun (a4FiveCrossColumn_spec A g w) i
  have hc' : 2*(A.1 : A4FiveMatrix) 0 i*a4FiveCrossColumn A g w 0 +
      6*(A.1 : A4FiveMatrix) 1 i*a4FiveCrossColumn A g w 1 +
      12*(A.1 : A4FiveMatrix) 2 i*a4FiveCrossColumn A g w 2 = -4*w*g i := by
    simpa [a4FiveGram,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      mul_comm,mul_left_comm,mul_assoc,add_assoc] using hc
  rw [a4FiveWeightedPair_embed,a4Five_scaled_weight_pair,← map_add,hc']
  have hz : -4*w*g i+4*g i*w = 0 := by ring
  rw [hz,map_zero]

def a4FiveAffineMatrix (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) (w : ZMod 5) (E : A4FiveMatrix) :
    Matrix (Fin 4) (Fin 4) (ZMod 25) :=
  !![a4FiveLift ((A.1 : A4FiveMatrix) 0 0)+a4FiveEmbed (E 0 0),
     a4FiveLift ((A.1 : A4FiveMatrix) 0 1)+a4FiveEmbed (E 0 1),
     a4FiveLift ((A.1 : A4FiveMatrix) 0 2)+a4FiveEmbed (E 0 2),
     a4FiveEmbed (a4FiveCrossColumn A g w 0);
     a4FiveLift ((A.1 : A4FiveMatrix) 1 0)+a4FiveEmbed (E 1 0),
     a4FiveLift ((A.1 : A4FiveMatrix) 1 1)+a4FiveEmbed (E 1 1),
     a4FiveLift ((A.1 : A4FiveMatrix) 1 2)+a4FiveEmbed (E 1 2),
     a4FiveEmbed (a4FiveCrossColumn A g w 1);
     a4FiveLift ((A.1 : A4FiveMatrix) 2 0)+a4FiveEmbed (E 2 0),
     a4FiveLift ((A.1 : A4FiveMatrix) 2 1)+a4FiveEmbed (E 2 1),
     a4FiveLift ((A.1 : A4FiveMatrix) 2 2)+a4FiveEmbed (E 2 2),
     a4FiveEmbed (a4FiveCrossColumn A g w 2);
     a4FiveLift (g 0),a4FiveLift (g 1),a4FiveLift (g 2),a4FiveLift w]

theorem a4Five_gram_entry (M : Matrix (Fin 4) (Fin 4) (ZMod 25)) (i j : Fin 4) :
    (M.transpose*a4FiveWorkingGram*M) i j =
      2*M 0 i*M 0 j+6*M 1 i*M 1 j+12*M 2 i*M 2 j+20*M 3 i*M 3 j := by
  simp [a4FiveWorkingGram,Matrix.mul_apply,Fin.sum_univ_succ]
  ring


theorem a4Five_lift_last_pair (u : Fin 3 → ZMod 5) (w : {w : ZMod 5 // w^2=1}) :
    2*a4FiveEmbed (u 0)*a4FiveEmbed (u 0)+
    6*a4FiveEmbed (u 1)*a4FiveEmbed (u 1)+
    12*a4FiveEmbed (u 2)*a4FiveEmbed (u 2)+
    20*a4FiveLift w.1*a4FiveLift w.1 = 20 := by
  rw [mul_assoc (2 : ZMod 25),a4Five_embed_pair_zero,
    mul_assoc (6 : ZMod 25),a4Five_embed_pair_zero,
    mul_assoc (12 : ZMod 25),a4Five_embed_pair_zero,a4Five_scaled_weight_pair]
  simp only [mul_zero,zero_add]
  have hw : 4*w.1*w.1 = (4 : ZMod 5) := by
    rw [mul_assoc,← pow_two,w.2,mul_one]
  rw [hw]
  decide

theorem a4FiveAffineMatrix_gram (A : finiteGramOrthogonalGroup a4FiveGram)
    (g : Fin 3 → ZMod 5) (w : {w : ZMod 5 // w^2=1})
    (E : a4FiveDerivativeFiber (a4FiveDerivativeCoefficient A) (a4FiveLiftTarget A g)) :
    (a4FiveAffineMatrix A g w.1 E.1).transpose*a4FiveWorkingGram*
      a4FiveAffineMatrix A g w.1 E.1 = a4FiveWorkingGram := by
  ext i j
  rw [a4Five_gram_entry]
  fin_cases i <;> fin_cases j <;>
    simp only [a4FiveAffineMatrix,a4FiveWorkingGram]
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 0 0
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 0 1
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 0 2
  · simpa [a4FiveWeightedPair] using a4Five_lift_cross_pair A g w.1 E.1 0
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 1 0
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 1 1
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 1 2
  · simpa [a4FiveWeightedPair] using a4Five_lift_cross_pair A g w.1 E.1 1
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 2 0
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 2 1
  · simpa [a4FiveWeightedPair,a4FiveIntegerGram] using a4Five_lift_top_pair A g E 2 2
  · simpa [a4FiveWeightedPair] using a4Five_lift_cross_pair A g w.1 E.1 2
  · simpa [a4FiveWeightedPair,mul_comm,mul_left_comm,mul_assoc] using
      a4Five_lift_cross_pair A g w.1 E.1 0
  · simpa [a4FiveWeightedPair,mul_comm,mul_left_comm,mul_assoc] using
      a4Five_lift_cross_pair A g w.1 E.1 1
  · simpa [a4FiveWeightedPair,mul_comm,mul_left_comm,mul_assoc] using
      a4Five_lift_cross_pair A g w.1 E.1 2
  · exact a4Five_lift_last_pair (a4FiveCrossColumn A g w.1) w


abbrev a4FiveDenominator :=
  a4FiveDiagonalLattice.associatedBilinearDualPadicDenominatorIntegralPreimage 5 2

def a4FiveFamilyOfIntegerMatrix (P : Matrix (Fin 4) (Fin 4) ℤ) :
    Fin 4 → localDualQuotientTarget a4FiveDenominator :=
  fun j => a4FiveDenominator.mkQ (fun i => P i j)

theorem a4FiveFamilyOfIntegerMatrix_apply (P : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → ℤ) :
    quotientBasisFamilyMap a4FiveDenominator (a4FiveFamilyOfIntegerMatrix P) x =
      a4FiveDenominator.mkQ (P.mulVec x) := by
  unfold quotientBasisFamilyMap a4FiveFamilyOfIntegerMatrix
  calc
    _ = a4FiveDenominator.mkQ (∑ j, x j • (fun i => P i j)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (map_zsmul a4FiveDenominator.mkQ (x j) (fun i => P i j)).symm
    _ = _ := by
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]

theorem a4Five_quadForm_cast (x : Fin 4 → ℤ) :
    (a4FiveDiagonalLattice.quadForm x : ZMod 25) =
      dotProduct (fun i => (x i : ZMod 25))
        (a4FiveWorkingGram.mulVec (fun i => (x i : ZMod 25))) := by
  rw [PositiveDefiniteIntegralLattice.quadForm_eq_dotProduct]
  simp [a4FiveDiagonalLattice, a4FiveWorkingGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem a4Five_gram_preserves_quadForm (P : Matrix (Fin 4) (Fin 4) ℤ)
    (hP : (P.map (Int.castRingHom (ZMod 25))).transpose * a4FiveWorkingGram *
      P.map (Int.castRingHom (ZMod 25)) = a4FiveWorkingGram) (x : Fin 4 → ℤ) :
    (a4FiveDiagonalLattice.quadForm (P.mulVec x) : ZMod 25) =
      (a4FiveDiagonalLattice.quadForm x : ZMod 25) := by
  let X := P.map (Int.castRingHom (ZMod 25))
  let v : Fin 4 → ZMod 25 := fun i => x i
  have hx : (fun i => (P.mulVec x i : ZMod 25)) = X.mulVec v := by
    ext i
    simp [X, v, Matrix.mulVec, dotProduct]
  calc
    _ = dotProduct (X.mulVec v) (a4FiveWorkingGram.mulVec (X.mulVec v)) := by
      rw [a4Five_quadForm_cast, hx]
    _ = dotProduct v ((X.transpose * a4FiveWorkingGram * X).mulVec v) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = dotProduct v (a4FiveWorkingGram.mulVec v) := by rw [hP]
    _ = _ := (a4Five_quadForm_cast x).symm
theorem a4FiveFamilyOfIntegerMatrix_mem (P : Matrix (Fin 4) (Fin 4) ℤ)
    (hP : (P.map (Int.castRingHom (ZMod 25))).transpose * a4FiveWorkingGram *
      P.map (Int.castRingHom (ZMod 25)) = a4FiveWorkingGram) :
    a4FiveFamilyOfIntegerMatrix P ∈ localDualQuotientSolutionFamilies
      a4FiveDiagonalLattice 5 2 a4FiveDenominator
        (associatedBilinearDualPadicDenominatorIntegralPreimage_rank a4FiveDiagonalLattice 5 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  rw [a4FiveFamilyOfIntegerMatrix_apply] at hxy
  have hy : y - P.mulVec x ∈ a4FiveDenominator :=
    (Submodule.Quotient.eq a4FiveDenominator).mp hxy.symm
  exact ((associatedBilinearDualPadicDenominatorIntegralPreimage_admissible a4FiveDiagonalLattice 5 2
    a4FiveDiagonal_hensel_two.associated_bilinear_quadratic_depth).2 hy).trans
      (a4Five_gram_preserves_quadForm P hP x)

def a4FiveIntegerMatrix (M : Matrix (Fin 4) (Fin 4) (ZMod 25)) :
    Matrix (Fin 4) (Fin 4) ℤ := M.map (fun z => (z.val : ℤ))

def a4FiveLiftDataToNative (t : a4FiveAffineLiftData) :
    associatedBilinearDualQuotientSolutionFamily a4FiveDiagonalLattice 5 2 := by
  rcases t with ⟨A, gh, w, E⟩
  let M := a4FiveAffineMatrix A gh w.1 E.1
  let P := a4FiveIntegerMatrix M
  have hp : P.map (Int.castRingHom (ZMod 25)) = M := by
    ext i j
    simp [P, a4FiveIntegerMatrix]
  have hGram : (P.map (Int.castRingHom (ZMod 25))).transpose * a4FiveWorkingGram *
      P.map (Int.castRingHom (ZMod 25)) = a4FiveWorkingGram := by
    rw [hp]
    exact a4FiveAffineMatrix_gram A gh w E
  have hmem := a4FiveFamilyOfIntegerMatrix_mem P hGram
  exact ⟨a4FiveFamilyOfIntegerMatrix P, hmem⟩


theorem a4Five_quotient_eq_iff (x y : Fin 4 → ℤ) :
    a4FiveDenominator.mkQ x = a4FiveDenominator.mkQ y ↔
      (x 0 : ZMod 25) = y 0 ∧ (x 1 : ZMod 25) = y 1 ∧
      (x 2 : ZMod 25) = y 2 ∧ (x 3 : ZMod 5) = y 3 := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  unfold a4FiveDenominator
  rw [Submodule.Quotient.eq,a4FiveDiagonal_associated_denominator,
    mem_diagonalPrimePowCoordinateSubmodule_iff]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  change (((x 0-y 0 : ℤ) : ZMod 25) = 0 ∧ ((x 1-y 1 : ℤ) : ZMod 25) = 0 ∧
    ((x 2-y 2 : ℤ) : ZMod 25) = 0 ∧ ((x 3-y 3 : ℤ) : ZMod 5) = 0) ↔ _
  simp only [Int.cast_sub,sub_eq_zero]

theorem a4Five_val_reduces (a : ZMod 25) :
    ((a.val : ℤ) : ZMod 5) = a4FiveReduction a := by
  calc
    _ = a4FiveReduction (((a.val : ℤ) : ZMod 25)) := (map_intCast _ _).symm
    _ = _ := by simp

theorem a4Five_integer_family_eq_iff (M N : Matrix (Fin 4) (Fin 4) (ZMod 25)) :
    a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix M) =
      a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix N) ↔
      ∀ j, M 0 j = N 0 j ∧ M 1 j = N 1 j ∧ M 2 j = N 2 j ∧
        a4FiveReduction (M 3 j) = a4FiveReduction (N 3 j) := by
  rw [funext_iff]
  simp only [a4FiveFamilyOfIntegerMatrix,a4Five_quotient_eq_iff,
    a4FiveIntegerMatrix,Matrix.map_apply,a4Five_val_reduces]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem a4Five_affine_reduces (a x : ZMod 5) :
    a4FiveReduction (a4FiveLift a+a4FiveEmbed x) = a := by
  rw [map_add,a4FiveLift_reduces,a4FiveEmbed_reduces,add_zero]

theorem a4Five_affine_injective (a x y : ZMod 5)
    (h : a4FiveLift a+a4FiveEmbed x = a4FiveLift a+a4FiveEmbed y) : x = y :=
  a4FiveEmbed_injective (add_left_cancel h)

theorem a4FiveLiftDataToNative_injective : Function.Injective a4FiveLiftDataToNative := by
  rintro ⟨A,g,w,E⟩ ⟨B,g',w',E'⟩ h
  have hf : a4FiveFamilyOfIntegerMatrix
      (a4FiveIntegerMatrix (a4FiveAffineMatrix A g w.1 E.1)) =
    a4FiveFamilyOfIntegerMatrix
      (a4FiveIntegerMatrix (a4FiveAffineMatrix B g' w'.1 E'.1)) := congrArg Subtype.val h
  have he := (a4Five_integer_family_eq_iff _ _).mp hf
  have hA : A = B := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 0).1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 1).1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 2).1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 0).2.1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 1).2.1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 2).2.1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 0).2.2.1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 1).2.2.1
    · simpa [a4FiveAffineMatrix,a4Five_affine_reduces] using
        congrArg a4FiveReduction (he 2).2.2.1
  cases hA
  have hg : g = g' := by
    ext i
    fin_cases i
    · simpa [a4FiveAffineMatrix,a4FiveLift_reduces] using (he 0).2.2.2
    · simpa [a4FiveAffineMatrix,a4FiveLift_reduces] using (he 1).2.2.2
    · simpa [a4FiveAffineMatrix,a4FiveLift_reduces] using (he 2).2.2.2
  cases hg
  have hw : w = w' := by
    apply Subtype.ext
    simpa [a4FiveAffineMatrix,a4FiveLift_reduces] using (he 3).2.2.2
  cases hw
  have hE : E = E' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact a4Five_affine_injective _ _ _ (he 0).1
    · exact a4Five_affine_injective _ _ _ (he 1).1
    · exact a4Five_affine_injective _ _ _ (he 2).1
    · exact a4Five_affine_injective _ _ _ (he 0).2.1
    · exact a4Five_affine_injective _ _ _ (he 1).2.1
    · exact a4Five_affine_injective _ _ _ (he 2).2.1
    · exact a4Five_affine_injective _ _ _ (he 0).2.2.1
    · exact a4Five_affine_injective _ _ _ (he 1).2.2.1
    · exact a4Five_affine_injective _ _ _ (he 2).2.2.1
  cases hE
  rfl

end MassFormulaReleaseExamples
