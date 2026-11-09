import SMSFormula.Applications.Examples.A4FiveLift

/-! Recovery of the actual block and residue data from native A4 families at five. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance a4FiveRecoveryPrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def a4FiveReducedGram : Matrix (Fin 4) (Fin 4) (ZMod 5) := Matrix.diagonal ![2,6,12,0]

def a4FiveTopBlock (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) : A4FiveMatrix :=
  !![M 0 0,M 0 1,M 0 2; M 1 0,M 1 1,M 1 2; M 2 0,M 2 1,M 2 2]

theorem a4FiveWorkingGram_reduces :
    a4FiveWorkingGram.map a4FiveReduction = a4FiveReducedGram := by decide

theorem a4Five_reduced_gram_condition (M : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (hM : M.transpose*a4FiveReducedGram*M = a4FiveReducedGram) (i j : Fin 4) :
    2*M 0 i*M 0 j+6*M 1 i*M 1 j+12*M 2 i*M 2 j = a4FiveReducedGram i j := by
  calc
    _ = (M.transpose*a4FiveReducedGram*M) i j := by
      simp [a4FiveReducedGram,Matrix.mul_apply,Fin.sum_univ_succ]
      ring
    _ = _ := congrArg (fun N : Matrix (Fin 4) (Fin 4) (ZMod 5) => N i j) hM

theorem a4FiveTopBlock_entry (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) (i j : Fin 3) :
    a4FiveTopBlock M i j = M (i.castAdd 1) (j.castAdd 1) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem a4FiveGram_block_entry (B : A4FiveMatrix) (i j : Fin 3) :
    (B.transpose*a4FiveGram*B) i j =
      2*B 0 i*B 0 j+6*B 1 i*B 1 j+12*B 2 i*B 2 j := by
  simp [a4FiveGram,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

theorem a4FiveTopBlock_orthogonal (M : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (hM : M.transpose*a4FiveReducedGram*M = a4FiveReducedGram) :
    (a4FiveTopBlock M).transpose*a4FiveGram*a4FiveTopBlock M = a4FiveGram := by
  ext i j
  rw [a4FiveGram_block_entry]
  simp only [a4FiveTopBlock_entry]
  have hi : a4FiveReducedGram (i.castAdd 1) (j.castAdd 1) = a4FiveGram i j := by
    fin_cases i <;> fin_cases j <;> decide
  exact (a4Five_reduced_gram_condition M hM (i.castAdd 1) (j.castAdd 1)).trans hi

theorem a4FiveTopBlock_det_ne_zero (M : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (hM : M.transpose*a4FiveReducedGram*M = a4FiveReducedGram) :
    (a4FiveTopBlock M).det ≠ 0 := by
  have hd := congrArg Matrix.det (a4FiveTopBlock_orthogonal M hM)
  simp only [Matrix.det_mul,Matrix.det_transpose] at hd
  have hD : a4FiveGram.det = 4 := by decide
  rw [hD] at hd
  intro hz
  rw [hz] at hd
  norm_num at hd
  exact (by decide : (0 : ZMod 5) ≠ 4) hd

theorem a4Five_reduced_gram (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    (M.map a4FiveReduction).transpose*a4FiveReducedGram*M.map a4FiveReduction =
      a4FiveReducedGram := by
  have h := congrArg (fun N : Matrix (Fin 4) (Fin 4) (ZMod 25) => N.map a4FiveReduction) hM
  simpa only [Matrix.map_mul,Matrix.transpose_map,a4FiveWorkingGram_reduces] using h

def a4FiveRecoveredBlock (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    finiteGramOrthogonalGroup a4FiveGram :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (a4FiveTopBlock (M.map a4FiveReduction))
    (a4FiveTopBlock_det_ne_zero _ (a4Five_reduced_gram M hM)),
    a4FiveTopBlock_orthogonal _ (a4Five_reduced_gram M hM)⟩

theorem a4FiveRecoveredBlock_entry (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) (i j : Fin 3) :
    (((a4FiveRecoveredBlock M hM).1 : A4FiveMatrix) i j) =
      a4FiveReduction (M (i.castAdd 1) (j.castAdd 1)) := by
  fin_cases i <;> fin_cases j <;> rfl


theorem a4FiveCoefficient_mulVec_entry (A : finiteGramOrthogonalGroup a4FiveGram)
    (b : Fin 3 → ZMod 5) (i : Fin 3) :
    (((A.1 : A4FiveMatrix).transpose*a4FiveGram).mulVec b) i =
      2*(A.1 : A4FiveMatrix) 0 i*b 0+6*(A.1 : A4FiveMatrix) 1 i*b 1+
        12*(A.1 : A4FiveMatrix) 2 i*b 2 := by
  simp [a4FiveGram,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem a4Five_working_cross_zero (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    ∀ i : Fin 3, a4FiveReduction (M (i.castAdd 1) 3) = 0 := by
  let A := a4FiveRecoveredBlock M hM
  let b : Fin 3 → ZMod 5 := fun i => a4FiveReduction (M (i.castAdd 1) 3)
  have hb : ((A.1 : A4FiveMatrix).transpose*a4FiveGram).mulVec b = 0 := by
    ext i
    rw [a4FiveCoefficient_mulVec_entry]
    simp only [A,a4FiveRecoveredBlock_entry]
    have hz : a4FiveReducedGram (i.castAdd 1) 3 = 0 := by fin_cases i <;> decide
    exact (a4Five_reduced_gram_condition (M.map a4FiveReduction)
      (a4Five_reduced_gram M hM) (i.castAdd 1) 3).trans hz
  have he : b = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr (a4FiveDerivativeCoefficient_unit A)
    simpa only [Matrix.mulVec_zero] using hb
  exact congr_fun he

theorem a4Five_twenty_scaled_pair (g w : ZMod 25) :
    (20 : ZMod 25)*g*w = a4FiveEmbed (4*a4FiveReduction g*a4FiveReduction w) := by
  have h : ∀ g w : ZMod 25,
      (20 : ZMod 25)*g*w = a4FiveEmbed (4*a4FiveReduction g*a4FiveReduction w) := by
    decide +kernel
  exact h g w

theorem a4Five_working_last_sq (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    a4FiveReduction (M 3 3)^2 = 1 := by
  have h := congrArg (fun N : Matrix (Fin 4) (Fin 4) (ZMod 25) => N 3 3) hM
  change (M.transpose*a4FiveWorkingGram*M) 3 3 = a4FiveWorkingGram 3 3 at h
  rw [a4Five_gram_entry] at h
  change 2*M 0 3*M 0 3+6*M 1 3*M 1 3+12*M 2 3*M 2 3+20*M 3 3*M 3 3 = 20 at h
  have h0 := a4Five_kernel_split (M 0 3) (a4Five_working_cross_zero M hM 0)
  have h1 := a4Five_kernel_split (M 1 3) (a4Five_working_cross_zero M hM 1)
  have h2 := a4Five_kernel_split (M 2 3) (a4Five_working_cross_zero M hM 2)
  rw [h0,h1,h2,mul_assoc (2 : ZMod 25),a4Five_embed_pair_zero,
    mul_assoc (6 : ZMod 25),a4Five_embed_pair_zero,
    mul_assoc (12 : ZMod 25),a4Five_embed_pair_zero,a4Five_twenty_scaled_pair] at h
  simp only [mul_zero,zero_add] at h
  have h4 : a4FiveEmbed 4 = 20 := by decide
  have he := a4FiveEmbed_injective (h.trans h4.symm)
  apply mul_left_cancel₀ (by decide : (4 : ZMod 5) ≠ 0)
  simpa only [mul_assoc,← pow_two,mul_one] using he

def a4FiveNativeMatrix
    (Y : associatedBilinearDualQuotientSolutionFamily a4FiveDiagonalLattice 5 2) :
    Matrix (Fin 4) (Fin 4) (ZMod 25) :=
  (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    a4FiveDiagonalLattice 5 2 Y).map Int.cast

theorem a4Five_native_working_gram
    (Y : associatedBilinearDualQuotientSolutionFamily a4FiveDiagonalLattice 5 2) :
    let M := a4FiveNativeMatrix Y
    M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram := by
  have h := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod_gram_congruence
    a4FiveDiagonalLattice 5 2 Y
  have hG : matrixMod a4FiveDiagonalLattice.polarGramMatrix (primePowModulus 5 2) =
      (2 : ZMod 25) • a4FiveWorkingGram := by decide
  rw [hG] at h
  let X := a4FiveNativeMatrix Y
  have h' : X.transpose*((2 : ZMod 25) • a4FiveWorkingGram)*X =
      (2 : ZMod 25) • a4FiveWorkingGram := h
  simp only [Matrix.mul_smul,Matrix.smul_mul] at h'
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod 25) => (13 : ZMod 25) • M) h'
  simpa only [smul_smul,show (13 : ZMod 25)*2 = 1 by decide,one_smul] using hc


def a4FiveRecoveredDigits (M : Matrix (Fin 4) (Fin 4) (ZMod 25)) : A4FiveMatrix :=
  Matrix.of fun i j => a4FiveDigit (M (i.castAdd 1) (j.castAdd 1))

theorem a4Five_recovered_head_column (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) (i : Fin 3) :
    (fun k => a4FiveLift (((a4FiveRecoveredBlock M hM).1 : A4FiveMatrix) k i)+
      a4FiveEmbed (a4FiveRecoveredDigits M k i)) =
      (fun k : Fin 3 => M (k.castAdd 1) (i.castAdd 1)) := by
  ext k
  rw [a4FiveRecoveredBlock_entry]
  exact (a4Five_split _).symm

theorem a4Five_top_condition (a b x y : Fin 3 → ZMod 5) (g h S : ZMod 25) (e : ZMod 5)
    (hbase : a4FiveWeightedPair (fun i => a4FiveLift (a i))
      (fun i => a4FiveLift (b i)) = S-a4FiveEmbed e)
    (hgram : a4FiveWeightedPair (fun i => a4FiveLift (a i)+a4FiveEmbed (x i))
      (fun i => a4FiveLift (b i)+a4FiveEmbed (y i))+20*g*h = S) :
    2*(a 0*y 0+x 0*b 0)+6*(a 1*y 1+x 1*b 1)+12*(a 2*y 2+x 2*b 2) =
      e-4*a4FiveReduction g*a4FiveReduction h := by
  rw [a4FiveWeightedPair_affine,hbase,a4Five_twenty_scaled_pair] at hgram
  have he : a4FiveEmbed
      (2*(a 0*y 0+x 0*b 0)+6*(a 1*y 1+x 1*b 1)+12*(a 2*y 2+x 2*b 2)+
       4*a4FiveReduction g*a4FiveReduction h) = a4FiveEmbed e := by
    rw [map_add]
    linear_combination hgram
  exact eq_sub_iff_add_eq.mpr (a4FiveEmbed_injective he)

theorem a4FiveRecoveredDigits_condition (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) (i j : Fin 3) :
    let A := a4FiveRecoveredBlock M hM
    let E := a4FiveRecoveredDigits M
    2*((A.1 : A4FiveMatrix) 0 i*E 0 j+E 0 i*(A.1 : A4FiveMatrix) 0 j)+
    6*((A.1 : A4FiveMatrix) 1 i*E 1 j+E 1 i*(A.1 : A4FiveMatrix) 1 j)+
    12*((A.1 : A4FiveMatrix) 2 i*E 2 j+E 2 i*(A.1 : A4FiveMatrix) 2 j) =
      ((a4FiveLiftError A i j/5 : ℤ) : ZMod 5)-
        4*a4FiveReduction (M 3 (i.castAdd 1))*a4FiveReduction (M 3 (j.castAdd 1)) := by
  dsimp only
  refine a4Five_top_condition
    (fun k => ((a4FiveRecoveredBlock M hM).1 : A4FiveMatrix) k i)
    (fun k => ((a4FiveRecoveredBlock M hM).1 : A4FiveMatrix) k j)
    (fun k => a4FiveRecoveredDigits M k i)
    (fun k => a4FiveRecoveredDigits M k j)
    (M 3 (i.castAdd 1)) (M 3 (j.castAdd 1)) (a4FiveIntegerGram i j : ZMod 25)
    ((a4FiveLiftError (a4FiveRecoveredBlock M hM) i j/5 : ℤ) : ZMod 5)
    (a4Five_base_pair (a4FiveRecoveredBlock M hM) i j) ?_
  rw [a4Five_recovered_head_column,a4Five_recovered_head_column]
  have hg := congrArg (fun N : Matrix (Fin 4) (Fin 4) (ZMod 25) =>
    N (i.castAdd 1) (j.castAdd 1)) hM
  change (M.transpose*a4FiveWorkingGram*M) (i.castAdd 1) (j.castAdd 1) =
    a4FiveWorkingGram (i.castAdd 1) (j.castAdd 1) at hg
  rw [a4Five_gram_entry] at hg
  have hd : (a4FiveIntegerGram i j : ZMod 25) =
      a4FiveWorkingGram (i.castAdd 1) (j.castAdd 1) := by
    fin_cases i <;> fin_cases j <;> decide
  rw [hd]
  exact hg

theorem a4FiveRecoveredDigits_mem (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    let A := a4FiveRecoveredBlock M hM
    let E := a4FiveRecoveredDigits M
    let g := fun i : Fin 3 => a4FiveReduction (M 3 (i.castAdd 1))
    ((a4FiveDerivativeCoefficient A : A4FiveMatrix)*E)+
      ((a4FiveDerivativeCoefficient A : A4FiveMatrix)*E).transpose = a4FiveLiftTarget A g := by
  ext i j
  rw [a4Five_derivative_entry]
  exact a4FiveRecoveredDigits_condition M hM i j


def a4FiveRecoveredCrossDigits (M : Matrix (Fin 4) (Fin 4) (ZMod 25)) : Fin 3 → ZMod 5 :=
  fun i => a4FiveDigit (M (i.castAdd 1) 3)

theorem a4Five_recovered_cross_column (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    (fun k => a4FiveEmbed (a4FiveRecoveredCrossDigits M k)) =
      (fun k : Fin 3 => M (k.castAdd 1) 3) := by
  ext k
  exact (a4Five_kernel_split _ (a4Five_working_cross_zero M hM k)).symm

theorem a4Five_cross_condition (a x u : Fin 3 → ZMod 5) (g w : ZMod 25)
    (hgram : a4FiveWeightedPair (fun i => a4FiveLift (a i)+a4FiveEmbed (x i))
      (fun i => a4FiveEmbed (u i))+20*g*w = 0) :
    2*a 0*u 0+6*a 1*u 1+12*a 2*u 2 = -4*a4FiveReduction w*a4FiveReduction g := by
  rw [a4FiveWeightedPair_embed,a4Five_twenty_scaled_pair,← map_add] at hgram
  have he := a4FiveEmbed_injective (hgram.trans (map_zero a4FiveEmbed).symm)
  linear_combination he

theorem a4FiveRecoveredCrossDigits_eq (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) :
    a4FiveRecoveredCrossDigits M = a4FiveCrossColumn (a4FiveRecoveredBlock M hM)
      (fun i => a4FiveReduction (M 3 (i.castAdd 1))) (a4FiveReduction (M 3 3)) := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
    (a4FiveDerivativeCoefficient_unit (a4FiveRecoveredBlock M hM))
  rw [a4FiveCrossColumn_spec]
  ext i
  rw [a4FiveCoefficient_mulVec_entry]
  refine a4Five_cross_condition
    (fun k => ((a4FiveRecoveredBlock M hM).1 : A4FiveMatrix) k i)
    (fun k => a4FiveRecoveredDigits M k i) (a4FiveRecoveredCrossDigits M)
    (M 3 (i.castAdd 1)) (M 3 3) ?_
  rw [a4Five_recovered_head_column,a4Five_recovered_cross_column M hM]
  have hg := congrArg (fun N : Matrix (Fin 4) (Fin 4) (ZMod 25) => N (i.castAdd 1) 3) hM
  change (M.transpose*a4FiveWorkingGram*M) (i.castAdd 1) 3 =
    a4FiveWorkingGram (i.castAdd 1) 3 at hg
  rw [a4Five_gram_entry] at hg
  have hz : a4FiveWorkingGram (i.castAdd 1) 3 = 0 := by fin_cases i <;> decide
  exact hg.trans hz

def a4FiveMatrixData (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) : a4FiveAffineLiftData :=
  ⟨a4FiveRecoveredBlock M hM,fun i => a4FiveReduction (M 3 (i.castAdd 1)),
    ⟨a4FiveReduction (M 3 3),a4Five_working_last_sq M hM⟩,
    ⟨a4FiveRecoveredDigits M,a4FiveRecoveredDigits_mem M hM⟩⟩

theorem a4Five_reconstruct_cross (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) (i : Fin 3) :
    a4FiveEmbed (a4FiveCrossColumn (a4FiveRecoveredBlock M hM)
      (fun k => a4FiveReduction (M 3 (k.castAdd 1))) (a4FiveReduction (M 3 3)) i) =
      M (i.castAdd 1) 3 := by
  have h := congr_fun (a4FiveRecoveredCrossDigits_eq M hM) i
  rw [← h]
  exact (a4Five_kernel_split _ (a4Five_working_cross_zero M hM i)).symm

theorem a4FiveMatrixData_reconstruct (M : Matrix (Fin 4) (Fin 4) (ZMod 25))
    (hM : M.transpose*a4FiveWorkingGram*M = a4FiveWorkingGram) (j : Fin 4) :
    let t := a4FiveMatrixData M hM
    let N := a4FiveAffineMatrix t.1 t.2.1 t.2.2.1.1 t.2.2.2.1
    N 0 j = M 0 j ∧ N 1 j = M 1 j ∧ N 2 j = M 2 j ∧
      a4FiveReduction (N 3 j) = a4FiveReduction (M 3 j) := by
  fin_cases j
  · refine ⟨?_,?_,?_,?_⟩
    · exact congr_fun (a4Five_recovered_head_column M hM 0) 0
    · exact congr_fun (a4Five_recovered_head_column M hM 0) 1
    · exact congr_fun (a4Five_recovered_head_column M hM 0) 2
    · exact a4FiveLift_reduces _
  · refine ⟨?_,?_,?_,?_⟩
    · exact congr_fun (a4Five_recovered_head_column M hM 1) 0
    · exact congr_fun (a4Five_recovered_head_column M hM 1) 1
    · exact congr_fun (a4Five_recovered_head_column M hM 1) 2
    · exact a4FiveLift_reduces _
  · refine ⟨?_,?_,?_,?_⟩
    · exact congr_fun (a4Five_recovered_head_column M hM 2) 0
    · exact congr_fun (a4Five_recovered_head_column M hM 2) 1
    · exact congr_fun (a4Five_recovered_head_column M hM 2) 2
    · exact a4FiveLift_reduces _
  · refine ⟨?_,?_,?_,?_⟩
    · exact a4Five_reconstruct_cross M hM 0
    · exact a4Five_reconstruct_cross M hM 1
    · exact a4Five_reconstruct_cross M hM 2
    · exact a4FiveLift_reduces _


theorem a4Five_integer_family_roundtrip (P : Matrix (Fin 4) (Fin 4) ℤ) :
    a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix (P.map (Int.castRingHom (ZMod 25)))) =
      a4FiveFamilyOfIntegerMatrix P := by
  ext j
  change a4FiveDenominator.mkQ (fun i =>
    a4FiveIntegerMatrix (P.map (Int.castRingHom (ZMod 25))) i j) =
    a4FiveDenominator.mkQ (fun i => P i j)
  rw [a4Five_quotient_eq_iff]
  simp only [a4FiveIntegerMatrix,Matrix.map_apply]
  change (((P 0 j : ZMod 25).val : ℤ) : ZMod 25) = (P 0 j : ZMod 25) ∧
    (((P 1 j : ZMod 25).val : ℤ) : ZMod 25) = (P 1 j : ZMod 25) ∧
    (((P 2 j : ZMod 25).val : ℤ) : ZMod 25) = (P 2 j : ZMod 25) ∧
    (((P 3 j : ZMod 25).val : ℤ) : ZMod 5) = (P 3 j : ZMod 5)
  rw [a4Five_val_reduces]
  simp only [map_intCast,Int.cast_natCast,ZMod.natCast_zmod_val,and_self]

theorem a4Five_native_matrix_family
    (Y : associatedBilinearDualQuotientSolutionFamily a4FiveDiagonalLattice 5 2) :
    a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix (a4FiveNativeMatrix Y)) = Y.1 := by
  let P := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix a4FiveDiagonalLattice 5 2 Y
  have h : a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix (a4FiveNativeMatrix Y)) =
      a4FiveFamilyOfIntegerMatrix P := a4Five_integer_family_roundtrip P
  rw [h]
  ext j
  change a4FiveDenominator.mkQ (Quotient.out (Y.1 j)) = Y.1 j
  exact Submodule.Quotient.mk_out _

theorem a4FiveLiftDataToNative_surjective : Function.Surjective a4FiveLiftDataToNative := by
  intro Y
  let M := a4FiveNativeMatrix Y
  have hM := a4Five_native_working_gram Y
  let t := a4FiveMatrixData M hM
  refine ⟨t,?_⟩
  apply Subtype.ext
  change a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix
    (a4FiveAffineMatrix t.1 t.2.1 t.2.2.1.1 t.2.2.2.1)) = Y.1
  calc
    _ = a4FiveFamilyOfIntegerMatrix (a4FiveIntegerMatrix M) :=
      (a4Five_integer_family_eq_iff _ _).mpr (a4FiveMatrixData_reconstruct M hM)
    _ = _ := a4Five_native_matrix_family Y

theorem a4FiveDiagonal_native_count :
    associatedBilinearDualQuotientCount a4FiveDiagonalLattice 5 2 = 7500000 := by
  rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  calc
    _ = Nat.card a4FiveAffineLiftData :=
      (Nat.card_congr (Equiv.ofBijective a4FiveLiftDataToNative
        ⟨a4FiveLiftDataToNative_injective,a4FiveLiftDataToNative_surjective⟩)).symm
    _ = 7500000 := a4FiveAffineLiftData_card

theorem a4FiveDiagonal_density : normalizedLocalDensity a4FiveDiagonalLattice 5 =
    48*Real.sqrt 5/625 := by
  rw [a4FiveDiagonal_density_eq_native_count,a4FiveDiagonal_native_count]
  norm_num only [Nat.cast_ofNat]
  ring

theorem a4_density_five : normalizedLocalDensity a4.latticeOfPolarForm 5 =
    48*Real.sqrt 5/625 :=
  a4_density_five_eq_diagonal.trans a4FiveDiagonal_density


theorem a4_native_count_five_two :
    associatedBilinearDualQuotientCount a4.latticeOfPolarForm 5 2 = 7500000 := by
  have hc := a4_density_five_eq_native_count
  rw [a4_density_five] at hc
  have hm : (associatedBilinearDualQuotientCount a4.latticeOfPolarForm 5 2 : ℝ)*Real.sqrt 5 =
      (7500000 : ℝ)*Real.sqrt 5 := by
    linear_combination -(97656250 : ℝ)*hc
  have hr := mul_right_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ)<5)) hm
  exact Nat.cast_injective hr

end MassFormulaReleaseExamples
