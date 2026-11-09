import SMSFormula.Applications.Unimodular.GenusClosure.WordCertificates

noncomputable section

namespace UnimodularGenusClosure
open Matrix TypeIIModEightCertificates
open scoped BigOperators

abbrev R4 := ZMod 4
abbrev R2 := ZMod 2

def modFour : R8 →+* R4 := ZMod.castHom (by decide : 4 ∣ 8) R4

def modTwo : R4 →+* R2 := ZMod.castHom (by decide : 2 ∣ 4) R2

def bitLift (value : R2) : R4 := (value.val : R4)

theorem modFour_val (value : R8) : modFour value = (value.val : R4) := by
  revert value
  decide

theorem modTwo_bitLift (value : R2) : modTwo (bitLift value) = value := by
  revert value
  decide

theorem exists_even_difference (left right : R4)
    (hmod : modTwo left = modTwo right) : ∃ value : R4, left = right + 2 * value := by
  revert left right
  decide

def matrixNorm {ι : Type*} [Fintype ι] (gram : Matrix ι ι R4)
    (vector : ι → R4) : R4 := vector ⬝ᵥ gram.mulVec vector

theorem matrixNorm_add_two {ι : Type*} [Fintype ι]
    (gram : Matrix ι ι R4) (hsymm : gram.IsSymm) (left right : ι → R4) :
    matrixNorm gram (left + (2 : R4) • right) = matrixNorm gram left := by
  have hcross : right ⬝ᵥ gram.mulVec left = left ⬝ᵥ gram.mulVec right := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro col _
    rw [hsymm.apply col row]
    ring
  calc
    matrixNorm gram (left + (2 : R4) • right) =
        matrixNorm gram left + (4 : R4) *
          (left ⬝ᵥ gram.mulVec right + matrixNorm gram right) := by
      simp only [matrixNorm, Matrix.mulVec_add, Matrix.mulVec_smul,
        dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      rw [hcross]
      ring
    _ = matrixNorm gram left := by rw [show (4 : R4) = 0 by decide]; simp

theorem matrixNorm_eq_of_modTwo_eq {ι : Type*} [Fintype ι]
    (gram : Matrix ι ι R4) (hsymm : gram.IsSymm) (left right : ι → R4)
    (hmod : ∀ index, modTwo (left index) = modTwo (right index)) :
    matrixNorm gram left = matrixNorm gram right := by
  choose correction hcorrection using fun index => exists_even_difference _ _ (hmod index)
  have hvector : left = right + (2 : R4) • correction := by
    funext index
    exact hcorrection index
  rw [hvector, matrixNorm_add_two gram hsymm]

def quarticPhase (value : R4) : ℂ := Complex.I ^ value.val

theorem quarticPhase_natCast (value : ℕ) :
    quarticPhase (value : R4) = Complex.I ^ value := by
  rw [quarticPhase, ZMod.val_natCast, Complex.I_pow_eq_pow_mod value]

def binaryMatrixGauss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (gram : Matrix ι ι R8) : ℂ :=
  ∑ vector : ι → R2,
    quarticPhase (matrixNorm (gram.map modFour) (fun index => bitLift (vector index)))

theorem matrixNorm_congr {ι : Type*} [Fintype ι]
    (gram change : Matrix ι ι R4) (vector : ι → R4) :
    matrixNorm gram (change.mulVec vector) =
      matrixNorm (change.transpose * gram * change) vector := by
  unfold matrixNorm
  calc
    (change.mulVec vector) ⬝ᵥ gram.mulVec (change.mulVec vector) =
        ((change.mulVec vector) ᵥ* gram) ⬝ᵥ (change.mulVec vector) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (vector ᵥ* (change.transpose * gram)) ⬝ᵥ (change.mulVec vector) := by
          rw [Matrix.vecMul_mulVec]
    _ = ((vector ᵥ* (change.transpose * gram)) ᵥ* change) ⬝ᵥ vector := by
          rw [Matrix.dotProduct_mulVec]
    _ = (vector ᵥ* (change.transpose * gram * change)) ⬝ᵥ vector := by
          rw [Matrix.vecMul_vecMul]
    _ = vector ⬝ᵥ (change.transpose * gram * change).mulVec vector := by
          rw [Matrix.dotProduct_mulVec]

theorem map_mulVec_modTwo {ι : Type*} [Fintype ι]
    (change : Matrix ι ι R4) (vector : ι → R4) :
    (fun index => modTwo (change.mulVec vector index)) =
      (change.map modTwo).mulVec (fun index => modTwo (vector index)) := by
  funext index
  simp [Matrix.mulVec, dotProduct]

theorem binaryGauss_eq_of_modFour_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source target : Matrix ι ι R4) (hsymm : source.IsSymm)
    (change inverse : Matrix ι ι R4)
    (hcongr : change.transpose * source * change = target)
    (hleft : inverse * change = 1) (hright : change * inverse = 1) :
    (∑ vector : ι → R2,
      quarticPhase (matrixNorm source (fun index => bitLift (vector index)))) =
    ∑ vector : ι → R2,
      quarticPhase (matrixNorm target (fun index => bitLift (vector index))) := by
  have hleftTwo : inverse.map modTwo * change.map modTwo = 1 := by
    rw [← Matrix.map_mul]
    simp [hleft]
  have hrightTwo : change.map modTwo * inverse.map modTwo = 1 := by
    rw [← Matrix.map_mul]
    simp [hright]
  let equiv : (ι → R2) ≃ (ι → R2) :=
    { toFun := (change.map modTwo).mulVec
      invFun := (inverse.map modTwo).mulVec
      left_inv := by
        intro vector
        rw [Matrix.mulVec_mulVec, hleftTwo, Matrix.one_mulVec]
      right_inv := by
        intro vector
        rw [Matrix.mulVec_mulVec, hrightTwo, Matrix.one_mulVec] }
  have hnorm (vector : ι → R2) :
      matrixNorm source (fun index => bitLift (equiv vector index)) =
        matrixNorm target (fun index => bitLift (vector index)) := by
    calc
      _ = matrixNorm source (change.mulVec (fun index => bitLift (vector index))) := by
        apply matrixNorm_eq_of_modTwo_eq source hsymm
        intro index
        rw [modTwo_bitLift]
        have hmap := congrFun (map_mulVec_modTwo change
          (fun index => bitLift (vector index))) index
        simpa only [modTwo_bitLift] using hmap.symm
      _ = _ := by rw [matrixNorm_congr, hcongr]
  calc
    _ = ∑ vector : ι → R2,
        quarticPhase (matrixNorm source (fun index => bitLift (equiv vector index))) :=
      (equiv.sum_comp _).symm
    _ = _ := by simp_rw [hnorm]

theorem binaryMatrixGauss_eq_of_certificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {source target : Matrix ι ι R8} (hsymm : source.IsSymm)
    (cert : GramCongruenceCertificate source target) :
    binaryMatrixGauss source = binaryMatrixGauss target := by
  have hsymmFour : (source.map modFour).IsSymm := by
    ext row col
    exact congrArg modFour (hsymm.apply row col)
  unfold binaryMatrixGauss
  apply binaryGauss_eq_of_modFour_congruence _ _ hsymmFour
    (cert.changeMatrix.map modFour) (cert.inverseMatrix.map modFour)
  · have hcertificate := congrArg (fun gram => gram.map modFour) cert.congruence
    simpa only [Matrix.map_mul] using hcertificate
  · rw [← Matrix.map_mul, cert.inverse_mul]
    simp
  · rw [← Matrix.map_mul, cert.mul_inverse]
    simp

theorem binaryMatrixGauss_wordMatrix (word : List R8) :
    binaryMatrixGauss (wordMatrix word) = binaryWordGauss word := by
  unfold binaryMatrixGauss binaryWordGauss
  apply Finset.sum_congr rfl
  intro vector _
  have hnorm : matrixNorm ((wordMatrix word).map modFour)
        (fun index => bitLift (vector index)) =
      ((∑ index, (word.get index).val * (vector index).val ^ 2 : ℕ) : R4) := by
    unfold matrixNorm wordMatrix
    have hdiag : (Matrix.diagonal word.get).map modFour =
        Matrix.diagonal (fun index => modFour (word.get index)) := by
      ext row col
      by_cases heq : row = col <;> simp [heq]
    rw [hdiag]
    simp only [dotProduct, Matrix.mulVec_diagonal, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_pow, bitLift]
    apply Finset.sum_congr rfl
    intro index _
    rw [modFour_val]
    ring
  rw [hnorm, quarticPhase_natCast]
  rfl

#assert_standard_axioms matrixNorm_eq_of_modTwo_eq
#assert_standard_axioms binaryGauss_eq_of_modFour_congruence
#assert_standard_axioms binaryMatrixGauss_eq_of_certificate
#assert_standard_axioms binaryMatrixGauss_wordMatrix

end UnimodularGenusClosure
