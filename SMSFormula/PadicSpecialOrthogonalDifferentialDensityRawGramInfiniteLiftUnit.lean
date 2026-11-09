import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInfiniteLiftGram

/-!
# Invertibility of the p-adic limit of a raw Gram branch

The exact Gram identity implies that the square of the limit determinant is
one.  The Gram determinant is only cancelled through its proved nonzeroness;
it is not assumed to be a unit at a bad prime.  This makes the branch limit a
unit in the matrix ring over `PadicInt`.

No choice of a unit witness, general-linear packaging, or stabilizer
membership is made in this module.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The p-adic limit of a compatible complete raw Gram branch also preserves
the original integral form.  This cancels scalar two rather than dividing by
it, so the statement is valid at the dyadic prime as well. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimit_preserves_form
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    C.padicLimit.transpose * L.pairingMatrix_padic p * C.padicLimit =
      L.pairingMatrix_padic p := by
  have h := C.padicLimit_preserves_gram
  rw [L.polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic p] at h
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  exact (smul_right_injective (Matrix (Fin n) (Fin n) ℤ_[p])
    (by norm_num : (2 : ℤ_[p]) ≠ 0)) h

/-- The determinant of the p-adic branch limit is its own multiplicative
inverse.  Only the nonzero Gram determinant is cancelled. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.det_padicLimit_mul_self_eq_one
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    C.padicLimit.det * C.padicLimit.det = 1 := by
  have hdet := congrArg Matrix.det C.padicLimit_preserves_gram
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hGne : (L.polarGramMatrix_padic p).det ≠ 0 := by
    rw [L.polarGramMatrix_padic_det p]
    exact Int.cast_ne_zero.mpr L.polarDeterminant_pos.ne'
  apply mul_right_cancel₀ hGne
  simpa [mul_assoc, mul_comm, mul_left_comm] using hdet

/-- The p-adic limit matrix of every infinite compatible complete raw branch
is a unit over the p-adic integers. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.isUnit_padicLimit
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    IsUnit C.padicLimit := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact IsUnit.of_mul_eq_one C.padicLimit.det C.det_padicLimit_mul_self_eq_one

end PositiveDefiniteIntegralLattice
