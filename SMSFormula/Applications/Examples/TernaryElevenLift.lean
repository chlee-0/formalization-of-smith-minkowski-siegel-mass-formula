import SMSFormula.Applications.Examples.TernaryElevenBlock

/-! Exact residue-layer arithmetic and the actual affine block lift at 11. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance ternaryElevenLiftPrime : Fact (Nat.Prime 11) := ⟨by decide⟩

def ternaryElevenLift (a : ZMod 11) : ZMod 121 := a.val

def ternaryElevenEmbed : ZMod 11 →+ ZMod 121 where
  toFun a := 11 * ternaryElevenLift a
  map_zero' := by decide
  map_add' := by
    have h : ∀ a b : ZMod 11,
        11 * ternaryElevenLift (a + b) =
          11 * ternaryElevenLift a + 11 * ternaryElevenLift b := by decide +kernel
    exact h

theorem ternaryElevenLift_reduces (a : ZMod 11) :
    ternaryElevenReduction (ternaryElevenLift a) = a := by
  have h : ∀ a : ZMod 11, ternaryElevenReduction (ternaryElevenLift a) = a := by decide
  exact h a

theorem ternaryElevenEmbed_reduces (a : ZMod 11) :
    ternaryElevenReduction (ternaryElevenEmbed a) = 0 := by
  change ternaryElevenReduction (11 * ternaryElevenLift a) = 0
  rw [map_mul]
  have h : ternaryElevenReduction 11 = 0 := by decide
  rw [h, zero_mul]

theorem ternaryElevenEmbed_injective : Function.Injective ternaryElevenEmbed := by
  have h : ∀ a b : ZMod 11, ternaryElevenEmbed a = ternaryElevenEmbed b → a = b := by
    decide +kernel
  exact h

theorem ternaryElevenEmbed_mul (a : ZMod 11) (b : ZMod 121) :
    ternaryElevenEmbed a * b = ternaryElevenEmbed (a * ternaryElevenReduction b) := by
  have h : ∀ a : ZMod 11, ∀ b : ZMod 121,
      ternaryElevenEmbed a * b = ternaryElevenEmbed (a * ternaryElevenReduction b) := by
    decide +kernel
  exact h a b

theorem ternaryEleven_mul_Embed (a : ZMod 121) (b : ZMod 11) :
    a * ternaryElevenEmbed b = ternaryElevenEmbed (ternaryElevenReduction a * b) := by
  rw [mul_comm, ternaryElevenEmbed_mul]
  congr 1
  ring

theorem ternaryElevenEmbed_intCast (z : ℤ) :
    ternaryElevenEmbed (z : ZMod 11) = 11 * (z : ZMod 121) := by
  have h := map_zsmul ternaryElevenEmbed z (1 : ZMod 11)
  have h1 : ternaryElevenEmbed 1 = 11 := by decide
  simpa only [zsmul_eq_mul, mul_one, h1, mul_comm] using h

theorem ternaryEleven_dvd_cast (z : ℤ) (hz : (11 : ℤ) ∣ z) :
    (z : ZMod 121) = ternaryElevenEmbed ((z / 11 : ℤ) : ZMod 11) := by
  rw [ternaryElevenEmbed_intCast]
  calc
    (z : ZMod 121) = ((11 * (z / 11) : ℤ) : ZMod 121) :=
      congrArg Int.cast (Int.mul_ediv_cancel' hz).symm
    _ = _ := by push_cast; rfl

def ternaryElevenDigit (a : ZMod 121) : ZMod 11 := ((a.val / 11 : ℕ) : ZMod 11)

theorem ternaryEleven_split (a : ZMod 121) :
    a = ternaryElevenLift (ternaryElevenReduction a) +
      ternaryElevenEmbed (ternaryElevenDigit a) := by
  have h : ∀ a : ZMod 121,
      a = ternaryElevenLift (ternaryElevenReduction a) +
        ternaryElevenEmbed (ternaryElevenDigit a) := by decide +kernel
  exact h a

theorem ternaryEleven_affine_mul (a b x y : ZMod 11) :
    (ternaryElevenLift a + ternaryElevenEmbed x) *
        (ternaryElevenLift b + ternaryElevenEmbed y) =
      ternaryElevenLift a * ternaryElevenLift b + ternaryElevenEmbed (a * y + x * b) := by
  rw [add_mul, mul_add, mul_add, ternaryEleven_mul_Embed, ternaryElevenEmbed_mul,
    ternaryElevenEmbed_mul, ternaryElevenLift_reduces, ternaryElevenLift_reduces,
    ternaryElevenEmbed_reduces]
  simp only [mul_zero, map_zero, add_zero, map_add]
  ring


theorem ternaryEleven_weighted_affine_pair (a b c d x y z t : ZMod 11) :
    (ternaryElevenLift a + ternaryElevenEmbed x) *
        (ternaryElevenLift b + ternaryElevenEmbed y) +
      2 * (ternaryElevenLift c + ternaryElevenEmbed z) *
        (ternaryElevenLift d + ternaryElevenEmbed t) =
      ternaryElevenLift a * ternaryElevenLift b +
        2 * ternaryElevenLift c * ternaryElevenLift d +
        ternaryElevenEmbed (a * y + x * b + 2 * (c * t + z * d)) := by
  rw [mul_assoc (2 : ZMod 121), ternaryEleven_affine_mul, ternaryEleven_affine_mul]
  simp only [two_mul, map_add]
  ring

theorem ternaryEleven_scaled_lift_pair (g h : ZMod 11) :
    (11 : ZMod 121) * ternaryElevenLift g * ternaryElevenLift h =
      ternaryElevenEmbed (g * h) := by
  change ternaryElevenEmbed g * ternaryElevenLift h = _
  rw [ternaryElevenEmbed_mul, ternaryElevenLift_reduces]

theorem ternaryEleven_affine_embed_pair (a x u : ZMod 11) :
    (ternaryElevenLift a + ternaryElevenEmbed x) * ternaryElevenEmbed u =
      ternaryElevenEmbed (a * u) := by
  rw [ternaryEleven_mul_Embed, map_add, ternaryElevenLift_reduces,
    ternaryElevenEmbed_reduces, add_zero]

theorem ternaryEleven_embed_pair_zero (u v : ZMod 11) :
    ternaryElevenEmbed u * ternaryElevenEmbed v = 0 := by
  rw [ternaryElevenEmbed_mul, ternaryElevenEmbed_reduces, mul_zero, map_zero]

theorem ternaryEleven_base_pair (A : ternaryElevenOrthogonalMatrices) (i j : Fin 2) :
    ternaryElevenLift (A.1 0 i) * ternaryElevenLift (A.1 0 j) +
      2 * ternaryElevenLift (A.1 1 i) * ternaryElevenLift (A.1 1 j) =
      (ternaryElevenIntegerGram i j : ZMod 121) -
        ternaryElevenEmbed ((ternaryElevenLiftError A i j / 11 : ℤ) : ZMod 11) := by
  have hi : ternaryElevenLiftError A i j = ternaryElevenIntegerGram i j -
      (ternaryElevenIntegerBlock A 0 i * ternaryElevenIntegerBlock A 0 j +
        2 * ternaryElevenIntegerBlock A 1 i * ternaryElevenIntegerBlock A 1 j) := by
    simp [ternaryElevenLiftError, ternaryElevenIntegerGram, Matrix.mul_apply,
      Fin.sum_univ_succ]
    ring_nf
    simp
  have hc := congrArg (Int.cast : ℤ → ZMod 121) hi
  push_cast at hc
  have hc' : (ternaryElevenLiftError A i j : ZMod 121) =
      (ternaryElevenIntegerGram i j : ZMod 121) -
      (ternaryElevenLift (A.1 0 i) * ternaryElevenLift (A.1 0 j) +
        2 * ternaryElevenLift (A.1 1 i) * ternaryElevenLift (A.1 1 j)) := hc
  rw [ternaryEleven_dvd_cast _ (ternaryElevenLiftError_dvd A i j)] at hc'
  linear_combination hc'


theorem ternaryElevenCrossColumn_spec (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (w : ZMod 11) :
    (A.1.transpose * ternaryElevenBinaryGram).mulVec (ternaryElevenCrossColumn A gh w) =
      -w • ![gh.1, gh.2] := by
  rw [← ternaryElevenDerivativeCoefficient_coe]
  simp [ternaryElevenCrossColumn, Matrix.mulVec_mulVec]

theorem ternaryElevenLiftTarget_entry (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (i j : Fin 2) :
    ternaryElevenLiftTarget A gh i j =
      ((ternaryElevenLiftError A i j / 11 : ℤ) : ZMod 11) -
        ![gh.1, gh.2] i * ![gh.1, gh.2] j := by
  fin_cases i <;> fin_cases j <;> simp [ternaryElevenLiftTarget] <;> ring

theorem ternaryEleven_derivative_entry (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11)
    (E : ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A)
      (ternaryElevenLiftTarget A gh)) (i j : Fin 2) :
    A.1 0 i * E.1 0 j + E.1 0 i * A.1 0 j +
      2 * (A.1 1 i * E.1 1 j + E.1 1 i * A.1 1 j) =
      ((ternaryElevenLiftError A i j / 11 : ℤ) : ZMod 11) -
        ![gh.1, gh.2] i * ![gh.1, gh.2] j := by
  calc
    _ = (((ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) * E.1) +
          ((ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) * E.1).transpose) i j := by
      simp [ternaryElevenDerivativeCoefficient_coe, ternaryElevenBinaryGram,
        Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    _ = ternaryElevenLiftTarget A gh i j := congrArg (fun M : TernaryElevenMatrix => M i j) E.2
    _ = _ := ternaryElevenLiftTarget_entry A gh i j

theorem ternaryEleven_lift_top_pair (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11)
    (E : ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A)
      (ternaryElevenLiftTarget A gh)) (i j : Fin 2) :
    (ternaryElevenLift (A.1 0 i) + ternaryElevenEmbed (E.1 0 i)) *
        (ternaryElevenLift (A.1 0 j) + ternaryElevenEmbed (E.1 0 j)) +
      2 * (ternaryElevenLift (A.1 1 i) + ternaryElevenEmbed (E.1 1 i)) *
        (ternaryElevenLift (A.1 1 j) + ternaryElevenEmbed (E.1 1 j)) +
      11 * ternaryElevenLift (![gh.1, gh.2] i) * ternaryElevenLift (![gh.1, gh.2] j) =
      (ternaryElevenIntegerGram i j : ZMod 121) := by
  rw [ternaryEleven_weighted_affine_pair, ternaryEleven_base_pair,
    ternaryEleven_scaled_lift_pair, ternaryEleven_derivative_entry]
  simp only [map_sub]
  ring

theorem ternaryEleven_lift_cross_pair (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (w : ZMod 11)
    (E : ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A)
      (ternaryElevenLiftTarget A gh)) (i : Fin 2) :
    (ternaryElevenLift (A.1 0 i) + ternaryElevenEmbed (E.1 0 i)) *
        ternaryElevenEmbed (ternaryElevenCrossColumn A gh w 0) +
      2 * (ternaryElevenLift (A.1 1 i) + ternaryElevenEmbed (E.1 1 i)) *
        ternaryElevenEmbed (ternaryElevenCrossColumn A gh w 1) +
      11 * ternaryElevenLift (![gh.1, gh.2] i) * ternaryElevenLift w = 0 := by
  have hc := congr_fun (ternaryElevenCrossColumn_spec A gh w) i
  have hc' : A.1 0 i * ternaryElevenCrossColumn A gh w 0 +
      2 * A.1 1 i * ternaryElevenCrossColumn A gh w 1 + ![gh.1, gh.2] i * w = 0 := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ,
      ternaryElevenBinaryGram] at hc
    linear_combination hc
  rw [mul_assoc (2 : ZMod 121), ternaryEleven_affine_embed_pair,
    ternaryEleven_affine_embed_pair, ternaryEleven_scaled_lift_pair]
  have h2 (z : ZMod 11) : (2 : ZMod 121) * ternaryElevenEmbed z =
      ternaryElevenEmbed (2 * z) := by simp only [two_mul, map_add]
  rw [h2, ← map_add, ← map_add, ← mul_assoc, hc', map_zero]


def ternaryElevenAffineMatrix (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (w : ZMod 11) (E : TernaryElevenMatrix) :
    Matrix (Fin 3) (Fin 3) (ZMod 121) :=
  !![ternaryElevenLift (A.1 0 0) + ternaryElevenEmbed (E 0 0),
      ternaryElevenLift (A.1 0 1) + ternaryElevenEmbed (E 0 1),
      ternaryElevenEmbed (ternaryElevenCrossColumn A gh w 0);
     ternaryElevenLift (A.1 1 0) + ternaryElevenEmbed (E 1 0),
      ternaryElevenLift (A.1 1 1) + ternaryElevenEmbed (E 1 1),
      ternaryElevenEmbed (ternaryElevenCrossColumn A gh w 1);
     ternaryElevenLift gh.1, ternaryElevenLift gh.2, ternaryElevenLift w]

theorem ternaryEleven_gram_entry (M : Matrix (Fin 3) (Fin 3) (ZMod 121)) (i j : Fin 3) :
    (M.transpose * ternaryElevenWorkingGram * M) i j =
      M 0 i * M 0 j + 2 * M 1 i * M 1 j + 11 * M 2 i * M 2 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, ternaryElevenWorkingGram]
  ring

theorem ternaryElevenAffineMatrix_gram (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (w : {w : ZMod 11 // w ^ 2 = 1})
    (E : ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A)
      (ternaryElevenLiftTarget A gh)) :
    let M := ternaryElevenAffineMatrix A gh w.1 E.1
    M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram := by
  ext i j
  rw [ternaryEleven_gram_entry]
  fin_cases i <;> fin_cases j
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram, ternaryElevenIntegerGram]
      using ternaryEleven_lift_top_pair A gh E 0 0
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram, ternaryElevenIntegerGram]
      using ternaryEleven_lift_top_pair A gh E 0 1
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram]
      using ternaryEleven_lift_cross_pair A gh w.1 E 0
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram, ternaryElevenIntegerGram]
      using ternaryEleven_lift_top_pair A gh E 1 0
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram, ternaryElevenIntegerGram]
      using ternaryEleven_lift_top_pair A gh E 1 1
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram]
      using ternaryEleven_lift_cross_pair A gh w.1 E 1
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram, mul_comm, mul_left_comm, mul_assoc]
      using ternaryEleven_lift_cross_pair A gh w.1 E 0
  · simpa [ternaryElevenAffineMatrix, ternaryElevenWorkingGram, mul_comm, mul_left_comm, mul_assoc]
      using ternaryEleven_lift_cross_pair A gh w.1 E 1
  · change ternaryElevenEmbed _ * ternaryElevenEmbed _ +
      2 * ternaryElevenEmbed _ * ternaryElevenEmbed _ +
      11 * ternaryElevenLift w.1 * ternaryElevenLift w.1 = 11
    rw [mul_assoc (2 : ZMod 121), ternaryEleven_embed_pair_zero,
      ternaryEleven_embed_pair_zero, ternaryEleven_scaled_lift_pair]
    rw [← pow_two w.1, w.2]
    have h1 : ternaryElevenEmbed 1 = 11 := by decide
    simp [h1]


abbrev ternaryElevenDenominator :=
  ternaryLattice.associatedBilinearDualPadicDenominatorIntegralPreimage 11 2

def ternaryElevenFamilyOfIntegerMatrix (P : Matrix (Fin 3) (Fin 3) ℤ) :
    Fin 3 → localDualQuotientTarget ternaryElevenDenominator :=
  fun j => ternaryElevenDenominator.mkQ (fun i => P i j)

theorem ternaryElevenFamilyOfIntegerMatrix_apply (P : Matrix (Fin 3) (Fin 3) ℤ)
    (x : Fin 3 → ℤ) :
    quotientBasisFamilyMap ternaryElevenDenominator (ternaryElevenFamilyOfIntegerMatrix P) x =
      ternaryElevenDenominator.mkQ (P.mulVec x) := by
  unfold quotientBasisFamilyMap ternaryElevenFamilyOfIntegerMatrix
  calc
    _ = ternaryElevenDenominator.mkQ (∑ j, x j • (fun i => P i j)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (map_zsmul ternaryElevenDenominator.mkQ (x j) (fun i => P i j)).symm
    _ = _ := by
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]

theorem ternaryEleven_quadForm_cast (x : Fin 3 → ℤ) :
    (ternaryLattice.quadForm x : ZMod 121) =
      dotProduct (fun i => (x i : ZMod 121))
        (ternaryElevenWorkingGram.mulVec (fun i => (x i : ZMod 121))) := by
  rw [PositiveDefiniteIntegralLattice.quadForm_eq_dotProduct]
  simp [ternaryLattice, ternaryElevenWorkingGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem ternaryEleven_gram_preserves_quadForm (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : (P.map (Int.castRingHom (ZMod 121))).transpose * ternaryElevenWorkingGram *
      P.map (Int.castRingHom (ZMod 121)) = ternaryElevenWorkingGram) (x : Fin 3 → ℤ) :
    (ternaryLattice.quadForm (P.mulVec x) : ZMod 121) =
      (ternaryLattice.quadForm x : ZMod 121) := by
  let X := P.map (Int.castRingHom (ZMod 121))
  let v : Fin 3 → ZMod 121 := fun i => x i
  have hx : (fun i => (P.mulVec x i : ZMod 121)) = X.mulVec v := by
    ext i
    simp [X, v, Matrix.mulVec, dotProduct]
  calc
    _ = dotProduct (X.mulVec v) (ternaryElevenWorkingGram.mulVec (X.mulVec v)) := by
      rw [ternaryEleven_quadForm_cast, hx]
    _ = dotProduct v ((X.transpose * ternaryElevenWorkingGram * X).mulVec v) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = dotProduct v (ternaryElevenWorkingGram.mulVec v) := by rw [hP]
    _ = _ := (ternaryEleven_quadForm_cast x).symm

theorem ternaryElevenFamilyOfIntegerMatrix_mem (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : (P.map (Int.castRingHom (ZMod 121))).transpose * ternaryElevenWorkingGram *
      P.map (Int.castRingHom (ZMod 121)) = ternaryElevenWorkingGram) :
    ternaryElevenFamilyOfIntegerMatrix P ∈ localDualQuotientSolutionFamilies
      ternaryLattice 11 2 ternaryElevenDenominator
        (associatedBilinearDualPadicDenominatorIntegralPreimage_rank ternaryLattice 11 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  rw [ternaryElevenFamilyOfIntegerMatrix_apply] at hxy
  have hy : y - P.mulVec x ∈ ternaryElevenDenominator :=
    (Submodule.Quotient.eq ternaryElevenDenominator).mp hxy.symm
  exact ((associatedBilinearDualPadicDenominatorIntegralPreimage_admissible ternaryLattice 11 2
    ternary_eleven_hensel_two.associated_bilinear_quadratic_depth).2 hy).trans
      (ternaryEleven_gram_preserves_quadForm P hP x)

def ternaryElevenIntegerMatrix (M : Matrix (Fin 3) (Fin 3) (ZMod 121)) :
    Matrix (Fin 3) (Fin 3) ℤ := M.map (fun z => (z.val : ℤ))

def ternaryElevenLiftDataToNative (t : ternaryElevenLiftData) :
    associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2 := by
  rcases t with ⟨A, gh, w, E⟩
  let M := ternaryElevenAffineMatrix A gh w.1 E.1
  let P := ternaryElevenIntegerMatrix M
  have hp : P.map (Int.castRingHom (ZMod 121)) = M := by
    ext i j
    simp [P, ternaryElevenIntegerMatrix]
  have hGram : (P.map (Int.castRingHom (ZMod 121))).transpose * ternaryElevenWorkingGram *
      P.map (Int.castRingHom (ZMod 121)) = ternaryElevenWorkingGram := by
    rw [hp]
    exact ternaryElevenAffineMatrix_gram A gh w E
  have hmem := ternaryElevenFamilyOfIntegerMatrix_mem P hGram
  exact ⟨ternaryElevenFamilyOfIntegerMatrix P, hmem⟩


theorem ternaryEleven_quotient_eq_iff (x y : Fin 3 → ℤ) :
    ternaryElevenDenominator.mkQ x = ternaryElevenDenominator.mkQ y ↔
      (x 0 : ZMod 121) = y 0 ∧ (x 1 : ZMod 121) = y 1 ∧ (x 2 : ZMod 11) = y 2 := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  unfold ternaryElevenDenominator
  rw [Submodule.Quotient.eq, ternary_associated_denominator_eleven_two,
    mem_diagonalPrimePowCoordinateSubmodule_iff]
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  change (((x 0 - y 0 : ℤ) : ZMod 121) = 0 ∧
    ((x 1 - y 1 : ℤ) : ZMod 121) = 0 ∧ ((x 2 - y 2 : ℤ) : ZMod 11) = 0) ↔ _
  simp only [Int.cast_sub, sub_eq_zero]

theorem ternaryEleven_val_reduces (a : ZMod 121) :
    ((a.val : ℤ) : ZMod 11) = ternaryElevenReduction a := by
  calc
    _ = ternaryElevenReduction (((a.val : ℤ) : ZMod 121)) := (map_intCast _ _).symm
    _ = _ := by simp

theorem ternaryEleven_integer_family_eq_iff (M N : Matrix (Fin 3) (Fin 3) (ZMod 121)) :
    ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix M) =
      ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix N) ↔
      ∀ j, M 0 j = N 0 j ∧ M 1 j = N 1 j ∧
        ternaryElevenReduction (M 2 j) = ternaryElevenReduction (N 2 j) := by
  rw [funext_iff]
  simp only [ternaryElevenFamilyOfIntegerMatrix, ternaryEleven_quotient_eq_iff,
    ternaryElevenIntegerMatrix, Matrix.map_apply, ternaryEleven_val_reduces]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem ternaryEleven_affine_reduces (a x : ZMod 11) :
    ternaryElevenReduction (ternaryElevenLift a + ternaryElevenEmbed x) = a := by
  rw [map_add, ternaryElevenLift_reduces, ternaryElevenEmbed_reduces, add_zero]

theorem ternaryEleven_affine_injective (a x y : ZMod 11)
    (h : ternaryElevenLift a + ternaryElevenEmbed x =
      ternaryElevenLift a + ternaryElevenEmbed y) : x = y :=
  ternaryElevenEmbed_injective (add_left_cancel h)

theorem ternaryElevenLiftDataToNative_injective : Function.Injective ternaryElevenLiftDataToNative := by
  rintro ⟨A, gh, w, E⟩ ⟨B, gh', w', E'⟩ h
  have hf : ternaryElevenFamilyOfIntegerMatrix
        (ternaryElevenIntegerMatrix (ternaryElevenAffineMatrix A gh w.1 E.1)) =
      ternaryElevenFamilyOfIntegerMatrix
        (ternaryElevenIntegerMatrix (ternaryElevenAffineMatrix B gh' w'.1 E'.1)) :=
    congrArg Subtype.val h
  have he := (ternaryEleven_integer_family_eq_iff _ _).mp hf
  have hA : A = B := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [ternaryElevenAffineMatrix, ternaryEleven_affine_reduces] using
        congrArg ternaryElevenReduction (he 0).1
    · simpa [ternaryElevenAffineMatrix, ternaryEleven_affine_reduces] using
        congrArg ternaryElevenReduction (he 1).1
    · simpa [ternaryElevenAffineMatrix, ternaryEleven_affine_reduces] using
        congrArg ternaryElevenReduction (he 0).2.1
    · simpa [ternaryElevenAffineMatrix, ternaryEleven_affine_reduces] using
        congrArg ternaryElevenReduction (he 1).2.1
  cases hA
  have hg : gh = gh' := by
    apply Prod.ext
    · simpa [ternaryElevenAffineMatrix, ternaryElevenLift_reduces] using (he 0).2.2
    · simpa [ternaryElevenAffineMatrix, ternaryElevenLift_reduces] using (he 1).2.2
  cases hg
  have hw : w = w' := by
    apply Subtype.ext
    simpa [ternaryElevenAffineMatrix, ternaryElevenLift_reduces] using (he 2).2.2
  cases hw
  have hE : E = E' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact ternaryEleven_affine_injective _ _ _ (he 0).1
    · exact ternaryEleven_affine_injective _ _ _ (he 1).1
    · exact ternaryEleven_affine_injective _ _ _ (he 0).2.1
    · exact ternaryEleven_affine_injective _ _ _ (he 1).2.1
  cases hE
  rfl


theorem ternaryEleven_scaled_pair (g h : ZMod 121) :
    (11 : ZMod 121) * g * h = ternaryElevenEmbed (ternaryElevenReduction g * ternaryElevenReduction h) := by
  have h1 : ternaryElevenEmbed 1 = 11 := by decide
  rw [← h1, ternaryElevenEmbed_mul, ternaryElevenEmbed_mul, one_mul]

theorem ternaryEleven_top_condition (a b c d x y z t : ZMod 11)
    (g h D : ZMod 121) (q : ZMod 11)
    (hbase : ternaryElevenLift a * ternaryElevenLift b +
      2 * ternaryElevenLift c * ternaryElevenLift d = D - ternaryElevenEmbed q)
    (hgram : (ternaryElevenLift a + ternaryElevenEmbed x) *
        (ternaryElevenLift b + ternaryElevenEmbed y) +
      2 * (ternaryElevenLift c + ternaryElevenEmbed z) *
        (ternaryElevenLift d + ternaryElevenEmbed t) + 11 * g * h = D) :
    a * y + x * b + 2 * (c * t + z * d) = q - ternaryElevenReduction g * ternaryElevenReduction h := by
  rw [ternaryEleven_weighted_affine_pair, hbase, ternaryEleven_scaled_pair] at hgram
  apply ternaryElevenEmbed_injective
  rw [map_sub]
  linear_combination hgram

theorem ternaryElevenTopBlock_entry (M : Matrix (Fin 3) (Fin 3) (ZMod 11)) (i j : Fin 2) :
    ternaryElevenTopBlock M i j = M (i.castAdd 1) (j.castAdd 1) := by
  fin_cases i <;> fin_cases j <;> rfl

def ternaryElevenMatrixBlock (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) :
    ternaryElevenOrthogonalMatrices := by
  have hr := congrArg (fun N : Matrix (Fin 3) (Fin 3) (ZMod 121) =>
    N.map ternaryElevenReduction) hM
  simp only [Matrix.map_mul, Matrix.transpose_map, ternaryElevenWorkingGram_reduces] at hr
  exact ⟨ternaryElevenTopBlock (M.map ternaryElevenReduction), ternaryElevenTopBlock_orthogonal _ hr⟩

def ternaryElevenMatrixDigits (M : Matrix (Fin 3) (Fin 3) (ZMod 121)) : TernaryElevenMatrix :=
  fun i j => ternaryElevenDigit (M (i.castAdd 1) (j.castAdd 1))

theorem ternaryElevenMatrixBlock_entry (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) (i j : Fin 2) :
    (ternaryElevenMatrixBlock M hM).1 i j =
      ternaryElevenReduction (M (i.castAdd 1) (j.castAdd 1)) :=
  ternaryElevenTopBlock_entry _ i j

theorem ternaryElevenMatrixDigits_condition (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) (i j : Fin 2) :
    let A := ternaryElevenMatrixBlock M hM
    let E := ternaryElevenMatrixDigits M
    A.1 0 i * E 0 j + E 0 i * A.1 0 j + 2 * (A.1 1 i * E 1 j + E 1 i * A.1 1 j) =
      ((ternaryElevenLiftError A i j / 11 : ℤ) : ZMod 11) -
        ternaryElevenReduction (M 2 (i.castAdd 1)) * ternaryElevenReduction (M 2 (j.castAdd 1)) := by
  dsimp only
  apply ternaryEleven_top_condition _ _ _ _ _ _ _ _ _ _ _ _
    (ternaryEleven_base_pair (ternaryElevenMatrixBlock M hM) i j)
  simp only [ternaryElevenMatrixBlock_entry, ternaryElevenMatrixDigits]
  change (ternaryElevenLift (ternaryElevenReduction (M 0 (i.castAdd 1))) +
      ternaryElevenEmbed (ternaryElevenDigit (M 0 (i.castAdd 1)))) *
      (ternaryElevenLift (ternaryElevenReduction (M 0 (j.castAdd 1))) +
      ternaryElevenEmbed (ternaryElevenDigit (M 0 (j.castAdd 1)))) +
      2 * (ternaryElevenLift (ternaryElevenReduction (M 1 (i.castAdd 1))) +
      ternaryElevenEmbed (ternaryElevenDigit (M 1 (i.castAdd 1)))) *
      (ternaryElevenLift (ternaryElevenReduction (M 1 (j.castAdd 1))) +
      ternaryElevenEmbed (ternaryElevenDigit (M 1 (j.castAdd 1)))) +
      11 * M 2 (i.castAdd 1) * M 2 (j.castAdd 1) = _
  rw [← ternaryEleven_split, ← ternaryEleven_split, ← ternaryEleven_split, ← ternaryEleven_split]
  convert ternaryElevenWorkingGram_entry M hM (i.castAdd 1) (j.castAdd 1) using 1
  fin_cases i <;> fin_cases j <;> rfl

theorem ternaryEleven_derivative_raw_entry (A : ternaryElevenOrthogonalMatrices)
    (E : TernaryElevenMatrix) (i j : Fin 2) :
    (((ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) * E) +
      ((ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) * E).transpose) i j =
      A.1 0 i * E 0 j + E 0 i * A.1 0 j + 2 * (A.1 1 i * E 1 j + E 1 i * A.1 1 j) := by
  simp [ternaryElevenDerivativeCoefficient_coe, ternaryElevenBinaryGram,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem ternaryElevenMatrixDigits_mem (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) :
    let A := ternaryElevenMatrixBlock M hM
    let gh := (ternaryElevenReduction (M 2 0), ternaryElevenReduction (M 2 1))
    ((ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) * ternaryElevenMatrixDigits M) +
      ((ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) * ternaryElevenMatrixDigits M).transpose =
        ternaryElevenLiftTarget A gh := by
  ext i j
  rw [ternaryEleven_derivative_raw_entry, ternaryElevenLiftTarget_entry,
    ternaryElevenMatrixDigits_condition]
  fin_cases i <;> fin_cases j <;> rfl


theorem ternaryEleven_kernel_split (a : ZMod 121) (ha : ternaryElevenReduction a = 0) :
    a = ternaryElevenEmbed (ternaryElevenDigit a) := by
  have h := ternaryEleven_split a
  rw [ha, show ternaryElevenLift 0 = 0 by decide, zero_add] at h
  exact h

theorem ternaryEleven_cross_condition (a c x z u v : ZMod 11) (g w : ZMod 121)
    (hgram : (ternaryElevenLift a + ternaryElevenEmbed x) * ternaryElevenEmbed u +
      2 * (ternaryElevenLift c + ternaryElevenEmbed z) * ternaryElevenEmbed v + 11 * g * w = 0) :
    a * u + 2 * c * v + ternaryElevenReduction g * ternaryElevenReduction w = 0 := by
  rw [mul_assoc (2 : ZMod 121), ternaryEleven_affine_embed_pair,
    ternaryEleven_affine_embed_pair, ternaryEleven_scaled_pair] at hgram
  apply ternaryElevenEmbed_injective
  rw [map_zero, map_add, map_add]
  have h2 : ternaryElevenEmbed (2 * c * v) = 2 * ternaryElevenEmbed (c * v) := by
    rw [mul_assoc, two_mul, map_add, two_mul]
  rw [h2]
  exact hgram

theorem ternaryElevenMatrixCrossDigits (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) :
    ![ternaryElevenDigit (M 0 2), ternaryElevenDigit (M 1 2)] =
      ternaryElevenCrossColumn (ternaryElevenMatrixBlock M hM)
        (ternaryElevenReduction (M 2 0), ternaryElevenReduction (M 2 1))
        (ternaryElevenReduction (M 2 2)) := by
  let A := ternaryElevenMatrixBlock M hM
  let gh := (ternaryElevenReduction (M 2 0), ternaryElevenReduction (M 2 1))
  let w := ternaryElevenReduction (M 2 2)
  have hr := congrArg (fun N : Matrix (Fin 3) (Fin 3) (ZMod 121) =>
    N.map ternaryElevenReduction) hM
  simp only [Matrix.map_mul, Matrix.transpose_map, ternaryElevenWorkingGram_reduces] at hr
  obtain ⟨hz0, hz1⟩ := ternaryElevenReducedGram_cross_zero (M.map ternaryElevenReduction) hr
  have hsplit0 := ternaryEleven_kernel_split (M 0 2) hz0
  have hsplit1 := ternaryEleven_kernel_split (M 1 2) hz1
  have hc (i : Fin 2) : A.1 0 i * ternaryElevenDigit (M 0 2) +
      2 * A.1 1 i * ternaryElevenDigit (M 1 2) +
        ternaryElevenReduction (M 2 (i.castAdd 1)) * w = 0 := by
    apply ternaryEleven_cross_condition _ _ _ _ _ _ _ _
    simp only [A, ternaryElevenMatrixBlock_entry]
    change (ternaryElevenLift (ternaryElevenReduction (M 0 (i.castAdd 1))) +
      ternaryElevenEmbed (ternaryElevenDigit (M 0 (i.castAdd 1)))) *
      ternaryElevenEmbed (ternaryElevenDigit (M 0 2)) +
      2 * (ternaryElevenLift (ternaryElevenReduction (M 1 (i.castAdd 1))) +
      ternaryElevenEmbed (ternaryElevenDigit (M 1 (i.castAdd 1)))) *
      ternaryElevenEmbed (ternaryElevenDigit (M 1 2)) + 11 * M 2 (i.castAdd 1) * M 2 2 = 0
    rw [← ternaryEleven_split, ← ternaryEleven_split, ← hsplit0, ← hsplit1]
    have h := ternaryElevenWorkingGram_entry M hM (i.castAdd 1) 2
    fin_cases i <;> exact h
  have hlin : (A.1.transpose * ternaryElevenBinaryGram).mulVec
      ![ternaryElevenDigit (M 0 2), ternaryElevenDigit (M 1 2)] = -w • ![gh.1, gh.2] := by
    ext i
    fin_cases i
    · have h := hc 0
      change A.1 0 0 * ternaryElevenDigit (M 0 2) +
        2 * A.1 1 0 * ternaryElevenDigit (M 1 2) + ternaryElevenReduction (M 2 0) * w = 0 at h
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ,
        ternaryElevenBinaryGram, gh]
      linear_combination h
    · have h := hc 1
      change A.1 0 1 * ternaryElevenDigit (M 0 2) +
        2 * A.1 1 1 * ternaryElevenDigit (M 1 2) + ternaryElevenReduction (M 2 1) * w = 0 at h
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ,
        ternaryElevenBinaryGram, gh]
      linear_combination h
  apply Matrix.mulVec_injective_iff_isUnit.mpr (ternaryElevenDerivativeCoefficient A).isUnit
  change (A.1.transpose * ternaryElevenBinaryGram).mulVec _ =
    (A.1.transpose * ternaryElevenBinaryGram).mulVec _
  exact hlin.trans (ternaryElevenCrossColumn_spec A gh w).symm

def ternaryElevenMatrixData (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) :
    ternaryElevenLiftData :=
  ⟨ternaryElevenMatrixBlock M hM,
    (ternaryElevenReduction (M 2 0), ternaryElevenReduction (M 2 1)),
    ⟨ternaryElevenReduction (M 2 2), ternaryElevenWorkingGram_last_sq M hM⟩,
    ⟨ternaryElevenMatrixDigits M, ternaryElevenMatrixDigits_mem M hM⟩⟩

theorem ternaryElevenMatrixData_reconstruct (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) :
    let t := ternaryElevenMatrixData M hM
    let N := ternaryElevenAffineMatrix t.1 t.2.1 t.2.2.1.1 t.2.2.2.1
    ∀ j, M 0 j = N 0 j ∧ M 1 j = N 1 j ∧
      ternaryElevenReduction (M 2 j) = ternaryElevenReduction (N 2 j) := by
  intro t N j
  fin_cases j
  · exact ⟨ternaryEleven_split (M 0 0), ternaryEleven_split (M 1 0),
      (ternaryElevenLift_reduces _).symm⟩
  · exact ⟨ternaryEleven_split (M 0 1), ternaryEleven_split (M 1 1),
      (ternaryElevenLift_reduces _).symm⟩
  · have hr := congrArg (fun Q : Matrix (Fin 3) (Fin 3) (ZMod 121) =>
        Q.map ternaryElevenReduction) hM
    simp only [Matrix.map_mul, Matrix.transpose_map, ternaryElevenWorkingGram_reduces] at hr
    obtain ⟨hz0, hz1⟩ := ternaryElevenReducedGram_cross_zero (M.map ternaryElevenReduction) hr
    have hu := ternaryElevenMatrixCrossDigits M hM
    refine ⟨?_, ?_, (ternaryElevenLift_reduces _).symm⟩
    · change M 0 2 = ternaryElevenEmbed _
      rw [ternaryEleven_kernel_split _ hz0]
      exact congrArg ternaryElevenEmbed (congr_fun hu 0)
    · change M 1 2 = ternaryElevenEmbed _
      rw [ternaryEleven_kernel_split _ hz1]
      exact congrArg ternaryElevenEmbed (congr_fun hu 1)

theorem ternaryEleven_integer_family_roundtrip (P : Matrix (Fin 3) (Fin 3) ℤ) :
    ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix (P.map (Int.castRingHom (ZMod 121)))) =
      ternaryElevenFamilyOfIntegerMatrix P := by
  ext j
  change ternaryElevenDenominator.mkQ (fun i =>
    ternaryElevenIntegerMatrix (P.map (Int.castRingHom (ZMod 121))) i j) =
    ternaryElevenDenominator.mkQ (fun i => P i j)
  rw [ternaryEleven_quotient_eq_iff]
  simp only [ternaryElevenIntegerMatrix, Matrix.map_apply]
  change (((P 0 j : ZMod 121).val : ℤ) : ZMod 121) = (P 0 j : ZMod 121) ∧
    (((P 1 j : ZMod 121).val : ℤ) : ZMod 121) = (P 1 j : ZMod 121) ∧
    (((P 2 j : ZMod 121).val : ℤ) : ZMod 11) = (P 2 j : ZMod 11)
  rw [ternaryEleven_val_reduces]
  simp only [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val, and_self]

theorem ternaryEleven_native_matrix_family
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix (ternaryElevenNativeMatrix Y)) = Y.1 := by
  let P := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix ternaryLattice 11 2 Y
  have h : ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix (ternaryElevenNativeMatrix Y)) =
      ternaryElevenFamilyOfIntegerMatrix P := ternaryEleven_integer_family_roundtrip P
  rw [h]
  ext j
  change ternaryElevenDenominator.mkQ (Quotient.out (Y.1 j)) = Y.1 j
  exact Submodule.Quotient.mk_out _

theorem ternaryElevenLiftDataToNative_surjective : Function.Surjective ternaryElevenLiftDataToNative := by
  intro Y
  let M := ternaryElevenNativeMatrix Y
  have hM := ternaryEleven_native_working_gram Y
  let t := ternaryElevenMatrixData M hM
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix
    (ternaryElevenAffineMatrix t.1 t.2.1 t.2.2.1.1 t.2.2.2.1)) = Y.1
  calc
    _ = ternaryElevenFamilyOfIntegerMatrix (ternaryElevenIntegerMatrix M) := by
      apply (ternaryEleven_integer_family_eq_iff _ _).mpr
      intro j
      obtain ⟨h0, h1, h2⟩ := ternaryElevenMatrixData_reconstruct M hM j
      exact ⟨h0.symm, h1.symm, h2.symm⟩
    _ = _ := ternaryEleven_native_matrix_family Y

theorem ternary_native_count_eleven_two :
    associatedBilinearDualQuotientCount ternaryLattice 11 2 = 53240 := by
  rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  calc
    _ = Nat.card ternaryElevenLiftData :=
      (Nat.card_congr (Equiv.ofBijective ternaryElevenLiftDataToNative
        ⟨ternaryElevenLiftDataToNative_injective, ternaryElevenLiftDataToNative_surjective⟩)).symm
    _ = 53240 := ternaryElevenLiftData_card

theorem ternary_density_eleven : normalizedLocalDensity ternaryLattice 11 = 20 / 121 := by
  rw [ternary_density_eleven_eq_native_count, ternary_native_count_eleven_two]
  norm_num

end MassFormulaReleaseExamples
