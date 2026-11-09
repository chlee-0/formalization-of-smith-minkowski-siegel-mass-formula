import SMSFormula.Applications.Examples.TernaryElevenSymmetricFiber
import SMSFormula.Product
import SMSFormula.Applications.Examples.TernaryDyadicQuotient

/-! The actual nonsingular binary block and its derivative coefficient at 11. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance ternaryElevenPrime : Fact (Nat.Prime 11) := ⟨by decide⟩

def ternaryElevenBinaryGram : TernaryElevenMatrix := !![1, 0; 0, 2]

def ternaryElevenOrthogonalMatrices :=
  {A : TernaryElevenMatrix // A.transpose * ternaryElevenBinaryGram * A =
    ternaryElevenBinaryGram}

theorem ternaryElevenOrthogonalMatrices_det_ne_zero (A : ternaryElevenOrthogonalMatrices) :
    A.1.det ≠ 0 := by
  have hd := congrArg Matrix.det A.2
  simp only [Matrix.det_mul, Matrix.det_transpose] at hd
  have hD : ternaryElevenBinaryGram.det = 2 := by decide
  rw [hD] at hd
  intro hz
  rw [hz] at hd
  norm_num at hd
  exact (by decide : (0 : ZMod 11) ≠ 2) hd

def ternaryElevenOrthogonalGroupEquiv :
    ternaryElevenOrthogonalMatrices ≃ finiteGramOrthogonalGroup ternaryElevenBinaryGram where
  toFun A := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A.1
    (ternaryElevenOrthogonalMatrices_det_ne_zero A), A.2⟩
  invFun A := ⟨(A.1 : TernaryElevenMatrix), A.2⟩
  left_inv _ := rfl
  right_inv A := by
    apply Subtype.ext
    apply Units.ext
    rfl

theorem ternaryElevenOrthogonalMatrices_card : Nat.card ternaryElevenOrthogonalMatrices = 20 := by
  rw [Nat.card_congr ternaryElevenOrthogonalGroupEquiv]
  have hcard := natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_eq_sq
    ternaryElevenBinaryGram (by decide) (by decide)
    (by rw [ZMod.ringChar_zmod_n]; decide) (3 : ZMod 11) (by decide)
  rw [hcard, Nat.card_eq_fintype_card, ZMod.card]

def ternaryElevenDerivativeCoefficient (A : ternaryElevenOrthogonalMatrices) :
    TernaryElevenMatrixˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (A.1.transpose * ternaryElevenBinaryGram) (by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (ternaryElevenOrthogonalMatrices_det_ne_zero A) (by decide))

theorem ternaryElevenDerivativeCoefficient_coe (A : ternaryElevenOrthogonalMatrices) :
    (ternaryElevenDerivativeCoefficient A : TernaryElevenMatrix) =
      A.1.transpose * ternaryElevenBinaryGram := rfl

theorem ternaryEleven_actual_derivative_fiber_card (A : ternaryElevenOrthogonalMatrices)
    (S : TernaryElevenMatrix) (hS : S.IsSymm) :
    Nat.card {X : TernaryElevenMatrix //
      A.1.transpose * ternaryElevenBinaryGram * X +
        X.transpose * ternaryElevenBinaryGram * A.1 = S} = 11 := by
  have hD : ternaryElevenBinaryGram.transpose = ternaryElevenBinaryGram := by decide
  have heq : {X : TernaryElevenMatrix //
      A.1.transpose * ternaryElevenBinaryGram * X +
        X.transpose * ternaryElevenBinaryGram * A.1 = S} =
      ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A) S := by
    unfold ternaryElevenDerivativeFiber
    simp only [ternaryElevenDerivativeCoefficient_coe,
      Matrix.transpose_mul, Matrix.transpose_transpose,
      hD, Matrix.mul_assoc]
  rw [heq]
  exact ternaryElevenDerivativeFiber_card _ S hS


/-- Reduction of the original ternary Gram matrix modulo 11. -/
def ternaryElevenReducedGram : Matrix (Fin 3) (Fin 3) (ZMod 11) :=
  !![1, 0, 0; 0, 2, 0; 0, 0, 0]

def ternaryElevenTopBlock (M : Matrix (Fin 3) (Fin 3) (ZMod 11)) :
    TernaryElevenMatrix := !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem ternaryElevenReducedGram_entry (M : Matrix (Fin 3) (Fin 3) (ZMod 11))
    (hM : M.transpose * ternaryElevenReducedGram * M = ternaryElevenReducedGram)
    (i j : Fin 3) :
    M 0 i * M 0 j + 2 * M 1 i * M 1 j = ternaryElevenReducedGram i j := by
  calc
    _ = (M.transpose * ternaryElevenReducedGram * M) i j := by
      simp [Matrix.mul_apply, Fin.sum_univ_succ, ternaryElevenReducedGram]
      ring_nf
      simp
    _ = _ := congrArg (fun N : Matrix (Fin 3) (Fin 3) (ZMod 11) => N i j) hM

/-- Every reduced Gram solution has an actual orthogonal upper-left block. -/
theorem ternaryElevenTopBlock_orthogonal (M : Matrix (Fin 3) (Fin 3) (ZMod 11))
    (hM : M.transpose * ternaryElevenReducedGram * M = ternaryElevenReducedGram) :
    (ternaryElevenTopBlock M).transpose * ternaryElevenBinaryGram *
      ternaryElevenTopBlock M = ternaryElevenBinaryGram := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [ternaryElevenTopBlock, ternaryElevenBinaryGram, ternaryElevenReducedGram,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_left_comm, mul_comm] using
      ternaryElevenReducedGram_entry M hM 0 0
  · simpa [ternaryElevenTopBlock, ternaryElevenBinaryGram, ternaryElevenReducedGram,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_left_comm, mul_comm] using
      ternaryElevenReducedGram_entry M hM 0 1
  · simpa [ternaryElevenTopBlock, ternaryElevenBinaryGram, ternaryElevenReducedGram,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_left_comm, mul_comm] using
      ternaryElevenReducedGram_entry M hM 1 0
  · simpa [ternaryElevenTopBlock, ternaryElevenBinaryGram, ternaryElevenReducedGram,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_left_comm, mul_comm] using
      ternaryElevenReducedGram_entry M hM 1 1

/-- The two upper-right entries vanish in every reduced Gram solution.
No invertibility assumption on the original three-by-three matrix is used. -/
theorem ternaryElevenReducedGram_cross_zero (M : Matrix (Fin 3) (Fin 3) (ZMod 11))
    (hM : M.transpose * ternaryElevenReducedGram * M = ternaryElevenReducedGram) :
    M 0 2 = 0 ∧ M 1 2 = 0 := by
  let A : ternaryElevenOrthogonalMatrices :=
    ⟨ternaryElevenTopBlock M, ternaryElevenTopBlock_orthogonal M hM⟩
  let C := ternaryElevenDerivativeCoefficient A
  have hc : (C : TernaryElevenMatrix).mulVec ![M 0 2, M 1 2] = 0 := by
    ext i
    fin_cases i
    · simpa [C, ternaryElevenDerivativeCoefficient_coe, A, ternaryElevenTopBlock,
        ternaryElevenBinaryGram, ternaryElevenReducedGram,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        mul_assoc, mul_left_comm, mul_comm] using ternaryElevenReducedGram_entry M hM 0 2
    · simpa [C, ternaryElevenDerivativeCoefficient_coe, A, ternaryElevenTopBlock,
        ternaryElevenBinaryGram, ternaryElevenReducedGram,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        mul_assoc, mul_left_comm, mul_comm] using ternaryElevenReducedGram_entry M hM 1 2
  have hz : ![M 0 2, M 1 2] = (0 : Fin 2 → ZMod 11) := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr C.isUnit
    simpa using hc
  exact ⟨congr_fun hz 0, congr_fun hz 1⟩


/-- The original F-Gram matrix at working modulus 121. -/
def ternaryElevenWorkingGram : Matrix (Fin 3) (Fin 3) (ZMod 121) :=
  !![1, 0, 0; 0, 2, 0; 0, 0, 11]

def ternaryElevenReduction : ZMod 121 →+* ZMod 11 :=
  ZMod.castHom (by decide : 11 ∣ 121) (ZMod 11)

theorem ternaryElevenWorkingGram_reduces :
    ternaryElevenWorkingGram.map ternaryElevenReduction = ternaryElevenReducedGram := by
  decide

def ternaryElevenNativeMatrix
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    Matrix (Fin 3) (Fin 3) (ZMod 121) :=
  (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    ternaryLattice 11 2 Y).map Int.cast

theorem ternaryEleven_native_working_gram
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    let X := ternaryElevenNativeMatrix Y
    X.transpose * ternaryElevenWorkingGram * X = ternaryElevenWorkingGram := by
  have h := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod_gram_congruence
    ternaryLattice 11 2 Y
  have hG : matrixMod ternaryLattice.polarGramMatrix (primePowModulus 11 2) =
      (2 : ZMod 121) • ternaryElevenWorkingGram := by decide
  rw [hG] at h
  let X := ternaryElevenNativeMatrix Y
  have h' : X.transpose * ((2 : ZMod 121) • ternaryElevenWorkingGram) * X =
      (2 : ZMod 121) • ternaryElevenWorkingGram := h
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h'
  have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod 121) => (61 : ZMod 121) • M) h'
  simpa only [smul_smul, show (61 : ZMod 121) * 2 = 1 by decide, one_smul] using hc

theorem ternaryEleven_native_representative_reduces
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    (ternaryElevenNativeMatrix Y).map ternaryElevenReduction =
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
        ternaryLattice 11 2 Y := by
  ext i j
  change ternaryElevenReduction ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    ternaryLattice 11 2 Y i j : ℤ) : ZMod 121) = _
  exact map_intCast ternaryElevenReduction _

theorem ternaryEleven_native_reduced_gram
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    let M := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
      ternaryLattice 11 2 Y
    M.transpose * ternaryElevenReducedGram * M = ternaryElevenReducedGram := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod 121) => M.map ternaryElevenReduction) (ternaryEleven_native_working_gram Y)
  simp only [Matrix.map_mul, Matrix.transpose_map, ternaryElevenWorkingGram_reduces] at h
  rw [ternaryEleven_native_representative_reduces] at h
  exact h

theorem ternaryEleven_native_cross_zero
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    let M := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
      ternaryLattice 11 2 Y
    M 0 2 = 0 ∧ M 1 2 = 0 :=
  ternaryElevenReducedGram_cross_zero _ (ternaryEleven_native_reduced_gram Y)


/-- The square of a residue in the kernel of reduction vanishes modulo 121. -/
theorem ternaryEleven_reduction_zero_sq (a : ZMod 121)
    (ha : ternaryElevenReduction a = 0) : a ^ 2 = 0 := by
  have h : ∀ a : ZMod 121, ternaryElevenReduction a = 0 → a ^ 2 = 0 := by decide +kernel
  exact h a ha

/-- Multiplication by 11 retains exactly one layer of residue information. -/
theorem ternaryEleven_mul_eleven_eq_iff (a : ZMod 121) :
    11 * a = 11 ↔ ternaryElevenReduction a = 1 := by
  have h : ∀ a : ZMod 121, 11 * a = 11 ↔ ternaryElevenReduction a = 1 := by decide +kernel
  exact h a

theorem ternaryElevenWorkingGram_entry (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram)
    (i j : Fin 3) :
    M 0 i * M 0 j + 2 * M 1 i * M 1 j + 11 * M 2 i * M 2 j =
      ternaryElevenWorkingGram i j := by
  calc
    _ = (M.transpose * ternaryElevenWorkingGram * M) i j := by
      simp [Matrix.mul_apply, Fin.sum_univ_succ, ternaryElevenWorkingGram]
      ring
    _ = _ := congrArg (fun N : Matrix (Fin 3) (Fin 3) (ZMod 121) => N i j) hM

/-- The full norm equation forces the reduced lower-right entry to square to one. -/
theorem ternaryElevenWorkingGram_last_sq (M : Matrix (Fin 3) (Fin 3) (ZMod 121))
    (hM : M.transpose * ternaryElevenWorkingGram * M = ternaryElevenWorkingGram) :
    (ternaryElevenReduction (M 2 2)) ^ 2 = 1 := by
  have hr := congrArg (fun N : Matrix (Fin 3) (Fin 3) (ZMod 121) =>
    N.map ternaryElevenReduction) hM
  simp only [Matrix.map_mul, Matrix.transpose_map, ternaryElevenWorkingGram_reduces] at hr
  obtain ⟨h0, h1⟩ := ternaryElevenReducedGram_cross_zero (M.map ternaryElevenReduction) hr
  have hs0 := ternaryEleven_reduction_zero_sq (M 0 2) h0
  have hs1 := ternaryEleven_reduction_zero_sq (M 1 2) h1
  have hn := ternaryElevenWorkingGram_entry M hM 2 2
  change M 0 2 * M 0 2 + 2 * M 1 2 * M 1 2 + 11 * M 2 2 * M 2 2 = 11 at hn
  have hnorm : (11 : ZMod 121) * (M 2 2) ^ 2 = 11 := by
    linear_combination hn - hs0 - 2 * hs1
  have hred := (ternaryEleven_mul_eleven_eq_iff ((M 2 2)^2)).mp hnorm
  simpa only [map_pow] using hred

theorem ternaryEleven_native_last_sq
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    let M := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
      ternaryLattice 11 2 Y
    M 2 2 ^ 2 = 1 := by
  have h := ternaryElevenWorkingGram_last_sq (ternaryElevenNativeMatrix Y)
    (ternaryEleven_native_working_gram Y)
  have hr := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod 11) => M 2 2)
    (ternaryEleven_native_representative_reduces Y)
  change (ternaryElevenReduction (ternaryElevenNativeMatrix Y 2 2)) = _ at hr
  rw [hr] at h
  exact h

theorem ternaryEleven_last_roots_card : Nat.card {w : ZMod 11 // w ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide


/-- Canonical integer representatives of the actual binary orthogonal block. -/
def ternaryElevenIntegerBlock (A : ternaryElevenOrthogonalMatrices) : Matrix (Fin 2) (Fin 2) ℤ :=
  A.1.map (fun z => (z.val : ℤ))

def ternaryElevenIntegerGram : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 2]

def ternaryElevenLiftError (A : ternaryElevenOrthogonalMatrices) : Matrix (Fin 2) (Fin 2) ℤ :=
  ternaryElevenIntegerGram -
    (ternaryElevenIntegerBlock A).transpose * ternaryElevenIntegerGram * ternaryElevenIntegerBlock A

theorem ternaryElevenIntegerBlock_reduces (A : ternaryElevenOrthogonalMatrices) :
    (ternaryElevenIntegerBlock A).map (Int.castRingHom (ZMod 11)) = A.1 := by
  ext i j
  change (((A.1 i j).val : ℤ) : ZMod 11) = A.1 i j
  simp

theorem ternaryElevenLiftError_dvd (A : ternaryElevenOrthogonalMatrices) (i j : Fin 2) :
    (11 : ℤ) ∣ ternaryElevenLiftError A i j := by
  have h : (ternaryElevenLiftError A).map (Int.cast : ℤ → ZMod 11) = 0 := by
    change (ternaryElevenLiftError A).map (Int.castRingHom (ZMod 11)) = 0
    have hG : ternaryElevenIntegerGram.map (Int.castRingHom (ZMod 11)) =
        ternaryElevenBinaryGram := by decide
    rw [ternaryElevenLiftError, Matrix.map_sub _ (by
      intro a b
      exact map_sub (Int.castRingHom (ZMod 11)) a b)]
    simp only [Matrix.map_mul, Matrix.transpose_map,
      ternaryElevenIntegerBlock_reduces, hG, A.2, sub_self]
  have hij := congrArg (fun M : TernaryElevenMatrix => M i j) h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).mp hij

/-- The affine derivative target includes the canonical base-lift error and
both free lower-left entries. -/
def ternaryElevenLiftTarget (A : ternaryElevenOrthogonalMatrices) (gh : ZMod 11 × ZMod 11) :
    TernaryElevenMatrix :=
  (ternaryElevenLiftError A).map (fun z => ((z / 11 : ℤ) : ZMod 11)) -
    !![gh.1 ^ 2, gh.1 * gh.2; gh.1 * gh.2, gh.2 ^ 2]

theorem ternaryElevenLiftTarget_symm (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) : (ternaryElevenLiftTarget A gh).IsSymm := by
  have hG : ternaryElevenIntegerGram.transpose = ternaryElevenIntegerGram := by decide
  have he : (ternaryElevenLiftError A).transpose = ternaryElevenLiftError A := by
    simp only [ternaryElevenLiftError, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hG, Matrix.mul_assoc]
  change (ternaryElevenLiftTarget A gh).transpose = ternaryElevenLiftTarget A gh
  rw [ternaryElevenLiftTarget, Matrix.transpose_sub, ← Matrix.transpose_map, he]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Parameter data for the block-lift route. The equivalence with all native
families is not proved here. -/
def ternaryElevenLiftData :=
  Σ A : ternaryElevenOrthogonalMatrices,
    Σ gh : ZMod 11 × ZMod 11,
      Σ _w : {w : ZMod 11 // w ^ 2 = 1},
        ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A)
          (ternaryElevenLiftTarget A gh)

def ternaryElevenAffineFiberEquiv (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) :
    ternaryElevenDerivativeFiber (ternaryElevenDerivativeCoefficient A)
      (ternaryElevenLiftTarget A gh) ≃ ZMod 11 :=
  (ternaryElevenDerivativeFiberEquiv _ _).trans
    (ternaryElevenSymmetricFiberEquiv _ (ternaryElevenLiftTarget_symm A gh))

def ternaryElevenLiftDataEquiv : ternaryElevenLiftData ≃
    ternaryElevenOrthogonalMatrices × (ZMod 11 × ZMod 11) ×
      {w : ZMod 11 // w ^ 2 = 1} × ZMod 11 where
  toFun t := (t.1, t.2.1, t.2.2.1,
    ternaryElevenAffineFiberEquiv t.1 t.2.1 t.2.2.2)
  invFun t := ⟨t.1, t.2.1, t.2.2.1,
    (ternaryElevenAffineFiberEquiv t.1 t.2.1).symm t.2.2.2⟩
  left_inv t := by
    rcases t with ⟨A, gh, w, X⟩
    change (⟨A, gh, w, (ternaryElevenAffineFiberEquiv A gh).symm
      (ternaryElevenAffineFiberEquiv A gh X)⟩ : ternaryElevenLiftData) = ⟨A, gh, w, X⟩
    rw [Equiv.symm_apply_apply]
  right_inv t := by
    rcases t with ⟨A, gh, w, x⟩
    change (A, gh, w, ternaryElevenAffineFiberEquiv A gh
      ((ternaryElevenAffineFiberEquiv A gh).symm x)) = (A, gh, w, x)
    rw [Equiv.apply_symm_apply]

theorem ternaryElevenLiftData_card : Nat.card ternaryElevenLiftData = 53240 := by
  rw [Nat.card_congr ternaryElevenLiftDataEquiv]
  simp only [Nat.card_prod, ternaryElevenOrthogonalMatrices_card, ternaryEleven_last_roots_card]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]


/-- The upper-right column divided by 11 is fixed by the cross equations. -/
def ternaryElevenCrossColumn (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (w : ZMod 11) : Fin 2 → ZMod 11 :=
  (((ternaryElevenDerivativeCoefficient A)⁻¹ : TernaryElevenMatrixˣ) :
    TernaryElevenMatrix).mulVec (-w • ![gh.1, gh.2])

theorem ternaryElevenCrossColumn_unique (A : ternaryElevenOrthogonalMatrices)
    (gh : ZMod 11 × ZMod 11) (w : ZMod 11) :
    ∃! u : Fin 2 → ZMod 11,
      (A.1.transpose * ternaryElevenBinaryGram).mulVec u = -w • ![gh.1, gh.2] := by
  let C := ternaryElevenDerivativeCoefficient A
  have hu : (C : TernaryElevenMatrix).mulVec (ternaryElevenCrossColumn A gh w) =
      -w • ![gh.1, gh.2] := by
    simp [ternaryElevenCrossColumn, C, Matrix.mulVec_mulVec]
  refine ⟨ternaryElevenCrossColumn A gh w, hu, ?_⟩
  intro u hu'
  apply Matrix.mulVec_injective_iff_isUnit.mpr C.isUnit
  exact hu'.trans hu.symm


/-- Residue data retained by a native family: orthogonal block, free lower-left
entries, and a square root of one in the last diagonal position. -/
def ternaryElevenBaseData :=
  ternaryElevenOrthogonalMatrices × (ZMod 11 × ZMod 11) × {w : ZMod 11 // w ^ 2 = 1}

def ternaryElevenNativeBaseData
    (Y : associatedBilinearDualQuotientSolutionFamily ternaryLattice 11 2) :
    ternaryElevenBaseData :=
  let M := associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
    ternaryLattice 11 2 Y
  (⟨ternaryElevenTopBlock M, ternaryElevenTopBlock_orthogonal M
      (ternaryEleven_native_reduced_gram Y)⟩,
    (M 2 0, M 2 1), ⟨M 2 2, ternaryEleven_native_last_sq Y⟩)

theorem ternaryElevenBaseData_card : Nat.card ternaryElevenBaseData = 4840 := by
  unfold ternaryElevenBaseData
  simp only [Nat.card_prod, ternaryElevenOrthogonalMatrices_card, ternaryEleven_last_roots_card]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end MassFormulaReleaseExamples
