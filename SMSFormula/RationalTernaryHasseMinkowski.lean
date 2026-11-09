import SMSFormula.MatrixCongruence
import SMSFormula.RationalLegendre
import SMSFormula.RationalPadicNorm
import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# Ternary rational Hasse--Minkowski

This leaf module combines rational diagonalization with the direct
diagonal ternary theorem.
-/

noncomputable section

open scoped Matrix

namespace Rat

/-- A rational Gram-isotropy witness remains isotropic after scalar extension
to any characteristic-zero field. -/
theorem gramIsotropic_scalarExtension_of_rat
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : PositiveDefiniteIntegralLattice.GramIsotropic A) :
    PositiveDefiniteIntegralLattice.GramIsotropic (A.map (algebraMap ℚ K)) := by
  rcases hA with ⟨x, hx, hvalue⟩
  refine ⟨fun i ↦ (x i : K), ?_, ?_⟩
  · intro hzero
    apply hx
    funext i
    have hi := congrFun hzero i
    apply (algebraMap ℚ K).injective
    simpa using hi
  · have hmap := congrArg (algebraMap ℚ K) hvalue
    simpa [PositiveDefiniteIntegralLattice.gramQuadraticValue, Matrix.mulVec, dotProduct]
      using hmap

private theorem map_diagonal_fin_three
    {K : Type*} [Field K] [CharZero K] (d : Fin 3 → ℚ) :
    (Matrix.diagonal d).map (algebraMap ℚ K) =
      Matrix.diagonal ![(d 0 : K), (d 1 : K), (d 2 : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- A nonsingular symmetric rational ternary Gram matrix that is isotropic
over the reals and every p-adic field is isotropic over the rationals. -/
theorem ternaryGramIsotropic_rat_of_real_and_padic
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (A.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (A.map (algebraMap ℚ ℚ_[p]))) :
    PositiveDefiniteIntegralLattice.GramIsotropic A := by
  obtain ⟨d, P, hd, hP, hA_iff⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det (by norm_num)
  have hcongr : A.IsCongruent (Matrix.diagonal d) := ⟨P, hP⟩
  have hreal_diagonal : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![(d 0 : ℝ), (d 1 : ℝ), (d 2 : ℝ)]) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map (algebraMap ℚ ℝ)) hreal
    simpa only [map_diagonal_fin_three] using h
  have hpadic_diagonal : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal
          ![(d 0 : ℚ_[p]), (d 1 : ℚ_[p]), (d 2 : ℚ_[p])]) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa only [map_diagonal_fin_three] using h
  have hdiagonal : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2]) :=
    (ternaryDiagonal_gramIsotropic_iff_real_and_padic
      (d 0) (d 1) (d 2) (hd 0) (hd 1) (hd 2)).mpr
      ⟨hreal_diagonal, hpadic_diagonal⟩
  apply hA_iff.mpr
  have hd_eq : d = ![d 0, d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hd_eq]
  exact hdiagonal

/-- Ternary Hasse--Minkowski for arbitrary nonsingular symmetric rational
Gram matrices. -/
theorem ternaryGramIsotropic_iff_real_and_padic
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic A ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (A.map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (A.map (algebraMap ℚ ℚ_[p])) := by
  constructor
  · intro hA
    exact ⟨gramIsotropic_scalarExtension_of_rat (K := ℝ) hA,
      fun p _ ↦ gramIsotropic_scalarExtension_of_rat (K := ℚ_[p]) hA⟩
  · rintro ⟨hreal, hpadic⟩
    exact ternaryGramIsotropic_rat_of_real_and_padic
      A hA_symm hA_det hreal hpadic

/-- A rational represented-value witness remains a represented-value witness
after scalar extension to any characteristic-zero field. -/
theorem exists_gramQuadraticValue_eq_scalarExtension_of_rat
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {c : ℚ}
    (hrep : ∃ v : Fin n → ℚ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) :
    ∃ v : Fin n → K,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) v = (c : K) := by
  obtain ⟨v, hv⟩ := hrep
  refine ⟨fun i ↦ (v i : K), ?_⟩
  have hmap := congrArg (algebraMap ℚ K) hv
  simpa [PositiveDefiniteIntegralLattice.gramQuadraticValue, Matrix.mulVec, dotProduct]
    using hmap

/-- A nonzero scalar locally represented by a nonsingular symmetric rational
binary form is represented over the rationals. -/
theorem exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0)
    (hreal : ∃ v : Fin 2 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 2 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p])) :
    ∃ v : Fin 2 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c := by
  let B : Matrix (Fin 3) (Fin 3) ℚ :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock (-c) A
  have hB_symm : B.IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm (-c) A hA_symm
  have hB_det : B.det ≠ 0 := by
    simp only [B, PositiveDefiniteIntegralLattice.finSuccGramBlock_det]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hA_det
  have hB_real : PositiveDefiniteIntegralLattice.GramIsotropic
      (B.map (algebraMap ℚ ℝ)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℝ) (A.map (algebraMap ℚ ℝ)) hreal
    simpa [B] using h
  have hB_padic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (B.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_finSuccGramBlock_of_exists_value
      (c : ℚ_[p]) (A.map (algebraMap ℚ ℚ_[p])) (hpadic p)
    simpa [B] using h
  have hB : PositiveDefiniteIntegralLattice.GramIsotropic B :=
    ternaryGramIsotropic_rat_of_real_and_padic
      B hB_symm hB_det hB_real hB_padic
  rcases PositiveDefiniteIntegralLattice.gramIsotropic_or_exists_value_of_finSuccGramBlock
      c A hB with hA | hrep
  · exact PositiveDefiniteIntegralLattice.exists_binary_gramQuadraticValue_eq_of_gramIsotropic
      A hA_symm hA_det (by norm_num) hA c
  · exact hrep

/-- Nonzero scalar representation by a nonsingular symmetric rational binary
form is equivalent to representation over the real and every p-adic field. -/
theorem exists_binary_gramQuadraticValue_eq_iff_real_and_padic
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (c : ℚ) (hc : c ≠ 0) :
    (∃ v : Fin 2 → ℚ, PositiveDefiniteIntegralLattice.gramQuadraticValue A v = c) ↔
      (∃ v : Fin 2 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (c : ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin 2 → ℚ_[p],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  constructor
  · intro hrep
    exact ⟨exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℝ) hrep,
      fun p _ ↦ exists_gramQuadraticValue_eq_scalarExtension_of_rat
        (K := ℚ_[p]) hrep⟩
  · rintro ⟨hreal, hpadic⟩
    exact exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
      A hA_symm hA_det c hc hreal hpadic

private theorem exists_common_differenceGramBlock_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K] {m n : ℕ} [NeZero m] [NeZero n]
    (M : Matrix (Fin (m + n)) (Fin (m + n)) ℚ)
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (P : GL (Fin (m + n)) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 = PositiveDefiniteIntegralLattice.differenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin m → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin n → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent (PositiveDefiniteIntegralLattice.differenceGramBlock A B) :=
    ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.differenceGramBlock (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    exact hA_det (f.injective (by simpa using hf))
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    exact hB_det (f.injective (by simpa using hf))
  exact
    (PositiveDefiniteIntegralLattice.gramIsotropic_differenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational form on
`Fin (m+n)` supplies fixed rational difference blocks with a common nonzero
represented value at every completion. -/
theorem exists_differenceGramBlock_common_values_of_real_and_padic
    {m n : ℕ} [NeZero m] [NeZero n]
    (M : Matrix (Fin (m + n)) (Fin (m + n)) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A : Matrix (Fin m) (Fin m) ℚ)
      (B : Matrix (Fin n) (Fin n) ℚ) (P : GL (Fin (m + n)) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 = PositiveDefiniteIntegralLattice.differenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin m → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin n → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin m → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin n → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_differenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_differenceGramBlock_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_differenceGramBlock_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_binary_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 4) (Fin 4) ℚ)
    (A B : Matrix (Fin 2) (Fin 2) ℚ) (P : GL (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 2 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 2 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact (PositiveDefiniteIntegralLattice.gramIsotropic_binaryPairDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-four
form supplies fixed rational binary blocks with a common nonzero represented
value at every completion. -/
theorem exists_binaryPairDifferenceGramBlock_common_values_of_rankFour_real_and_padic
    (M : Matrix (Fin 4) (Fin 4) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A B : Matrix (Fin 2) (Fin 2) ℚ) (P : GL (Fin 4) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.binaryPairDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 2 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 2 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 2 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 2 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_binaryPairDifferenceGramBlock_gramIsotropic_iff
        M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_binary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_binary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_binary_ternary_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 5) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ) (P : GL (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 2 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact (PositiveDefiniteIntegralLattice.gramIsotropic_binaryTernaryDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-five
form supplies fixed rational binary and ternary blocks with a common nonzero
represented value at every completion. -/
theorem exists_binaryTernaryDifferenceGramBlock_common_values_of_rankFive_real_and_padic
    (M : Matrix (Fin 5) (Fin 5) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℚ)
      (B : Matrix (Fin 3) (Fin 3) ℚ) (P : GL (Fin 5) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.binaryTernaryDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 2 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 2 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_binaryTernaryDifferenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_binary_ternary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_binary_ternary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_ternary_pair_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 6) (Fin 6) ℚ)
    (A B : Matrix (Fin 3) (Fin 3) ℚ) (P : GL (Fin 6) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact (PositiveDefiniteIntegralLattice.gramIsotropic_ternaryPairDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-six
form supplies fixed rational ternary blocks with a common nonzero represented
value at every completion. -/
theorem exists_ternaryPairDifferenceGramBlock_common_values_of_rankSix_real_and_padic
    (M : Matrix (Fin 6) (Fin 6) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A B : Matrix (Fin 3) (Fin 3) ℚ) (P : GL (Fin 6) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.ternaryPairDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_ternaryPairDifferenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_ternary_pair_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_ternary_pair_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_ternary_quaternary_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 7) (Fin 7) ℚ)
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ) (P : GL (Fin 7) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 3 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock
        (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact
    (PositiveDefiniteIntegralLattice.gramIsotropic_ternaryQuaternaryDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-seven
form supplies fixed rational ternary and quaternary blocks with a common
nonzero represented value at every completion. -/
theorem exists_ternaryQuaternaryDifferenceGramBlock_common_values_of_rankSeven_real_and_padic
    (M : Matrix (Fin 7) (Fin 7) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℚ)
      (B : Matrix (Fin 4) (Fin 4) ℚ) (P : GL (Fin 7) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.ternaryQuaternaryDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 3 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 3 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_ternaryQuaternaryDifferenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_ternary_quaternary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_ternary_quaternary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_quaternary_pair_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 8) (Fin 8) ℚ)
    (A B : Matrix (Fin 4) (Fin 4) ℚ) (P : GL (Fin 8) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock
        (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact
    (PositiveDefiniteIntegralLattice.gramIsotropic_quaternaryPairDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-eight
form supplies fixed rational quaternary blocks with a common nonzero
represented value at every completion. -/
theorem exists_quaternaryPairDifferenceGramBlock_common_values_of_rankEight_real_and_padic
    (M : Matrix (Fin 8) (Fin 8) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A B : Matrix (Fin 4) (Fin 4) ℚ) (P : GL (Fin 8) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.quaternaryPairDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_quaternaryPairDifferenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_quaternary_pair_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_quaternary_pair_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_quaternary_quinary_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 9) (Fin 9) ℚ)
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ) (P : GL (Fin 9) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 4 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 5 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock
        (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact
    (PositiveDefiniteIntegralLattice.gramIsotropic_quaternaryQuinaryDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-nine
form supplies fixed rational quaternary and quinary blocks with a common
nonzero represented value at every completion. -/
theorem exists_quaternaryQuinaryDifferenceGramBlock_common_values_of_rankNine_real_and_padic
    (M : Matrix (Fin 9) (Fin 9) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A : Matrix (Fin 4) (Fin 4) ℚ)
      (B : Matrix (Fin 5) (Fin 5) ℚ) (P : GL (Fin 9) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.quaternaryQuinaryDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 4 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 4 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_quaternaryQuinaryDifferenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_quaternary_quinary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_quaternary_quinary_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

private theorem exists_common_quinary_pair_value_of_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 10) (Fin 10) ℚ)
    (A B : Matrix (Fin 5) (Fin 5) ℚ) (P : GL (Fin 10) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hP : P.1ᵀ * M * P.1 =
      PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock A B)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ K))) :
    ∃ c : K, c ≠ 0 ∧
      (∃ u : Fin 5 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ K)) u = c) ∧
      ∃ v : Fin 5 → K, PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ K)) v = c := by
  let f := algebraMap ℚ K
  have hcongr : M.IsCongruent
      (PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock A B) := ⟨P, hP⟩
  have hblock : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock
        (A.map f) (B.map f)) := by
    have h := PositiveDefiniteIntegralLattice.gramIsotropic_of_isCongruent
      (hcongr.map f) hiso
    simpa [f] using h
  have hA_symm_map : (A.map f).IsSymm := hA_symm.map f
  have hB_symm_map : (B.map f).IsSymm := hB_symm.map f
  have hA_det_map : (A.map f).det ≠ 0 := by
    have hdet : (A.map f).det = f A.det := by
      simpa using (RingHom.map_det f A).symm
    rw [hdet]
    intro hf
    apply hA_det
    apply f.injective
    simpa using hf
  have hB_det_map : (B.map f).det ≠ 0 := by
    have hdet : (B.map f).det = f B.det := by
      simpa using (RingHom.map_det f B).symm
    rw [hdet]
    intro hf
    apply hB_det
    apply f.injective
    simpa using hf
  exact
    (PositiveDefiniteIntegralLattice.gramIsotropic_quinaryPairDifferenceGramBlock_iff_exists_common_value
      (A.map f) (B.map f) hA_symm_map hA_det_map hB_symm_map hB_det_map
      (by norm_num)).mp hblock

/-- Real and p-adic isotropy of a nonsingular symmetric rational rank-ten
form supplies fixed rational quinary blocks with a common nonzero represented
value at every completion. -/
theorem exists_quinaryPairDifferenceGramBlock_common_values_of_rankTen_real_and_padic
    (M : Matrix (Fin 10) (Fin 10) ℚ)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (M.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (M.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (A B : Matrix (Fin 5) (Fin 5) ℚ) (P : GL (Fin 10) ℚ),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
      P.1ᵀ * M * P.1 =
        PositiveDefiniteIntegralLattice.quinaryPairDifferenceGramBlock A B ∧
      (∃ c : ℝ, c ≠ 0 ∧
        (∃ u : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℝ)) u = c) ∧
        ∃ v : Fin 5 → ℝ, PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℝ)) v = c) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℚ_[p], c ≠ 0 ∧
        (∃ u : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
        ∃ v : Fin 5 → ℚ_[p], PositiveDefiniteIntegralLattice.gramQuadraticValue
          (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, _hiso⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_quinaryPairDifferenceGramBlock_gramIsotropic_iff
      M hM_symm hM_det (by norm_num)
  refine ⟨A, B, P, hA_symm, hA_det, hB_symm, hB_det, hP, ?_, ?_⟩
  · exact exists_common_quinary_pair_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP hreal
  · intro p hp
    exact exists_common_quinary_pair_value_of_scalarExtension
      M A B P hA_symm hA_det hB_symm hB_det hP (hpadic p)

/-- A p-adic number sufficiently close to one is a square. The radius works
uniformly at odd and dyadic primes. -/
theorem padic_isSquare_of_norm_sub_one_lt_norm_two_sq
    {p : ℕ} [Fact p.Prime] {q : ℚ_[p]}
    (hq : ‖q - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2) : IsSquare q := by
  have htwo_le : ‖(2 : ℚ_[p])‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one ℚ_[p] 2
  have htwo_sq_le : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (2 : ℚ_[p])]
  have hq_sub_one_lt : ‖q - 1‖ < 1 := hq.trans_le htwo_sq_le
  have hq_le : ‖q‖ ≤ 1 := by
    calc
      ‖q‖ = ‖(q - 1) + 1‖ := by ring_nf
      _ ≤ max ‖q - 1‖ ‖(1 : ℚ_[p])‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by simp [hq_sub_one_lt.le]
  let u : ℤ_[p] := ⟨q, hq_le⟩
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u
  have hFeval : F.aeval (1 : ℤ_[p]) = 1 - u := by
    simp [F]
  have hdeval : F.derivative.aeval (1 : ℤ_[p]) = 2 := by
    norm_num [F]
  have hnorm :
      ‖F.aeval (1 : ℤ_[p])‖ <
        ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hFeval, hdeval]
    change ‖(1 : ℚ_[p]) - q‖ < ‖(2 : ℚ_[p])‖ ^ 2
    simpa [norm_sub_rev] using hq
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[p]), ?_⟩
  have hz' : z ^ 2 = u := sub_eq_zero.mp (by simpa [F] using hz)
  have hzc := congrArg (fun w : ℤ_[p] ↦ (w : ℚ_[p])) hz'
  simpa [u, pow_two] using hzc.symm

/-- The explicit p-adic ball around a nonzero scalar lies in its nonzero
square orbit. -/
theorem exists_padic_nonzero_sq_mul_eq_of_mem_ball
    {p : ℕ} [Fact p.Prime] {c y : ℚ_[p]} (hc : c ≠ 0)
    (hy : y ∈ Metric.ball c (‖c‖ * ‖(2 : ℚ_[p])‖ ^ 2)) :
    ∃ s : ℚ_[p], s ≠ 0 ∧ y = s ^ 2 * c := by
  have hratio : ‖y / c - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2 := by
    rw [show y / c - 1 = (y - c) / c by field_simp]
    rw [norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hc)).2
    simpa [Metric.mem_ball, dist_eq_norm, mul_comm] using hy
  have htwo_le : ‖(2 : ℚ_[p])‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one ℚ_[p] 2
  have htwo_sq_le : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (2 : ℚ_[p])]
  have hratio_ne : y / c ≠ 0 := by
    intro hzero
    rw [hzero] at hratio
    have hone_lt : (1 : ℝ) < ‖(2 : ℚ_[p])‖ ^ 2 := by
      simpa using hratio
    exact (not_lt_of_ge htwo_sq_le) hone_lt
  obtain ⟨s, hs⟩ := padic_isSquare_of_norm_sub_one_lt_norm_two_sq hratio
  have hs_sq : s ^ 2 = y / c := by
    simpa [pow_two] using hs.symm
  refine ⟨s, ?_, ?_⟩
  · intro hs0
    apply hratio_ne
    rw [← hs_sq, hs0]
    simp
  · rw [hs_sq]
    field_simp

/-- Every nonzero real scalar has an open neighborhood contained in its
nonzero-square orbit. -/
theorem exists_isOpen_mem_subset_real_nonzeroSqOrbit
    {c : ℝ} (hc : c ≠ 0) :
    ∃ U : Set ℝ, IsOpen U ∧ c ∈ U ∧
      U ⊆ {y | ∃ s : ℝ, s ≠ 0 ∧ y = s ^ 2 * c} := by
  by_cases hcpos : 0 < c
  · refine ⟨Set.Ioi 0, isOpen_Ioi, hcpos, ?_⟩
    intro y hy
    let s := Real.sqrt (y / c)
    have hratio : 0 < y / c := div_pos hy hcpos
    have hs_sq : s ^ 2 = y / c := Real.sq_sqrt hratio.le
    refine ⟨s, Real.sqrt_ne_zero'.mpr hratio, ?_⟩
    rw [hs_sq]
    field_simp
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    refine ⟨Set.Iio 0, isOpen_Iio, hcneg, ?_⟩
    intro y hy
    let s := Real.sqrt (y / c)
    have hratio : 0 < y / c := div_pos_of_neg_of_neg hy hcneg
    have hs_sq : s ^ 2 = y / c := Real.sq_sqrt hratio.le
    refine ⟨s, Real.sqrt_ne_zero'.mpr hratio, ?_⟩
    rw [hs_sq]
    field_simp

/-- Every nonzero p-adic scalar has an open neighborhood contained in its
nonzero-square orbit. -/
theorem exists_isOpen_mem_subset_padic_nonzeroSqOrbit
    {p : ℕ} [Fact p.Prime] {c : ℚ_[p]} (hc : c ≠ 0) :
    ∃ U : Set ℚ_[p], IsOpen U ∧ c ∈ U ∧
      U ⊆ {y | ∃ s : ℚ_[p], s ≠ 0 ∧ y = s ^ 2 * c} := by
  refine ⟨Metric.ball c (‖c‖ * ‖(2 : ℚ_[p])‖ ^ 2),
    Metric.isOpen_ball, ?_, ?_⟩
  · apply Metric.mem_ball_self
    exact mul_pos (norm_pos_iff.mpr hc)
      (pow_pos (norm_pos_iff.mpr (by norm_num)) 2)
  · intro y hy
    exact exists_padic_nonzero_sq_mul_eq_of_mem_ball hc hy

/-- A nonzero common represented real value lies in an open set of common
represented values. -/
theorem exists_isOpen_mem_subset_real_binaryCommonRepresents
    {A B : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (hc : c ≠ 0)
    (hcommon : PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B c) :
    ∃ U : Set ℝ, IsOpen U ∧ c ∈ U ∧
      U ⊆ {y | PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B y} := by
  obtain ⟨U, hUopen, hcU, hU⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit hc
  refine ⟨U, hUopen, hcU, ?_⟩
  intro y hy
  obtain ⟨s, _hs, rfl⟩ := hU hy
  exact hcommon.sq_mul s

/-- A nonzero common represented p-adic value lies in an open set of common
represented values. -/
theorem exists_isOpen_mem_subset_padic_binaryCommonRepresents
    {p : ℕ} [Fact p.Prime]
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]} {c : ℚ_[p]}
    (hc : c ≠ 0)
    (hcommon : PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B c) :
    ∃ U : Set ℚ_[p], IsOpen U ∧ c ∈ U ∧
      U ⊆ {y | PositiveDefiniteIntegralLattice.BinaryCommonRepresents A B y} := by
  obtain ⟨U, hUopen, hcU, hU⟩ :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit hc
  refine ⟨U, hUopen, hcU, ?_⟩
  intro y hy
  obtain ⟨s, _hs, rfl⟩ := hU hy
  exact hcommon.sq_mul s

/-- The product of the reduced denominators of all entries of a rational
square matrix. -/
def matrixDenominatorProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∏ i, ∏ j, (A i j).den

/-- A natural support containing two, all entry denominators, and the reduced
numerators and denominators of the determinants of two rational square
matrices. -/
def matrixPairBadPrimeSupportNat {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  2 * matrixDenominatorProduct A * matrixDenominatorProduct B *
    A.det.num.natAbs * A.det.den * B.det.num.natAbs * B.det.den

/-- The finite set of primes where two rational square matrices need not have
unimodular integral models. -/
def matrixPairBadPrimeSet {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) : Finset ℕ :=
  (matrixPairBadPrimeSupportNat A B).primeFactors

lemma matrix_entry_den_dvd_denominatorProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (A i j).den ∣ matrixDenominatorProduct A := by
  apply dvd_trans
    (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j))
  exact Finset.dvd_prod_of_mem
    (fun i => ∏ j, (A i j).den) (Finset.mem_univ i)

lemma matrixPairBadPrimeSupportNat_ne_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0) :
    matrixPairBadPrimeSupportNat A B ≠ 0 := by
  have hAden : matrixDenominatorProduct A ≠ 0 := by
    simp only [matrixDenominatorProduct]
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact (A i j).den_nz
  have hBden : matrixDenominatorProduct B ≠ 0 := by
    simp only [matrixDenominatorProduct]
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact (B i j).den_nz
  simp [matrixPairBadPrimeSupportNat, hAden, hBden,
    Rat.num_ne_zero.mpr hA_det, Rat.num_ne_zero.mpr hB_det]

/-- For a prime, membership in the bad-prime set is exactly divisibility of
the explicit natural support. -/
lemma prime_mem_matrixPairBadPrimeSet_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    p ∈ matrixPairBadPrimeSet A B ↔
      p ∣ matrixPairBadPrimeSupportNat A B := by
  rw [matrixPairBadPrimeSet, Nat.mem_primeFactors]
  simp [hp, matrixPairBadPrimeSupportNat_ne_zero A B hA_det hB_det]

/-- Entrywise integral model of a rational square matrix at a prime avoiding
all entry denominators. -/
def rationalMatrixPadicInt
    {p n : ℕ} [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (hden : ∀ i j, ¬p ∣ (A i j).den) :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  fun i j => ⟨(A i j : ℚ_[p]), Padic.norm_rat_le_one (hden i j)⟩

@[simp] lemma rationalMatrixPadicInt_map
    {p n : ℕ} [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (hden : ∀ i j, ¬p ∣ (A i j).den) :
    (rationalMatrixPadicInt A hden).map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) := by
  rfl

lemma rationalMatrixPadicInt_isSymm
    {p n : ℕ} [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm)
    (hden : ∀ i j, ¬p ∣ (A i j).den) :
    (rationalMatrixPadicInt A hden).IsSymm := by
  ext i j
  apply Subtype.ext
  exact congrArg (fun q : ℚ => (q : ℚ_[p])) (hA_symm.apply i j)

lemma rationalMatrixPadicInt_det_isUnit
    {p n : ℕ} [Fact p.Prime] (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_det : A.det ≠ 0)
    (hden : ∀ i j, ¬p ∣ (A i j).den)
    (hdetnum : ¬p ∣ A.det.num.natAbs)
    (hdetden : ¬p ∣ A.det.den) :
    IsUnit (rationalMatrixPadicInt A hden).det := by
  have hmap := rationalMatrixPadicInt_map A hden
  have hdetcast :
      (((rationalMatrixPadicInt A hden).det : ℤ_[p]) : ℚ_[p]) =
        (A.det : ℚ_[p]) := by
    calc
      (((rationalMatrixPadicInt A hden).det : ℤ_[p]) : ℚ_[p]) =
          ((rationalMatrixPadicInt A hden).map
            PadicInt.Coe.ringHom).det := by
        simpa using (RingHom.map_det PadicInt.Coe.ringHom
          (rationalMatrixPadicInt A hden))
      _ = (A.map (algebraMap ℚ ℚ_[p])).det := congrArg Matrix.det hmap
      _ = (A.det : ℚ_[p]) :=
        (RingHom.map_det (algebraMap ℚ ℚ_[p]) A).symm
  have hval : padicValRat p A.det = 0 := by
    rw [padicValRat_def, padicValInt,
      ← Nat.factorization_def _ (Fact.out : p.Prime),
      ← Nat.factorization_def _ (Fact.out : p.Prime),
      Nat.factorization_eq_zero_of_not_dvd hdetnum,
      Nat.factorization_eq_zero_of_not_dvd hdetden]
    norm_num
  rw [PadicInt.isUnit_iff]
  change
    ‖(((rationalMatrixPadicInt A hden).det : ℤ_[p]) : ℚ_[p])‖ = 1
  rw [hdetcast, Padic.norm_eq_zpow_neg_valuation]
  · simp [Padic.valuation_ratCast, hval]
  · exact_mod_cast hA_det

/-- Compatibility alias for the denominator product of a rational binary
matrix. -/
def binaryMatrixDenominatorProduct
    (A : Matrix (Fin 2) (Fin 2) ℚ) : ℕ :=
  matrixDenominatorProduct A

/-- Compatibility alias for the bad-prime support of two binary matrices. -/
def binaryPairBadPrimeSupportNat
    (A B : Matrix (Fin 2) (Fin 2) ℚ) : ℕ :=
  matrixPairBadPrimeSupportNat A B

/-- Compatibility alias for the bad-prime set of two binary matrices. -/
def binaryPairBadPrimeSet
    (A B : Matrix (Fin 2) (Fin 2) ℚ) : Finset ℕ :=
  matrixPairBadPrimeSet A B

lemma binaryMatrix_entry_den_dvd_denominatorProduct
    (A : Matrix (Fin 2) (Fin 2) ℚ) (i j : Fin 2) :
    (A i j).den ∣ binaryMatrixDenominatorProduct A := by
  exact matrix_entry_den_dvd_denominatorProduct A i j

lemma binaryPairBadPrimeSupportNat_ne_zero
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0) :
    binaryPairBadPrimeSupportNat A B ≠ 0 := by
  exact matrixPairBadPrimeSupportNat_ne_zero A B hA_det hB_det

lemma prime_mem_binaryPairBadPrimeSet_iff
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    p ∈ binaryPairBadPrimeSet A B ↔
      p ∣ binaryPairBadPrimeSupportNat A B := by
  exact prime_mem_matrixPairBadPrimeSet_iff A B hA_det hB_det hp

/-- Compatibility alias for the integral model of a rational binary matrix. -/
def rationalBinaryMatrixPadicInt
    {p : ℕ} [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hden : ∀ i j, ¬p ∣ (A i j).den) :
    Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  rationalMatrixPadicInt A hden

@[simp] lemma rationalBinaryMatrixPadicInt_map
    {p : ℕ} [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hden : ∀ i j, ¬p ∣ (A i j).den) :
    (rationalBinaryMatrixPadicInt A hden).map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) := by
  exact rationalMatrixPadicInt_map A hden

lemma rationalBinaryMatrixPadicInt_isSymm
    {p : ℕ} [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm)
    (hden : ∀ i j, ¬p ∣ (A i j).den) :
    (rationalBinaryMatrixPadicInt A hden).IsSymm := by
  exact rationalMatrixPadicInt_isSymm A hA_symm hden

lemma rationalBinaryMatrixPadicInt_det_isUnit
    {p : ℕ} [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_det : A.det ≠ 0)
    (hden : ∀ i j, ¬p ∣ (A i j).den)
    (hdetnum : ¬p ∣ A.det.num.natAbs)
    (hdetden : ¬p ∣ A.det.den) :
    IsUnit (rationalBinaryMatrixPadicInt A hden).det := by
  exact rationalMatrixPadicInt_det_isUnit
    A hA_det hden hdetnum hdetden

/-- A prime outside the generic matrix-pair bad set is odd and avoids every
entry denominator and determinant numerator or denominator. -/
lemma matrixPairGoodPrimeData {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpnot : p ∉ matrixPairBadPrimeSet A B) :
    p ≠ 2 ∧
      (∀ i j, ¬p ∣ (A i j).den) ∧
      (∀ i j, ¬p ∣ (B i j).den) ∧
      (¬p ∣ A.det.num.natAbs) ∧ (¬p ∣ A.det.den) ∧
      (¬p ∣ B.det.num.natAbs) ∧ (¬p ∣ B.det.den) := by
  have hpndvd : ¬p ∣ matrixPairBadPrimeSupportNat A B := by
    intro h
    exact hpnot
      ((prime_mem_matrixPairBadPrimeSet_iff
        A B hA_det hB_det hp).2 h)
  have avoid_of_dvd {d : ℕ}
      (hd : d ∣ matrixPairBadPrimeSupportNat A B) : ¬p ∣ d := by
    intro hpd
    exact hpndvd (dvd_trans hpd hd)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hp2
    apply hpndvd
    refine ⟨matrixDenominatorProduct A *
      matrixDenominatorProduct B * A.det.num.natAbs * A.det.den *
        B.det.num.natAbs * B.det.den, ?_⟩
    simp [hp2, matrixPairBadPrimeSupportNat]
    ring
  · intro i j
    apply avoid_of_dvd
    apply dvd_trans (matrix_entry_den_dvd_denominatorProduct A i j)
    refine ⟨2 * matrixDenominatorProduct B * A.det.num.natAbs *
      A.det.den * B.det.num.natAbs * B.det.den, ?_⟩
    simp [matrixPairBadPrimeSupportNat]
    ring
  · intro i j
    apply avoid_of_dvd
    apply dvd_trans (matrix_entry_den_dvd_denominatorProduct B i j)
    refine ⟨2 * matrixDenominatorProduct A * A.det.num.natAbs *
      A.det.den * B.det.num.natAbs * B.det.den, ?_⟩
    simp [matrixPairBadPrimeSupportNat]
    ring
  · apply avoid_of_dvd
    refine ⟨2 * matrixDenominatorProduct A *
      matrixDenominatorProduct B * A.det.den * B.det.num.natAbs *
        B.det.den, ?_⟩
    simp [matrixPairBadPrimeSupportNat]
    ring
  · apply avoid_of_dvd
    refine ⟨2 * matrixDenominatorProduct A *
      matrixDenominatorProduct B * A.det.num.natAbs *
        B.det.num.natAbs * B.det.den, ?_⟩
    simp [matrixPairBadPrimeSupportNat]
    ring
  · apply avoid_of_dvd
    refine ⟨2 * matrixDenominatorProduct A *
      matrixDenominatorProduct B * A.det.num.natAbs * A.det.den *
        B.det.den, ?_⟩
    simp [matrixPairBadPrimeSupportNat]
    ring
  · apply avoid_of_dvd
    refine ⟨2 * matrixDenominatorProduct A *
      matrixDenominatorProduct B * A.det.num.natAbs * A.det.den *
        B.det.num.natAbs, ?_⟩
    simp [matrixPairBadPrimeSupportNat]
    ring

/-- Outside the generic finite bad-prime set, fixed nonsingular symmetric
rational forms of dimensions at least three both represent every p-adic
scalar. -/
theorem matrixPairCommonRepresents_padic_of_not_mem_badPrimeSet
    {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ matrixPairBadPrimeSet A B) (c : ℚ_[p]) :
    (∃ u : Fin m → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
    ∃ v : Fin n → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hAp_map : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBp_map : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hAp_map] using
      PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_padic_of_integral
        hpodd hm Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) c
  · simpa [hBp_map] using
      PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_padic_of_integral
        hpodd hn Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) c

private lemma binaryPairGoodPrimeData
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpnot : p ∉ binaryPairBadPrimeSet A B) :
    p ≠ 2 ∧
      (∀ i j, ¬p ∣ (A i j).den) ∧
      (∀ i j, ¬p ∣ (B i j).den) ∧
      (¬p ∣ A.det.num.natAbs) ∧ (¬p ∣ A.det.den) ∧
      (¬p ∣ B.det.num.natAbs) ∧ (¬p ∣ B.det.den) := by
  exact matrixPairGoodPrimeData A B hA_det hB_det hp hpnot

/-- Outside the explicit finite bad-prime set, two nonsingular symmetric
rational binary forms commonly represent every p-adic integral unit. -/
theorem binaryCommonRepresents_padic_unit_of_not_mem_binaryPairBadPrimeSet
    (A B : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {p : ℕ} [Fact p.Prime] (hpnot : p ∉ binaryPairBadPrimeSet A B)
    {c : ℤ_[p]} (hc : IsUnit c) :
    PositiveDefiniteIntegralLattice.BinaryCommonRepresents
      (A.map (algebraMap ℚ ℚ_[p])) (B.map (algebraMap ℚ ℚ_[p]))
      (c : ℚ_[p]) := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    binaryPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalBinaryMatrixPadicInt A hAden
  let Bp := rationalBinaryMatrixPadicInt B hBden
  have hAp_map : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalBinaryMatrixPadicInt_map A hAden
  have hBp_map : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalBinaryMatrixPadicInt_map B hBden
  have hcommon :=
    PositiveDefiniteIntegralLattice.binaryCommonRepresents_padic_unit_of_integral
      hpodd Ap Bp
        (rationalBinaryMatrixPadicInt_isSymm A hA_symm hAden)
        (rationalBinaryMatrixPadicInt_det_isUnit
          A hA_det hAden hAnum hAdenDet)
        (rationalBinaryMatrixPadicInt_isSymm B hB_symm hBden)
        (rationalBinaryMatrixPadicInt_det_isUnit
          B hB_det hBden hBnum hBdenDet) hc
  simpa [hAp_map, hBp_map] using hcommon

/-- Explicit bad-prime support for a rational binary and ternary matrix. -/
def binaryTernaryBadPrimeSupportNat
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ) : ℕ :=
  matrixPairBadPrimeSupportNat A B

/-- The finite set where a rational binary--ternary pair need not have
unimodular integral models. -/
def binaryTernaryBadPrimeSet
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ) : Finset ℕ :=
  matrixPairBadPrimeSet A B

lemma binaryTernaryBadPrimeSupportNat_ne_zero
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0) :
    binaryTernaryBadPrimeSupportNat A B ≠ 0 := by
  exact matrixPairBadPrimeSupportNat_ne_zero A B hA_det hB_det

/-- Membership in the mixed bad-prime set is exactly divisibility of its
explicit natural support. -/
lemma prime_mem_binaryTernaryBadPrimeSet_iff
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    p ∈ binaryTernaryBadPrimeSet A B ↔
      p ∣ binaryTernaryBadPrimeSupportNat A B := by
  exact prime_mem_matrixPairBadPrimeSet_iff A B hA_det hB_det hp

/-- Outside the explicit mixed bad-prime set, fixed nonsingular symmetric
rational binary and ternary forms commonly represent every p-adic integral
unit. The ternary side in fact represents every p-adic scalar. -/
theorem binaryTernaryCommonRepresents_padic_unit_of_not_mem_badPrimeSet
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (B : Matrix (Fin 3) (Fin 3) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {p : ℕ} [Fact p.Prime] (hpnot : p ∉ binaryTernaryBadPrimeSet A B)
    {c : ℤ_[p]} (hc : IsUnit c) :
    (∃ u : Fin 2 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = (c : ℚ_[p])) ∧
    ∃ v : Fin 3 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = (c : ℚ_[p]) := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hAp_map : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBp_map : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hAp_map] using
      PositiveDefiniteIntegralLattice.exists_binary_gramQuadraticValue_eq_padic_unit_of_integral
        hpodd Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) hc
  · simpa [hBp_map] using
      PositiveDefiniteIntegralLattice.exists_ternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) (c : ℚ_[p])

/-- Explicit bad-prime support for a rational ternary and quaternary matrix. -/
def ternaryQuaternaryBadPrimeSupportNat
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ) : ℕ :=
  matrixPairBadPrimeSupportNat A B

/-- The finite set where a rational ternary--quaternary pair need not have
unimodular integral models. -/
def ternaryQuaternaryBadPrimeSet
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ) : Finset ℕ :=
  matrixPairBadPrimeSet A B

lemma ternaryQuaternaryBadPrimeSupportNat_ne_zero
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0) :
    ternaryQuaternaryBadPrimeSupportNat A B ≠ 0 := by
  exact matrixPairBadPrimeSupportNat_ne_zero A B hA_det hB_det

/-- Membership in the ternary--quaternary bad-prime set is exactly
divisibility of its explicit natural support. -/
lemma prime_mem_ternaryQuaternaryBadPrimeSet_iff
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    p ∈ ternaryQuaternaryBadPrimeSet A B ↔
      p ∣ ternaryQuaternaryBadPrimeSupportNat A B := by
  exact prime_mem_matrixPairBadPrimeSet_iff A B hA_det hB_det hp

/-- Outside the explicit bad-prime set, fixed nonsingular symmetric rational
ternary and quaternary forms commonly represent every p-adic scalar. -/
theorem ternaryQuaternaryCommonRepresents_padic_of_not_mem_badPrimeSet
    (A : Matrix (Fin 3) (Fin 3) ℚ)
    (B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ ternaryQuaternaryBadPrimeSet A B) (c : ℚ_[p]) :
    (∃ u : Fin 3 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
    ∃ v : Fin 4 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hAp_map : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBp_map : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hAp_map] using
      PositiveDefiniteIntegralLattice.exists_ternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) c
  · simpa [hBp_map] using
      PositiveDefiniteIntegralLattice.exists_quaternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) c

/-- Explicit bad-prime support for a rational quaternary and quinary matrix. -/
def quaternaryQuinaryBadPrimeSupportNat
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ) : ℕ :=
  matrixPairBadPrimeSupportNat A B

/-- The finite set where a rational quaternary--quinary pair need not have
unimodular integral models. -/
def quaternaryQuinaryBadPrimeSet
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ) : Finset ℕ :=
  matrixPairBadPrimeSet A B

lemma quaternaryQuinaryBadPrimeSupportNat_ne_zero
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0) :
    quaternaryQuinaryBadPrimeSupportNat A B ≠ 0 := by
  exact matrixPairBadPrimeSupportNat_ne_zero A B hA_det hB_det

/-- Membership in the quaternary--quinary bad-prime set is exactly
divisibility of its explicit natural support. -/
lemma prime_mem_quaternaryQuinaryBadPrimeSet_iff
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    p ∈ quaternaryQuinaryBadPrimeSet A B ↔
      p ∣ quaternaryQuinaryBadPrimeSupportNat A B := by
  exact prime_mem_matrixPairBadPrimeSet_iff A B hA_det hB_det hp

/-- Outside the explicit bad-prime set, fixed nonsingular symmetric rational
quaternary and quinary forms commonly represent every p-adic scalar. -/
theorem quaternaryQuinaryCommonRepresents_padic_of_not_mem_badPrimeSet
    (A : Matrix (Fin 4) (Fin 4) ℚ)
    (B : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ quaternaryQuinaryBadPrimeSet A B) (c : ℚ_[p]) :
    (∃ u : Fin 4 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[p])) u = c) ∧
    ∃ v : Fin 5 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) v = c := by
  obtain ⟨hpodd, hAden, hBden, hAnum, hAdenDet, hBnum, hBdenDet⟩ :=
    matrixPairGoodPrimeData A B hA_det hB_det
      (Fact.out : p.Prime) hpnot
  let Ap := rationalMatrixPadicInt A hAden
  let Bp := rationalMatrixPadicInt B hBden
  have hAp_map : Ap.map PadicInt.Coe.ringHom =
      A.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map A hAden
  have hBp_map : Bp.map PadicInt.Coe.ringHom =
      B.map (algebraMap ℚ ℚ_[p]) :=
    rationalMatrixPadicInt_map B hBden
  constructor
  · simpa [hAp_map] using
      PositiveDefiniteIntegralLattice.exists_quaternary_gramQuadraticValue_eq_padic_of_integral
        hpodd Ap
          (rationalMatrixPadicInt_isSymm A hA_symm hAden)
          (rationalMatrixPadicInt_det_isUnit
            A hA_det hAden hAnum hAdenDet) c
  · simpa [hBp_map] using
      PositiveDefiniteIntegralLattice.exists_quinary_gramQuadraticValue_eq_padic_of_integral
        hpodd Bp
          (rationalMatrixPadicInt_isSymm B hB_symm hBden)
          (rationalMatrixPadicInt_det_isUnit
            B hB_det hBden hBnum hBdenDet) c

end Rat

namespace PositiveDefiniteIntegralLattice

/-- Representation by a nondegenerate rational binary diagonal form after
characteristic-zero scalar extension is the corresponding quadratic norm
condition. -/
theorem exists_binaryDiagonal_gramQuadraticValue_eq_iff_quadraticNormRepresents
    {K : Type*} [Field K] [CharZero K]
    (a b q : ℚ) (ha : a ≠ 0) :
    (∃ v : Fin 2 → K,
      gramQuadraticValue
        (Matrix.diagonal ![(a : K), (b : K)]) v = (q : K)) ↔
      quadraticNormRepresents ((-b / a : ℚ) : K) ((q / a : ℚ) : K) := by
  rw [quadraticNormRepresents_iff_exists]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v 0, v 1, ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at hv ⊢
    field_simp [haK]
    linear_combination hv
  · rintro ⟨x, y, hxy⟩
    refine ⟨![x, y], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at hxy ⊢
    field_simp [haK] at hxy
    linear_combination hxy

/-- A rational congruence to a binary diagonal form identifies represented
values after every characteristic-zero scalar extension with one quadratic
norm condition. -/
theorem exists_binary_gramQuadraticValue_eq_iff_quadraticNormRepresents_of_diagonalization
    {K : Type*} [Field K] [CharZero K]
    (A : Matrix (Fin 2) (Fin 2) ℚ) (a b q : ℚ) (ha : a ≠ 0)
    (hcongr : A.IsCongruent (Matrix.diagonal ![a, b])) :
    (∃ v : Fin 2 → K,
      gramQuadraticValue (A.map (algebraMap ℚ K)) v = (q : K)) ↔
      quadraticNormRepresents ((-b / a : ℚ) : K) ((q / a : ℚ) : K) := by
  have hmap := hcongr.map (algebraMap ℚ K)
  have hrep := exists_gramQuadraticValue_eq_iff_of_isCongruent hmap (q : K)
  apply hrep.trans
  simpa using
    (exists_binaryDiagonal_gramQuadraticValue_eq_iff_quadraticNormRepresents
      (K := K) a b q ha)

end PositiveDefiniteIntegralLattice

namespace Rat

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

/-- At every rational finite place, the quadratic norm condition is
equivalent to the corresponding factor in the rational Hilbert product. -/
theorem quadraticNormRepresents_rat_padic_iff_finiteHilbertFactor_eq_one
    (p : {p : ℕ // p.Prime}) {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    PositiveDefiniteIntegralLattice.quadraticNormRepresents
        (d : ℚ_[p.1]) (c : ℚ_[p.1]) ↔
      finiteHilbertFactor d c p = 1 := by
  rw [finiteHilbertFactor]
  split
  next hp2 =>
    have hpEq : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    subst p
    exact
      PositiveDefiniteIntegralLattice.quadraticNormRepresents_rat_padic_iff_dyadicHilbertSymbol_eq_one
        hd hc
  next hp2 =>
    exact
      PositiveDefiniteIntegralLattice.quadraticNormRepresents_rat_padic_iff_oddPrimeHilbertSymbol_eq_one
        hp2 hd hc

/-- Rational Hilbert reciprocity fills one omitted finite-place quadratic norm
condition from the real condition and all other finite-place conditions. -/
theorem quadraticNormRepresents_rat_padic_of_real_and_all_but_one
    (ell : {p : ℕ // p.Prime}) {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.quadraticNormRepresents (d : ℝ) (c : ℝ))
    (hpadic : ∀ p : {p : ℕ // p.Prime}, p ≠ ell →
      PositiveDefiniteIntegralLattice.quadraticNormRepresents
        (d : ℚ_[p.1]) (c : ℚ_[p.1])) :
    PositiveDefiniteIntegralLattice.quadraticNormRepresents
      (d : ℚ_[ell.1]) (c : ℚ_[ell.1]) := by
  apply (quadraticNormRepresents_rat_padic_iff_finiteHilbertFactor_eq_one
    ell hd hc).2
  have hformula := hilbertProductFormula hd hc
  have hrealFactor : realHilbertSymbol d c = 1 :=
    (PositiveDefiniteIntegralLattice.quadraticNormRepresents_real_iff_realHilbertSymbol_eq_one
      d c hd hc).1 hreal
  unfold HilbertProductFormula at hformula
  rw [hrealFactor, one_mul] at hformula
  by_cases hell : ell ∈ hilbertBadPrimeSet d c
  · have hprod : finiteHilbertProduct d c (hilbertBadPrimeSet d c) =
        finiteHilbertFactor d c ell := by
      unfold finiteHilbertProduct
      apply Finset.prod_eq_single ell
      · intro p hp hne
        exact
          (quadraticNormRepresents_rat_padic_iff_finiteHilbertFactor_eq_one
            p hd hc).1 (hpadic p hne)
      · exact fun hnot => False.elim (hnot hell)
    rw [hprod] at hformula
    exact hformula
  · exact finiteHilbertFactor_eq_one_of_not_mem_hilbertBadPrimeSet
      hd hc ell hell

/-- A nonzero value represented by a nonsingular symmetric rational binary
form over the real field and every p-adic field except one is represented at
the omitted p-adic place. -/
theorem exists_binary_gramQuadraticValue_eq_padic_of_real_and_all_but_one
    (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (q : ℚ) (hq : q ≠ 0) (ell : {p : ℕ // p.Prime})
    (hreal : ∃ v : Fin 2 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℝ)) v = (q : ℝ))
    (hpadic : ∀ p : {p : ℕ // p.Prime}, p ≠ ell →
      ∃ v : Fin 2 → ℚ_[p.1],
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (A.map (algebraMap ℚ ℚ_[p.1])) v = (q : ℚ_[p.1])) :
    ∃ v : Fin 2 → ℚ_[ell.1],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (A.map (algebraMap ℚ ℚ_[ell.1])) v = (q : ℚ_[ell.1]) := by
  obtain ⟨d, P, hd, hP⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_diagonal
      A hA_symm hA_det (by norm_num)
  let a : ℚ := d 0
  let b : ℚ := d 1
  have ha : a ≠ 0 := hd 0
  have hb : b ≠ 0 := hd 1
  have hd_eq : d = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  have hcongr : A.IsCongruent (Matrix.diagonal ![a, b]) := by
    refine ⟨P, ?_⟩
    simpa [hd_eq] using hP
  let D : ℚ := -b / a
  let C : ℚ := q / a
  have hD : D ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hC : C ≠ 0 := div_ne_zero hq ha
  have hnormReal : PositiveDefiniteIntegralLattice.quadraticNormRepresents
      (D : ℝ) (C : ℝ) := by
    exact
      (PositiveDefiniteIntegralLattice.exists_binary_gramQuadraticValue_eq_iff_quadraticNormRepresents_of_diagonalization
        (K := ℝ) A a b q ha hcongr).1 hreal
  have hnormPadic : ∀ p : {p : ℕ // p.Prime}, p ≠ ell →
      PositiveDefiniteIntegralLattice.quadraticNormRepresents
        (D : ℚ_[p.1]) (C : ℚ_[p.1]) := by
    intro p hp
    exact
      (PositiveDefiniteIntegralLattice.exists_binary_gramQuadraticValue_eq_iff_quadraticNormRepresents_of_diagonalization
        (K := ℚ_[p.1]) A a b q ha hcongr).1 (hpadic p hp)
  have hnormEll := quadraticNormRepresents_rat_padic_of_real_and_all_but_one
    ell hD hC hnormReal hnormPadic
  exact
    (PositiveDefiniteIntegralLattice.exists_binary_gramQuadraticValue_eq_iff_quadraticNormRepresents_of_diagonalization
      (K := ℚ_[ell.1]) A a b q ha hcongr).2 hnormEll

end Rat
