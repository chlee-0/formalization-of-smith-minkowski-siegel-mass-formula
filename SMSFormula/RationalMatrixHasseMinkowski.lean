import SMSFormula.RationalWeakApproximation

noncomputable section

open scoped Matrix

namespace Rat

/-- A congruence between two nonsingular leading scalar blocks induces a
congruence between their tails. A Gram isometry first adjusts the given
congruence to fix the leading coordinate. -/
private theorem finSuccTail_isCongruent_of_isCongruent
    {K : Type*} [Field K] {n : ℕ} (hchar : ringChar K ≠ 2)
    (c : K) (hc : c ≠ 0)
    (C D : Matrix (Fin n) (Fin n) K)
    (hC_symm : C.IsSymm) (hC_det : C.det ≠ 0) (hD_det : D.det ≠ 0)
    (hblock : (PositiveDefiniteIntegralLattice.finSuccGramBlock c C).IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c D)) :
    C.IsCongruent D := by
  let e : Fin (n + 1) → K := PositiveDefiniteIntegralLattice.finSuccHeadVector
  rcases hblock with ⟨X, hX⟩
  have hChead : PositiveDefiniteIntegralLattice.gramQuadraticValue
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) e = c := by
    rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_finSuccGramBlock]
    simp [e, PositiveDefiniteIntegralLattice.finSuccHeadVector,
      PositiveDefiniteIntegralLattice.gramQuadraticValue]
  have hDhead : PositiveDefiniteIntegralLattice.gramQuadraticValue
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c D) e = c := by
    rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_finSuccGramBlock]
    simp [e, PositiveDefiniteIntegralLattice.finSuccHeadVector,
      PositiveDefiniteIntegralLattice.gramQuadraticValue]
  have hvalue : PositiveDefiniteIntegralLattice.gramQuadraticValue
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) (X.1 *ᵥ e) =
        PositiveDefiniteIntegralLattice.gramQuadraticValue
          (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) e := by
    rw [PositiveDefiniteIntegralLattice.gramQuadraticValue_mulVec_of_congr
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C)
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c D) X hX e, hDhead, hChead]
  have hXene : PositiveDefiniteIntegralLattice.gramQuadraticValue
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) (X.1 *ᵥ e) ≠ 0 := by
    rw [hvalue, hChead]
    exact hc
  have hblock_symm :
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C).IsSymm :=
    PositiveDefiniteIntegralLattice.finSuccGramBlock_isSymm c C hC_symm
  have hblock_det :
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C).det ≠ 0 := by
    simp [hc, hC_det]
  obtain ⟨T, hT, hThead⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramIsometry_mulVec_eq_of_same_nonzero_value
      hchar (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) hblock_symm hblock_det
      (X.1 *ᵥ e) e hvalue hXene
  let Z : GL (Fin (n + 1)) K := T * X
  have hZcongr : Z.1ᵀ * PositiveDefiniteIntegralLattice.finSuccGramBlock c C * Z.1 =
      PositiveDefiniteIntegralLattice.finSuccGramBlock c D := by
    change (T.1 * X.1)ᵀ * PositiveDefiniteIntegralLattice.finSuccGramBlock c C *
      (T.1 * X.1) = PositiveDefiniteIntegralLattice.finSuccGramBlock c D
    rw [Matrix.transpose_mul]
    calc
      (X.1ᵀ * T.1ᵀ) * PositiveDefiniteIntegralLattice.finSuccGramBlock c C *
          (T.1 * X.1) =
        X.1ᵀ * (T.1ᵀ * PositiveDefiniteIntegralLattice.finSuccGramBlock c C * T.1) *
          X.1 := by simp only [Matrix.mul_assoc]
      _ = PositiveDefiniteIntegralLattice.finSuccGramBlock c D := by rw [hT, hX]
  have hZhead : Z.1 *ᵥ e = e := by
    change (T.1 * X.1) *ᵥ e = e
    rw [← Matrix.mulVec_mulVec, hThead]
  let U : Matrix (Fin n) (Fin n) K :=
    PositiveDefiniteIntegralLattice.finSuccTailMatrix Z.1
  have hU : Uᵀ * C * U = D := by
    exact PositiveDefiniteIntegralLattice.finSuccTailMatrix_congr
      c hc C D Z.1 hZcongr hZhead
  have hU_det : U.det ≠ 0 := by
    intro hdet
    have hdet_eq := congrArg Matrix.det hU
    simp [Matrix.det_mul, hdet] at hdet_eq
    exact hD_det hdet_eq.symm
  let U' : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero U hU_det
  exact ⟨U', by simpa [U'] using hU⟩

/-- Rational leading-block splittings and a congruence after scalar extension
induce a congruence between the scalar-extended rational tails. -/
private theorem finSuccTail_isCongruent_of_scalarExtension
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (c : ℚ) (hc : c ≠ 0)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (C D : Matrix (Fin n) (Fin n) ℚ)
    (P Q : GL (Fin (n + 1)) ℚ)
    (hC_symm : C.IsSymm) (hC_det : C.det ≠ 0) (hD_det : D.det ≠ 0)
    (hP : P.1ᵀ * A * P.1 = PositiveDefiniteIntegralLattice.finSuccGramBlock c C)
    (hQ : Q.1ᵀ * B * Q.1 = PositiveDefiniteIntegralLattice.finSuccGramBlock c D)
    (hAB : (A.map (algebraMap ℚ K)).IsCongruent
      (B.map (algebraMap ℚ K))) :
    (C.map (algebraMap ℚ K)).IsCongruent
      (D.map (algebraMap ℚ K)) := by
  let f := algebraMap ℚ K
  have hAblock : A.IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) := ⟨P, hP⟩
  have hBblock : B.IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c D) := ⟨Q, hQ⟩
  have hAblock_map : (A.map f).IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock (f c) (C.map f)) := by
    simpa [f] using hAblock.map f
  have hBblock_map : (B.map f).IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock (f c) (D.map f)) := by
    simpa [f] using hBblock.map f
  have hblocks :
      (PositiveDefiniteIntegralLattice.finSuccGramBlock (f c) (C.map f)).IsCongruent
        (PositiveDefiniteIntegralLattice.finSuccGramBlock (f c) (D.map f)) :=
    (hAblock_map.symm.trans hAB).trans hBblock_map
  have hc_map : f c ≠ 0 := by
    intro hfc
    exact hc (f.injective (by simpa using hfc))
  have hC_det_map : (C.map f).det ≠ 0 := by
    have hdet : (C.map f).det = f C.det := by
      simpa using (RingHom.map_det f C).symm
    rw [hdet]
    intro hzero
    exact hC_det (f.injective (by simpa using hzero))
  have hD_det_map : (D.map f).det ≠ 0 := by
    have hdet : (D.map f).det = f D.det := by
      simpa using (RingHom.map_det f D).symm
    rw [hdet]
    intro hzero
    exact hD_det (f.injective (by simpa using hzero))
  exact finSuccTail_isCongruent_of_isCongruent
    (by norm_num) (f c) hc_map (C.map f) (D.map f)
      (hC_symm.map f) hC_det_map hD_det_map hblocks

/-- Locally congruent nonsingular symmetric rational forms of dimension at
least two represent one common nonzero rational scalar. -/
theorem exists_common_nonzero_gramQuadraticValue_of_isCongruent_real_and_padic
    {n : ℕ} (hn : 2 ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : (A.map (algebraMap ℚ ℝ)).IsCongruent
      (B.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (B.map (algebraMap ℚ ℚ_[p]))) :
    ∃ c : ℚ, c ≠ 0 ∧
      (∃ x : Fin n → ℚ,
        PositiveDefiniteIntegralLattice.gramQuadraticValue A x = c) ∧
      ∃ y : Fin n → ℚ,
        PositiveDefiniteIntegralLattice.gramQuadraticValue B y = c := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨c, hc, hA⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_ne_zero
      A hA_symm hA_det (by norm_num)
  have hBreal : ∃ y : Fin n → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℝ)) y = (c : ℝ) :=
    PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_of_isCongruent
      hreal (c : ℝ)
        (exists_gramQuadraticValue_eq_scalarExtension_of_rat
          (K := ℝ) hA)
  have hBpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ y : Fin n → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue
        (B.map (algebraMap ℚ ℚ_[p])) y = (c : ℚ_[p]) := by
    intro p hp
    exact PositiveDefiniteIntegralLattice.exists_gramQuadraticValue_eq_of_isCongruent
      (hpadic p) (c : ℚ_[p])
        (exists_gramQuadraticValue_eq_scalarExtension_of_rat
          (K := ℚ_[p]) hA)
  exact ⟨c, hc, hA,
    exists_gramQuadraticValue_eq_rat_of_real_and_padic
      hn B hB_symm hB_det c hc hBreal hBpadic⟩

/-- Locally congruent rational Gram forms split along rational vectors of one
common nonzero value into fixed rational codimension-one complements that are
congruent over the real field and every p-adic field. -/
theorem exists_finSucc_complements_isCongruent_real_and_padic
    {n : ℕ} (hn : 1 ≤ n)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : (A.map (algebraMap ℚ ℝ)).IsCongruent
      (B.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (B.map (algebraMap ℚ ℚ_[p]))) :
    ∃ (c : ℚ) (x y : Fin (n + 1) → ℚ)
      (C D : Matrix (Fin n) (Fin n) ℚ)
      (P Q : GL (Fin (n + 1)) ℚ),
      c ≠ 0 ∧
      PositiveDefiniteIntegralLattice.gramQuadraticValue A x = c ∧
      PositiveDefiniteIntegralLattice.gramQuadraticValue B y = c ∧
      C.IsSymm ∧ C.det ≠ 0 ∧ D.IsSymm ∧ D.det ≠ 0 ∧
      P.1 *ᵥ PositiveDefiniteIntegralLattice.finSuccHeadVector = x ∧
      P.1ᵀ * A * P.1 = PositiveDefiniteIntegralLattice.finSuccGramBlock c C ∧
      Q.1 *ᵥ PositiveDefiniteIntegralLattice.finSuccHeadVector = y ∧
      Q.1ᵀ * B * Q.1 = PositiveDefiniteIntegralLattice.finSuccGramBlock c D ∧
      (C.map (algebraMap ℚ ℝ)).IsCongruent
        (D.map (algebraMap ℚ ℝ)) ∧
      ∀ (p : ℕ) [Fact p.Prime],
        (C.map (algebraMap ℚ ℚ_[p])).IsCongruent
          (D.map (algebraMap ℚ ℚ_[p])) := by
  obtain ⟨c, hc, ⟨x, hx⟩, ⟨y, hy⟩⟩ :=
    exists_common_nonzero_gramQuadraticValue_of_isCongruent_real_and_padic
      (n := n + 1) (by omega) A B hA_symm hA_det hB_symm hB_det
        hreal hpadic
  have hxne : PositiveDefiniteIntegralLattice.gramQuadraticValue A x ≠ 0 := by
    rw [hx]
    exact hc
  have hyne : PositiveDefiniteIntegralLattice.gramQuadraticValue B y ≠ 0 := by
    rw [hy]
    exact hc
  obtain ⟨C, P, hC_symm, hC_det, hPhead, hP⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_finSuccBlock_with_head
      A hA_symm hA_det (by norm_num) x hxne
  obtain ⟨D, Q, hD_symm, hD_det, hQhead, hQ⟩ :=
    PositiveDefiniteIntegralLattice.exists_gramMatrix_congr_finSuccBlock_with_head
      B hB_symm hB_det (by norm_num) y hyne
  have hP' : P.1ᵀ * A * P.1 =
      PositiveDefiniteIntegralLattice.finSuccGramBlock c C := by simpa [hx] using hP
  have hQ' : Q.1ᵀ * B * Q.1 =
      PositiveDefiniteIntegralLattice.finSuccGramBlock c D := by simpa [hy] using hQ
  have htail_real : (C.map (algebraMap ℚ ℝ)).IsCongruent
      (D.map (algebraMap ℚ ℝ)) :=
    finSuccTail_isCongruent_of_scalarExtension
      c hc A B C D P Q hC_symm hC_det hD_det hP' hQ' hreal
  have htail_padic : ∀ (p : ℕ) [Fact p.Prime],
      (C.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (D.map (algebraMap ℚ ℚ_[p])) := by
    intro p hp
    exact finSuccTail_isCongruent_of_scalarExtension
      c hc A B C D P Q hC_symm hC_det hD_det hP' hQ' (hpadic p)
  exact ⟨c, x, y, C, D, P, Q, hc, hx, hy, hC_symm, hC_det,
    hD_symm, hD_det, hPhead, hP', hQhead, hQ', htail_real, htail_padic⟩

/-- Local-global matrix congruence in dimension `n` implies local-global
matrix congruence in dimension `n+1`, provided `n` is positive. -/
theorem isCongruent_rat_of_isCongruent_real_and_padic_of_finSucc
    {n : ℕ} (hn : 1 ≤ n)
    (hind : ∀ (C D : Matrix (Fin n) (Fin n) ℚ),
      C.IsSymm → C.det ≠ 0 → D.IsSymm → D.det ≠ 0 →
      (C.map (algebraMap ℚ ℝ)).IsCongruent
        (D.map (algebraMap ℚ ℝ)) →
      (∀ (p : ℕ) [Fact p.Prime],
        (C.map (algebraMap ℚ ℚ_[p])).IsCongruent
          (D.map (algebraMap ℚ ℚ_[p]))) →
      C.IsCongruent D)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hreal : (A.map (algebraMap ℚ ℝ)).IsCongruent
      (B.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (B.map (algebraMap ℚ ℚ_[p]))) :
    A.IsCongruent B := by
  obtain ⟨c, x, y, C, D, P, Q, hc, hx, hy, hC_symm, hC_det,
      hD_symm, hD_det, hPhead, hP, hQhead, hQ, htail_real, htail_padic⟩ :=
    exists_finSucc_complements_isCongruent_real_and_padic
      hn A B hA_symm hA_det hB_symm hB_det hreal hpadic
  have hCD : C.IsCongruent D :=
    hind C D hC_symm hC_det hD_symm hD_det htail_real htail_padic
  have hblock : (PositiveDefiniteIntegralLattice.finSuccGramBlock c C).IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c D) := by
    rcases hCD with ⟨T, hT⟩
    refine ⟨PositiveDefiniteIntegralLattice.finSuccGeneralLinearBlock T, ?_⟩
    rw [PositiveDefiniteIntegralLattice.finSuccGeneralLinearBlock_coe,
      PositiveDefiniteIntegralLattice.finSuccMatrixBlock_congr, hT]
  have hAblock : A.IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c C) := ⟨P, hP⟩
  have hBblock : B.IsCongruent
      (PositiveDefiniteIntegralLattice.finSuccGramBlock c D) := ⟨Q, hQ⟩
  exact (hAblock.trans hblock).trans hBblock.symm

/-- A local congruence of nonsingular rational unary forms makes the ratio of
their coefficients a square after scalar extension. -/
private theorem finOne_ratio_isSquare_of_isCongruent_scalarExtension
    {K : Type*} [Field K] [CharZero K]
    (A B : Matrix (Fin 1) (Fin 1) ℚ) (hA_det : A.det ≠ 0)
    (hAB : (A.map (algebraMap ℚ K)).IsCongruent
      (B.map (algebraMap ℚ K))) :
    IsSquare ((B 0 0 / A 0 0 : ℚ) : K) := by
  let f := algebraMap ℚ K
  have hA00 : A 0 0 ≠ 0 := by
    simpa [Matrix.det_fin_one] using hA_det
  have hA00_map : f (A 0 0) ≠ 0 := by
    intro hzero
    apply hA00
    apply f.injective
    simpa using hzero
  rcases hAB with ⟨T, hT⟩
  refine ⟨T.1 0 0, ?_⟩
  have hentry := congrFun (congrFun hT 0) 0
  simp [Matrix.mul_apply] at hentry
  change f (B 0 0 / A 0 0) = T.1 0 0 * T.1 0 0
  calc
    f (B 0 0 / A 0 0) = f (B 0 0) / f (A 0 0) := by simp
    _ = T.1 0 0 * T.1 0 0 := by
      rw [div_eq_iff hA00_map]
      dsimp only [f] at hentry ⊢
      calc
        (B 0 0 : K) = T.1 0 0 * (A 0 0 : K) * T.1 0 0 := hentry.symm
        _ = (T.1 0 0 * T.1 0 0) * (A 0 0 : K) := by ring

/-- Unary Hasse--Minkowski in matrix-congruence form. -/
private theorem finOne_isCongruent_rat_of_real_and_padic
    (A B : Matrix (Fin 1) (Fin 1) ℚ)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    (hreal : (A.map (algebraMap ℚ ℝ)).IsCongruent
      (B.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (B.map (algebraMap ℚ ℚ_[p]))) :
    A.IsCongruent B := by
  let q : ℚ := B 0 0 / A 0 0
  have hq : IsSquare q :=
    (Rat.isSquare_iff_isSquare_real_and_padic q).mpr
      ⟨finOne_ratio_isSquare_of_isCongruent_scalarExtension
          A B hA_det hreal,
        fun p _ => finOne_ratio_isSquare_of_isCongruent_scalarExtension
          A B hA_det (hpadic p)⟩
  obtain ⟨r, hr⟩ := hq
  have hA00 : A 0 0 ≠ 0 := by
    simpa [Matrix.det_fin_one] using hA_det
  have hB00 : B 0 0 ≠ 0 := by
    simpa [Matrix.det_fin_one] using hB_det
  have hq_ne : q ≠ 0 := div_ne_zero hB00 hA00
  have hr_ne : r ≠ 0 := by
    intro hrzero
    apply hq_ne
    simpa [hrzero] using hr
  let Tmat : Matrix (Fin 1) (Fin 1) ℚ := fun _ _ => r
  have hTmat_det : Tmat.det ≠ 0 := by
    simpa [Tmat, Matrix.det_fin_one] using hr_ne
  let T : GL (Fin 1) ℚ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Tmat hTmat_det
  have hentry : r * A 0 0 * r = B 0 0 := by
    dsimp [q] at hr
    field_simp [hA00] at hr
    calc
      r * A 0 0 * r = A 0 0 * r ^ 2 := by ring
      _ = B 0 0 := hr.symm
  refine ⟨T, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simpa [T, Tmat, Matrix.mul_apply] using hentry

/-- Hasse--Minkowski in matrix-congruence form for nonsingular symmetric
rational Gram matrices in every dimension. -/
theorem isCongruent_rat_of_isCongruent_real_and_padic
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
    (hA_det : A.det ≠ 0) (hB_det : B.det ≠ 0)
    (hreal : (A.map (algebraMap ℚ ℝ)).IsCongruent
      (B.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (B.map (algebraMap ℚ ℚ_[p]))) :
    A.IsCongruent B := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hAB : A = B := Subsingleton.elim A B
          rw [hAB]
          exact Matrix.IsCongruent.refl B
      | succ n =>
          cases n with
          | zero =>
              exact finOne_isCongruent_rat_of_real_and_padic
                A B hA_det hB_det hreal hpadic
          | succ n =>
              exact isCongruent_rat_of_isCongruent_real_and_padic_of_finSucc
                (n := n + 1) (by omega)
                (fun C D hC_symm hC_det hD_symm hD_det hCD_real hCD_padic =>
                  ih (n + 1) (by omega) C D hC_symm hD_symm hC_det hD_det
                    hCD_real hCD_padic)
                A B hA_symm hA_det hB_symm hB_det hreal hpadic

end Rat
