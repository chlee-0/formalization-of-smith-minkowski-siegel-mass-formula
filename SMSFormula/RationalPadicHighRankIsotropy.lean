import SMSFormula.RationalLegendre

/-!
# High-rank isotropy over odd p-adic fields

This file proves the odd-prime part of the local input needed for the
intrinsic `GSpin` similitude comparison.  Three rational diagonal
coefficients with the same valuation parity can be normalized either to
three p-adic integral units, or to one common valuation-one scalar times
three units.  The existing unimodular ternary isotropy theorem then applies.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

private lemma binary_values_eq_of_ne_common
    {x y z : ℕ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hz : z = 0 ∨ z = 1) (hxz : x ≠ z) (hyz : y ≠ z) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> simp_all

private lemma exists_three_equal_of_five_binary_values
    (f : Fin 5 → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      f i = f j ∧ f i = f k := by
  by_cases h01 : f 0 = f 1
  · by_cases h02 : f 0 = f 2
    · exact ⟨0, 1, 2, by decide, by decide, by decide, h01, h02⟩
    · by_cases h03 : f 0 = f 3
      · exact ⟨0, 1, 3, by decide, by decide, by decide, h01, h03⟩
      · by_cases h04 : f 0 = f 4
        · exact ⟨0, 1, 4, by decide, by decide, by decide, h01, h04⟩
        · have h0 := hf 0
          have h2 := hf 2
          have h3 := hf 3
          have h4 := hf 4
          have h23 : f 2 = f 3 :=
            binary_values_eq_of_ne_common h2 h3 h0 (Ne.symm h02) (Ne.symm h03)
          have h24 : f 2 = f 4 :=
            binary_values_eq_of_ne_common h2 h4 h0 (Ne.symm h02) (Ne.symm h04)
          exact ⟨2, 3, 4, by decide, by decide, by decide, h23, h24⟩
  · by_cases h02 : f 0 = f 2
    · by_cases h03 : f 0 = f 3
      · exact ⟨0, 2, 3, by decide, by decide, by decide, h02, h03⟩
      · by_cases h04 : f 0 = f 4
        · exact ⟨0, 2, 4, by decide, by decide, by decide, h02, h04⟩
        · have h0 := hf 0
          have h1 := hf 1
          have h3 := hf 3
          have h4 := hf 4
          have h13 : f 1 = f 3 :=
            binary_values_eq_of_ne_common h1 h3 h0 (Ne.symm h01) (Ne.symm h03)
          have h14 : f 1 = f 4 :=
            binary_values_eq_of_ne_common h1 h4 h0 (Ne.symm h01) (Ne.symm h04)
          exact ⟨1, 3, 4, by decide, by decide, by decide, h13, h14⟩
    · have h0 := hf 0
      have h1 := hf 1
      have h2 := hf 2
      have h12 : f 1 = f 2 :=
        binary_values_eq_of_ne_common h1 h2 h0 (Ne.symm h01) (Ne.symm h02)
      by_cases h13 : f 1 = f 3
      · exact ⟨1, 2, 3, by decide, by decide, by decide, h12, h13⟩
      · by_cases h14 : f 1 = f 4
        · exact ⟨1, 2, 4, by decide, by decide, by decide, h12, h14⟩
        · have h3 := hf 3
          have h4 := hf 4
          have h03 : f 0 = f 3 :=
            binary_values_eq_of_ne_common h0 h3 h1 h01 (Ne.symm h13)
          have h04 : f 0 = f 4 :=
            binary_values_eq_of_ne_common h0 h4 h1 h01 (Ne.symm h14)
          exact ⟨0, 3, 4, by decide, by decide, by decide, h03, h04⟩

private theorem quinaryDiagonal_gramIsotropic_of_ternary_indices
    {K : Type*} [Field K] (d : Fin 5 → K) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hiso : GramIsotropic (Matrix.diagonal ![d i, d j, d k])) :
    GramIsotropic (Matrix.diagonal d) := by
  obtain ⟨x, y, z, hxyz, hzero⟩ :=
    (Rat.ternaryDiagonal_gramIsotropic_iff_exists_coordinates
      (d i) (d j) (d k)).mp hiso
  let w : Fin 5 → K := Pi.single i x + Pi.single j y + Pi.single k z
  refine ⟨w, ?_, ?_⟩
  · intro hw
    have hx : x = 0 := by
      have hi := congrFun hw i
      simpa [w, hij, hik] using hi
    have hy : y = 0 := by
      have hj := congrFun hw j
      simpa [w, hij, hjk] using hj
    have hz : z = 0 := by
      have hk := congrFun hw k
      simpa [w, hik, hjk] using hk
    exact hxyz.elim (fun h ↦ h hx) fun h ↦
      h.elim (fun h ↦ h hy) (fun h ↦ h hz)
  · simp only [gramQuadraticValue, Matrix.mulVec_diagonal, dotProduct]
    let F : Fin 5 → K := fun r ↦ w r * (d r * w r)
    have hi_mem : i ∈ (Finset.univ : Finset (Fin 5)) := Finset.mem_univ i
    have hj_mem : j ∈ (Finset.univ : Finset (Fin 5)) \ {i} := by
      simp [hij.symm]
    have hk_mem : k ∈ ((Finset.univ : Finset (Fin 5)) \ {i}) \ {j} := by
      simp [hik.symm, hjk.symm]
    have hrest :
        ∑ r ∈ (((Finset.univ : Finset (Fin 5)) \ {i}) \ {j}) \ {k}, F r = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr' : (r ≠ i ∧ r ≠ j) ∧ r ≠ k := by simpa using hr
      rcases hr' with ⟨⟨hri, hrj⟩, hrk⟩
      simp [F, w, hri, hrj, hrk]
    change ∑ r, F r = 0
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi_mem F]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hj_mem F]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hk_mem F]
    rw [hrest]
    simp [F, w, hij, hik, hjk]
    linear_combination hzero

/-- At an odd prime, a rational diagonal ternary form is isotropic when its
three nonzero coefficients have the same valuation parity. -/
theorem ternaryDiagonal_gramIsotropic_padic_of_valuationParity_eq
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : Rat.valuationParity p a = Rat.valuationParity p b)
    (hac : Rat.valuationParity p a = Rat.valuationParity p c) :
    GramIsotropic
      (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])]) := by
  rcases Rat.valuationParity_eq_zero_or_one p a with hpa | hpa
  · have hpb : Rat.valuationParity p b = 0 := hab.symm.trans hpa
    have hpc : Rat.valuationParity p c = 0 := hac.symm.trans hpa
    obtain ⟨sa, hsa, A, hAunit, hAcast, _⟩ :=
      exists_padicInt_unit_target_square_normalization ha hpa
    obtain ⟨sb, hsb, B, hBunit, hBcast, _⟩ :=
      exists_padicInt_unit_target_square_normalization hb hpb
    obtain ⟨sc, hsc, C, hCunit, hCcast, _⟩ :=
      exists_padicInt_unit_target_square_normalization hc hpc
    let U : Matrix (Fin 3) (Fin 3) ℤ_[p] := Matrix.diagonal ![A, B, C]
    have hU_symm : U.IsSymm := by simp [U]
    have hU_det : IsUnit U.det := by
      simp [U, Matrix.det_diagonal, Fin.prod_univ_three, hAunit, hBunit, hCunit]
    have hUiso : GramIsotropic (U.map PadicInt.Coe.ringHom) :=
      ternary_gramIsotropic_padic_of_integral hpodd U hU_symm hU_det
    have hnormalized : GramIsotropic
        (Matrix.diagonal
          ![((a * sa ^ 2 : ℚ) : ℚ_[p]),
            ((b * sb ^ 2 : ℚ) : ℚ_[p]),
            ((c * sc ^ 2 : ℚ) : ℚ_[p])]) := by
      convert hUiso using 1
      all_goals
        ext i j
        fin_cases i <;> fin_cases j <;> simp [U, hAcast, hBcast, hCcast]
    exact (Rat.ternaryDiagonal_gramIsotropic_mul_sq_each_iff
      (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])
      (sa : ℚ_[p]) (sb : ℚ_[p]) (sc : ℚ_[p])
      (by exact_mod_cast hsa) (by exact_mod_cast hsb) (by exact_mod_cast hsc)).mp
        (by simpa using hnormalized)
  · have hpb : Rat.valuationParity p b = 1 := hab.symm.trans hpa
    have hpc : Rat.valuationParity p c = 1 := hac.symm.trans hpa
    obtain ⟨sa, hsa, D, hDval, hDcast, _⟩ :=
      exists_padicInt_ramified_parameter_square_normalization ha hpa
    obtain ⟨sb, hsb, B, hBunit, hBcast, _⟩ :=
      exists_padicInt_ramified_mul_unit_target_square_normalization hb hpb hDval
    obtain ⟨sc, hsc, C, hCunit, hCcast, _⟩ :=
      exists_padicInt_ramified_mul_unit_target_square_normalization hc hpc hDval
    let U : Matrix (Fin 3) (Fin 3) ℤ_[p] := Matrix.diagonal ![1, B, C]
    have hU_symm : U.IsSymm := by simp [U]
    have hU_det : IsUnit U.det := by
      simp [U, Matrix.det_diagonal, Fin.prod_univ_three, hBunit, hCunit]
    have hUiso : GramIsotropic (U.map PadicInt.Coe.ringHom) :=
      ternary_gramIsotropic_padic_of_integral hpodd U hU_symm hU_det
    have hDne : (D : ℚ_[p]) ≠ 0 := by
      intro hD
      have hD0 : D = 0 := by exact Subtype.ext hD
      simp [hD0] at hDval
    have hscaled : GramIsotropic
        (Matrix.diagonal
          ![(D : ℚ_[p]), ((D * B : ℤ_[p]) : ℚ_[p]),
            ((D * C : ℤ_[p]) : ℚ_[p])]) := by
      have h := (Rat.ternaryDiagonal_gramIsotropic_mul_scalar_iff
        (1 : ℚ_[p]) (B : ℚ_[p]) (C : ℚ_[p]) (D : ℚ_[p]) hDne).2
          (by simpa [U] using hUiso)
      simpa using h
    have hnormalized : GramIsotropic
        (Matrix.diagonal
          ![((a * sa ^ 2 : ℚ) : ℚ_[p]),
            ((b * sb ^ 2 : ℚ) : ℚ_[p]),
            ((c * sc ^ 2 : ℚ) : ℚ_[p])]) := by
      convert hscaled using 1
      all_goals
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hDcast, hBcast, hCcast]
    exact (Rat.ternaryDiagonal_gramIsotropic_mul_sq_each_iff
      (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])
      (sa : ℚ_[p]) (sb : ℚ_[p]) (sc : ℚ_[p])
      (by exact_mod_cast hsa) (by exact_mod_cast hsb) (by exact_mod_cast hsc)).mp
        (by simpa using hnormalized)

/-- Every nondegenerate rational diagonal form of rank five becomes
isotropic over an odd p-adic field.  Among five coefficients, three have the
same valuation parity, and the preceding ternary theorem applies to that
coordinate subform. -/
theorem quinaryDiagonal_gramIsotropic_padic_of_rat
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (d : Fin 5 → ℚ) (hd : ∀ i, d i ≠ 0) :
    GramIsotropic (Matrix.diagonal (fun i ↦ (d i : ℚ_[p]))) := by
  obtain ⟨i, j, k, hij, hik, hjk, hijpar, hikpar⟩ :=
    exists_three_equal_of_five_binary_values
      (fun r ↦ Rat.valuationParity p (d r))
      (fun r ↦ Rat.valuationParity_eq_zero_or_one p (d r))
  have hternary : GramIsotropic
      (Matrix.diagonal ![(d i : ℚ_[p]), (d j : ℚ_[p]), (d k : ℚ_[p])]) :=
    ternaryDiagonal_gramIsotropic_padic_of_valuationParity_eq
      hpodd (hd i) (hd j) (hd k) hijpar hikpar
  exact quinaryDiagonal_gramIsotropic_of_ternary_indices
    (fun r ↦ (d r : ℚ_[p])) i j k hij hik hjk hternary

/-- Every nonsingular symmetric rational rank-five form becomes isotropic
over an odd p-adic field. -/
theorem quinary_gramIsotropic_padic_of_rat
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    GramIsotropic (A.map (algebraMap ℚ ℚ_[p])) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det (by norm_num)
  have hdiag : GramIsotropic
      (Matrix.diagonal (fun i ↦ (d i : ℚ_[p]))) :=
    quinaryDiagonal_gramIsotropic_padic_of_rat hpodd d hd
  have hcongr : (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
      ((Matrix.diagonal d).map (algebraMap ℚ ℚ_[p])) :=
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩).map
      (algebraMap ℚ ℚ_[p])
  apply (gramIsotropic_iff_of_isCongruent hcongr).2
  simpa using hdiag

/-- Every nonsingular symmetric rational form of rank at least five becomes
isotropic over an odd p-adic field.  After rational diagonalization, the
first five diagonal coordinates already contain the isotropic subform. -/
theorem gramIsotropic_padic_of_rat_of_five_le
    {p n : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (hn : 5 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    GramIsotropic (A.map (algebraMap ℚ ℚ_[p])) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det (by norm_num)
  let dp : Fin (5 + k) → ℚ_[p] := fun i ↦ (d i : ℚ_[p])
  let A₅ : Matrix (Fin 5) (Fin 5) ℚ_[p] :=
    Matrix.diagonal (fun i ↦ dp (Fin.castAdd k i))
  let B : Matrix (Fin k) (Fin k) ℚ_[p] :=
    Matrix.diagonal (fun i ↦ -dp (Fin.natAdd 5 i))
  have hA₅iso : GramIsotropic A₅ := by
    apply quinaryDiagonal_gramIsotropic_padic_of_rat hpodd
      (fun i ↦ d (Fin.castAdd k i))
    intro i
    exact hd (Fin.castAdd k i)
  have hblock : GramIsotropic (differenceGramBlock A₅ B) :=
    (gramIsotropic_differenceGramBlock_iff A₅ B).2 (Or.inl hA₅iso)
  have hdiag : GramIsotropic (Matrix.diagonal dp) := by
    rw [← differenceGramBlock_diagonal_split dp]
    exact hblock
  have hcongr : (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
      ((Matrix.diagonal d).map (algebraMap ℚ ℚ_[p])) :=
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩).map
      (algebraMap ℚ ℚ_[p])
  apply (gramIsotropic_iff_of_isCongruent hcongr).2
  simpa [dp] using hdiag

end PositiveDefiniteIntegralLattice
