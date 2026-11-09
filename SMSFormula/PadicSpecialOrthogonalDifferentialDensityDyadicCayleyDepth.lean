import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicGaugeBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceSelectedDepthCarrier

/-!
# The one-power dyadic loss in inverse Cayley coordinates

For a dyadic integral matrix `G` congruent to one modulo `2^k`, with
`2 <= k`, write `G - 1 = 2 E`.  The half-difference `E` is integral and is
divisible by `2^(k-1)`, while `1 + E` is an integral matrix unit.  Hence

`G + 1 = 2 (1 + E)`

and the common scalar two cancels in the rational inverse-Cayley formula.
The resulting coordinate has exactly the certified outer depth `k - 1`.

No translation saturation, residue-cardinality formula, or dyadic gauge value
is asserted.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- An integral p-adic matrix reducing to the identity modulo the residue
prime is a matrix unit. -/
theorem padicIntMatrix_isUnit_of_toZMod_eq_one
    {p : ℕ} [Fact (Nat.Prime p)]
    (A : Matrix (Fin n) (Fin n) ℤ_[p])
    (hA : ∀ i j, PadicInt.toZMod (A i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j) :
    IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hmap : A.map PadicInt.toZMod = 1 := by
    ext i j
    exact hA i j
  have hmoddet : IsUnit (PadicInt.toZMod A.det) := by
    rw [RingHom.map_det]
    change IsUnit (A.map PadicInt.toZMod).det
    rw [hmap]
    simp
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hzero
  have htozero : PadicInt.toZMod A.det = 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    simp [hzero]
  exact (isUnit_iff_ne_zero.mp hmoddet) htozero

/-- Entrywise divisibility by `2^k`, for positive `k`, admits an exact
integral half still divisible by `2^(k-1)`. -/
theorem exists_padicIntMatrix_half_mem_span_pow_pred
    (k : ℕ) (hk : 1 ≤ k)
    (D : Matrix (Fin n) (Fin n) ℤ_[2])
    (hD : ∀ i j,
      D i j ∈ (Ideal.span {(2 : ℤ_[2]) ^ k} : Ideal ℤ_[2])) :
    ∃ E : Matrix (Fin n) (Fin n) ℤ_[2],
      (2 : ℤ_[2]) • E = D ∧
      ∀ i j,
        E i j ∈
          (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)} : Ideal ℤ_[2]) := by
  choose z hz using fun i j ↦ Ideal.mem_span_singleton.mp (hD i j)
  let E : Matrix (Fin n) (Fin n) ℤ_[2] :=
    fun i j ↦ (2 : ℤ_[2]) ^ (k - 1) * z i j
  refine ⟨E, ?_, ?_⟩
  · ext i j
    change (2 : ℤ_[2]) * ((2 : ℤ_[2]) ^ (k - 1) * z i j) = D i j
    rw [hz i j]
    rw [← mul_assoc, mul_comm (2 : ℤ_[2]), ← pow_succ]
    rw [Nat.sub_add_cancel hk]
  · intro i j
    exact (Ideal.mem_span_singleton).2 ⟨z i j, rfl⟩

/-- At depth at least two, the dyadic inverse-Cayley coordinate loses exactly
one certified prime power after the common scalar two is cancelled. -/
theorem norm_integralMatrix_mul_dyadicIntegralCayleyInverse_le_pow_pred
    (k : ℕ) (hk : 2 ≤ k)
    (F : Matrix (Fin n) (Fin n) ℤ_[2])
    (G : GL (Fin n) ℤ_[2])
    (hG : ∀ i j, PadicInt.toZModPow k (G.1 i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod (2 ^ k))) i j) :
    ∀ i j,
      ‖(F.map PadicInt.Coe.ringHom *
          ((G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
            (G.1.map PadicInt.Coe.ringHom - 1))) i j‖ ≤
        ‖(2 : ℚ_[2]) ^ (k - 1)‖ := by
  let D : Matrix (Fin n) (Fin n) ℤ_[2] := G.1 - 1
  have hD : ∀ i j,
      D i j ∈ (Ideal.span {(2 : ℤ_[2]) ^ k} : Ideal ℤ_[2]) := by
    intro i j
    have hz : D i j ∈ RingHom.ker (PadicInt.toZModPow k) := by
      rw [RingHom.mem_ker]
      dsimp [D]
      rw [map_sub, hG]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    simpa only [PadicInt.ker_toZModPow] using hz
  obtain ⟨E, htwoE, hE⟩ :=
    exists_padicIntMatrix_half_mem_span_pow_pred k (by omega) D hD
  have hkpred : 1 ≤ k - 1 := by omega
  have hspan :
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)} : Ideal ℤ_[2]) ≤
        Ideal.span {(2 : ℤ_[2])} := by
    apply Ideal.span_le.2
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact (Ideal.mem_span_singleton).2
      (dvd_pow_self _ (Nat.ne_of_gt hkpred))
  have hEmod : ∀ i j, PadicInt.toZMod (E i j) = 0 := by
    intro i j
    have hemax : E i j ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact hspan (hE i j)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hemax
    exact hemax
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have hAmod : ∀ i j, PadicInt.toZMod (A i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j := by
    intro i j
    dsimp [A]
    rw [map_add, hEmod]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hA : IsUnit A :=
    padicIntMatrix_isUnit_of_toZMod_eq_one A hAmod
  let U : GL (Fin n) ℤ_[2] := hA.unit
  let B : Matrix (Fin n) (Fin n) ℤ_[2] := (U⁻¹).1
  have hU : U.1 = A := hA.unit_spec
  have hBmap :
      B.map PadicInt.Coe.ringHom =
        (A.map PadicInt.Coe.ringHom)⁻¹ := by
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U⁻¹).1 =
        (A.map PadicInt.Coe.ringHom)⁻¹
    rw [map_inv, Matrix.coe_units_inv]
    change
      (U.1.map PadicInt.Coe.ringHom)⁻¹ =
        (A.map PadicInt.Coe.ringHom)⁻¹
    rw [hU]
  have hDmap :
      D.map PadicInt.Coe.ringHom =
        G.1.map PadicInt.Coe.ringHom - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  have htwoEmap :
      (2 : ℚ_[2]) • E.map PadicInt.Coe.ringHom =
        G.1.map PadicInt.Coe.ringHom - 1 := by
    rw [← hDmap]
    ext i j
    have hij := congrFun (congrFun htwoE i) j
    simp only [Matrix.smul_apply] at hij
    change PadicInt.Coe.ringHom ((2 : ℤ_[2]) * E i j) =
      PadicInt.Coe.ringHom (D i j)
    exact congrArg PadicInt.Coe.ringHom (by simpa [smul_eq_mul] using hij)
  have hGplus :
      G.1.map PadicInt.Coe.ringHom + 1 =
        (2 : ℚ_[2]) • A.map PadicInt.Coe.ringHom := by
    dsimp [A]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b)]
    rw [Matrix.map_one PadicInt.Coe.ringHom (map_zero _) (map_one _)]
    calc
      G.1.map PadicInt.Coe.ringHom + 1 =
          (G.1.map PadicInt.Coe.ringHom - 1) +
            (2 : ℚ_[2]) • (1 : Matrix (Fin n) (Fin n) ℚ_[2]) := by
              module
      _ = (2 : ℚ_[2]) • E.map PadicInt.Coe.ringHom +
            (2 : ℚ_[2]) • (1 : Matrix (Fin n) (Fin n) ℚ_[2]) := by
              rw [htwoEmap]
      _ = (2 : ℚ_[2]) •
            (1 + E.map PadicInt.Coe.ringHom) := by module
  have hAq : IsUnit (A.map PadicInt.Coe.ringHom) := by
    rw [← hU]
    exact
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).isUnit
  have hGplusUnit :
      IsUnit (G.1.map PadicInt.Coe.ringHom + 1) := by
    rw [hGplus, smul_eq_diagonal_mul]
    exact
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[2]) ≠ 0)).map
          (Matrix.scalar (Fin n)) |>.mul hAq
  have hcancel :
      (G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
          (G.1.map PadicInt.Coe.ringHom - 1) =
        B.map PadicInt.Coe.ringHom * E.map PadicInt.Coe.ringHom := by
    apply hGplusUnit.mul_left_cancel
    have hGplusDet :
        IsUnit (G.1.map PadicInt.Coe.ringHom + 1).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hGplusUnit
    have hAdet : IsUnit (A.map PadicInt.Coe.ringHom).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hAq
    calc
      (G.1.map PadicInt.Coe.ringHom + 1) *
          ((G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
            (G.1.map PadicInt.Coe.ringHom - 1)) =
          G.1.map PadicInt.Coe.ringHom - 1 := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGplusDet,
              one_mul]
      _ = (2 : ℚ_[2]) • E.map PadicInt.Coe.ringHom := htwoEmap.symm
      _ = (G.1.map PadicInt.Coe.ringHom + 1) *
          (B.map PadicInt.Coe.ringHom *
            E.map PadicInt.Coe.ringHom) := by
            rw [hGplus, hBmap]
            rw [smul_mul_assoc]
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAdet,
              one_mul]
  let C : Matrix (Fin n) (Fin n) ℤ_[2] := F * B * E
  have hC : ∀ i j,
      C i j ∈
        (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)} : Ideal ℤ_[2]) := by
    intro i j
    dsimp [C]
    rw [Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    apply Ideal.mul_mem_left
    exact hE a j
  intro i j
  have hnormInt :=
    (PadicInt.norm_le_pow_iff_mem_span_pow (C i j) (k - 1)).2 (hC i j)
  have hCmap :
      C.map PadicInt.Coe.ringHom =
        F.map PadicInt.Coe.ringHom *
          ((G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
            (G.1.map PadicInt.Coe.ringHom - 1)) := by
    dsimp [C]
    rw [Matrix.map_mul, Matrix.map_mul, hcancel, Matrix.mul_assoc]
  rw [← hCmap]
  change ‖((C i j : ℤ_[2]) : ℚ_[2])‖ ≤ _
  have hnormcoe : ‖((C i j : ℤ_[2]) : ℚ_[2])‖ = ‖C i j‖ := rfl
  rw [hnormcoe]
  calc
    ‖C i j‖ ≤ (2 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) := hnormInt
    _ = ‖(2 : ℚ_[2]) ^ (k - 1)‖ := by
      rw [norm_pow, norm_two_dyadic]
      simp [inv_pow]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The complete dyadic density source lies in the form-adapted coordinate
ball one level shallower than the selected principal-congruence depth. -/
theorem
    localPadicSpecialOrthogonalDifferentialDyadicDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall_pred
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 ⊆
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro X hX
  apply
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero X).2
  intro q
  rcases
      L.exists_densityCongruenceKernel_inverse_formula_and_reduction_of_mem_sourceAmbientSet
        2 X hX with
    ⟨g, hg, hformula, hreduction⟩
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical 2 g
  let G : GL (Fin n) ℤ_[2] :=
    L.localPadicLatticeStabilizerIntegralGL 2 h.1
  have hbound :=
    norm_integralMatrix_mul_dyadicIntegralCayleyInverse_le_pow_pred
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
      (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
      (L.pairingMatrix_padic 2) G hreduction q.1.1 q.1.2
  have hGmap :
      G.1.map PadicInt.Coe.ringHom =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]) := by
    ext i j
    exact L.localPadicLatticeStabilizerIntegralGL_apply 2 h.1 i j
  rw [hGmap] at hbound
  rw [hformula]
  simpa only [
    L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField 2] using hbound

/-- The exact selected dyadic source sandwich: the general determinant-loss
inner ball remains valid at two, while the inverse-Cayley outer ball loses one
level.  No additive saturation between these levels is inferred. -/
theorem
    localPadicSpecialOrthogonalDifferentialDyadicDensityCongruence_explicit_formElementaryUniformCoordinateBall_sandwich
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
          padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ⊆
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 ∧
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 ⊆
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    ⟨L.skewAdjointFormElementaryPadicUniformCoordinateBall_add_pairingDeterminantVal_subset_densityCongruenceSourceAmbientSet
        2,
      L.localPadicSpecialOrthogonalDifferentialDyadicDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall_pred⟩

end PositiveDefiniteIntegralLattice
