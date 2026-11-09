import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceElementaryCoordinates
import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeCoordinateTarget
import SMSFormula.SkewAdjointPadicElementaryCoordinateMeasureScale
import SMSFormula.CayleyRingAlgebra

/-!
# The good-prime density kernel is an elementary coordinate ball

At a prime outside the Schulze--Pillot bad-prime set, the integral form
matrix is a matrix unit.  This lets us reverse the elementary-coordinate
bound already proved for the density-adapted inverse Cayley kernel: an
elementary coordinate vector divisible by the selected prime power has an
integral forward Cayley transform congruent to the identity at that depth.

This file proves only the converse containment and the resulting exact set
equality.  It does not evaluate the ball measure or substitute it into the
local-density comparison.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- A strict-upper norm bound on a skew-symmetric matrix controls every
entry, including the zero diagonal. -/
theorem norm_apply_le_of_skewSymmetric_upper
    {p k : ℕ} [Fact (Nat.Prime p)]
    (Y : skewSymmetricMatricesSubmodule
      (R := ℚ_[p]) (ι := Fin n))
    (hY : ∀ q : StrictUpperPair n,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[p]) q.1.1 q.1.2‖ ≤
        ‖(p : ℚ_[p]) ^ k‖) :
    ∀ i j,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[p]) i j‖ ≤
        ‖(p : ℚ_[p]) ^ k‖ := by
  intro i j
  by_cases hij : i = j
  · subst j
    have hdiag :=
      congr_fun (congr_fun Y.property i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hdiag
    have hzero :
        (Y : Matrix (Fin n) (Fin n) ℚ_[p]) i i = 0 := by
      apply (mul_left_cancel₀ (show (2 : ℚ_[p]) ≠ 0 by norm_num))
      linear_combination hdiag
    rw [hzero, norm_zero]
    exact norm_nonneg _
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact hY ⟨⟨i, j⟩, hij⟩
    · have hskew :=
        congr_fun (congr_fun Y.property j) i
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at hskew
      rw [hskew, norm_neg]
      exact hY ⟨⟨j, i⟩, hji⟩

/-- A p-adic integral matrix divisible by a positive power of `p` has
invertible Cayley denominator `1 - X`. -/
theorem padicIntMatrix_one_sub_isUnit_of_mem_span_pow
    {p k : ℕ} [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (X : Matrix (Fin n) (Fin n) ℤ_[p])
    (hX : ∀ i j,
      X i j ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])) :
    IsUnit (1 - X) := by
  have hspan :
      (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) ≤
        Ideal.span {(p : ℤ_[p])} := by
    apply Ideal.span_le.2
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact (Ideal.mem_span_singleton).2
      (dvd_pow_self _ (Nat.ne_of_gt hk))
  have hXmod : X.map PadicInt.toZMod = 0 := by
    ext i j
    have hij :
        X i j ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact hspan (hX i j)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hij
    exact hij
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hzero
  have htozero : PadicInt.toZMod (1 - X).det = 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    simp [hzero]
  have htoone : PadicInt.toZMod (1 - X).det = 1 := by
    rw [RingHom.map_det]
    change ((1 - X).map PadicInt.toZMod).det = 1
    rw [Matrix.map_sub _ (fun a b ↦
      map_sub PadicInt.toZMod a b),
      Matrix.map_one PadicInt.toZMod
        (map_zero PadicInt.toZMod) (map_one PadicInt.toZMod),
      hXmod,
      sub_zero, Matrix.det_one]
  rw [htoone] at htozero
  exact one_ne_zero htozero

/-- The ring-level Cayley transform of a divisible integral skew-adjoint
matrix is an integral matrix unit congruent to one.  Its scalar extension is
the literal field-level Cayley formula. -/
theorem exists_padicInt_cayley_GL_toZModPow_eq_one
    {p k : ℕ} [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (F : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : IsUnit F.det)
    (X :
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hX : ∀ i j,
      (X : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
        (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p])) :
    ∃ U : GL (Fin n) ℤ_[p],
      U.1 =
          cayleyRingForwardMatrix
            (X : Matrix (Fin n) (Fin n) ℤ_[p]) ∧
      (∀ i j,
        PadicInt.toZModPow k (U.1 i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j) ∧
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix
          ((X : Matrix (Fin n) (Fin n) ℤ_[p]).map
            PadicInt.Coe.ringHom) := by
  let Xm : Matrix (Fin n) (Fin n) ℤ_[p] := X
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := 1 - Xm
  have hA : IsUnit A := by
    exact padicIntMatrix_one_sub_isUnit_of_mem_span_pow hk Xm hX
  have hsource : Xm ∈ cayleyRingSource := hA
  let C : Matrix (Fin n) (Fin n) ℤ_[p] :=
    cayleyRingForwardMatrix Xm
  have hCdet : C.det = 1 := by
    exact skewAdjointCayleyRingForwardMatrix_det_one F hF X hsource
  have hCunit : IsUnit C := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [hCdet]
    exact isUnit_one
  let U : GL (Fin n) ℤ_[p] := hCunit.unit
  have hU : U.1 = C := hCunit.unit_spec
  have htwoX : ∀ i j,
      (cayleyRingTwoMatrix (ι := Fin n) (R := ℤ_[p]) *
        Xm) i j ∈
          (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    rw [Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    exact Ideal.mul_mem_left _ _ (hX a j)
  have hD : ∀ i j,
      (C - 1) i j ∈
        (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    rw [show C = cayleyRingForwardMatrix Xm from rfl,
      cayleyRingForwardMatrix_sub_one Xm hsource,
      Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    exact Ideal.mul_mem_right _ _
      (htwoX i a)
  have hreduce : ∀ i j,
      PadicInt.toZModPow k (U.1 i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
    intro i j
    have hker := hD i j
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker] at hker
    change
      PadicInt.toZModPow k
        (C i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0
      at hker
    rw [map_sub] at hker
    have hone :
        PadicInt.toZModPow k
            ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [hone] at hker
    rw [hU]
    exact sub_eq_zero.mp hker
  have hAinvmap :
      A⁻¹.map PadicInt.Coe.ringHom =
        (A.map PadicInt.Coe.ringHom)⁻¹ := by
    rw [show A⁻¹ = (hA.unit⁻¹).1 by
      rw [Matrix.coe_units_inv, hA.unit_spec]]
    change
      (Matrix.GeneralLinearGroup.map
          PadicInt.Coe.ringHom hA.unit⁻¹).1 =
        (A.map PadicInt.Coe.ringHom)⁻¹
    rw [map_inv, Matrix.coe_units_inv]
    congr 1
  have hmap :
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix
          (Xm.map PadicInt.Coe.ringHom) := by
    change U.1.map PadicInt.Coe.ringHom =
      cayleyRingForwardMatrix (Xm.map PadicInt.Coe.ringHom)
    rw [hU]
    change
      ((1 + Xm) * A⁻¹).map PadicInt.Coe.ringHom =
        (1 + Xm.map PadicInt.Coe.ringHom) *
          (1 - Xm.map PadicInt.Coe.ringHom)⁻¹
    rw [Matrix.map_mul, hAinvmap]
    congr 1
    · rw [Matrix.map_add _ (fun a b ↦
        map_add PadicInt.Coe.ringHom a b),
        Matrix.map_one PadicInt.Coe.ringHom
          (map_zero PadicInt.Coe.ringHom)
          (map_one PadicInt.Coe.ringHom)]
    · congr 1
      rw [show A = 1 - Xm from rfl,
        Matrix.map_sub _ (fun a b ↦
          map_sub PadicInt.Coe.ringHom a b),
        Matrix.map_one PadicInt.Coe.ringHom
          (map_zero PadicInt.Coe.ringHom)
          (map_one PadicInt.Coe.ringHom)]
  exact ⟨U, hU, hreduce, hmap⟩

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Away from the Schulze--Pillot bad-prime set, the integral form matrix is
a matrix unit over the p-adic integers. -/
theorem pairingMatrix_padic_isUnit_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L) :
    IsUnit (L.pairingMatrix_padic q.1) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hdet :
      (L.pairingMatrix_padic q.1).det = (L.pairingDeterminant : ℤ_[q.1]) := by
    change
      (L.pairingMatrix.map (Int.castRingHom ℤ_[q.1])).det =
        (L.pairingDeterminant : ℤ_[q.1])
    exact ((Int.castRingHom ℤ_[q.1]).map_det L.pairingMatrix).symm
  rw [hdet, PadicInt.isUnit_iff,
    padicInt_norm_intCast_eq_padicValInt q.1
      (ne_of_gt L.pairingDeterminant_pos),
    ← L.padicValInt_polarDeterminant_eq_padicValInt_pairingDeterminant_of_ne_two q.1
      (L.not_mem_massBadPrimeSet_ne_two hq),
    L.padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet hq]
  norm_num

/-- A point of the selected form-adapted ball at a good prime has an
integral skew-adjoint lift whose entries are all divisible by the selected
prime power. -/
theorem
    exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L)
    (k : ℕ)
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map
          (algebraMap ℚ ℚ_[q.1]))).toSubmodule)
    (hX : X ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        q.1 k L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    ∃ Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic q.1)).toSubmodule,
      (Xz : Matrix (Fin n) (Fin n) ℤ_[q.1]).map
          PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) ∧
      ∀ i j,
        (Xz : Matrix (Fin n) (Fin n) ℤ_[q.1]) i j ∈
          (Ideal.span {(q.1 : ℤ_[q.1]) ^ k} : Ideal ℤ_[q.1]) := by
  let Fz := L.pairingMatrix_padic q.1
  let Fq := L.pairingMatrix_padicField q.1
  let Y :=
    skewAdjointFormPadicSkewSymmetricLinearEquiv
      q.1 L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero X
  have hYupper : ∀ r : StrictUpperPair n,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[q.1]) r.1.1 r.1.2‖ ≤
        ‖(q.1 : ℚ_[q.1]) ^ k‖ := by
    intro r
    have hr :=
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        q.1 k L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero X).1 hX r
    simpa only [
      coe_skewAdjointFormPadicSkewSymmetricLinearEquiv_apply] using hr
  have hYall : ∀ i j,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[q.1]) i j‖ ≤
        ‖(q.1 : ℚ_[q.1]) ^ k‖ :=
    norm_apply_le_of_skewSymmetric_upper Y hYupper
  have hpow_le_one : ‖(q.1 : ℚ_[q.1]) ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (le_of_lt Padic.norm_p_lt_one)
  let Yz : Matrix (Fin n) (Fin n) ℤ_[q.1] :=
    fun i j ↦
      ⟨(Y : Matrix (Fin n) (Fin n) ℚ_[q.1]) i j,
        (PadicInt.mem_subring_iff q.1).2
          (le_trans (hYall i j) hpow_le_one)⟩
  have hYzmap :
      Yz.map PadicInt.Coe.ringHom =
        (Y : Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
    rfl
  have hYzmem : ∀ i j,
      Yz i j ∈
        (Ideal.span {(q.1 : ℤ_[q.1]) ^ k} : Ideal ℤ_[q.1]) := by
    intro i j
    apply (PadicInt.norm_le_pow_iff_mem_span_pow (Yz i j) k).1
    change
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[q.1]) i j‖ ≤
        (q.1 : ℝ) ^ (-(k : ℤ))
    calc
      _ ≤ ‖(q.1 : ℚ_[q.1]) ^ k‖ := hYall i j
      _ = (q.1 : ℝ) ^ (-(k : ℤ)) := by
        rw [norm_pow, Padic.norm_p]
        simp [inv_pow]
  have hFunit : IsUnit Fz := by
    exact L.pairingMatrix_padic_isUnit_of_not_mem_massBadPrimeSet q hq
  let U : GL (Fin n) ℤ_[q.1] := hFunit.unit
  let B : Matrix (Fin n) (Fin n) ℤ_[q.1] := (U⁻¹).1
  let Xzm : Matrix (Fin n) (Fin n) ℤ_[q.1] := B * Yz
  have hBmap :
      B.map PadicInt.Coe.ringHom = Fq⁻¹ := by
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U⁻¹).1 =
        Fq⁻¹
    rw [map_inv, Matrix.coe_units_inv]
    congr 1
  have hFqdet : IsUnit Fq.det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    exact hFunit.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
  have hXzmap :
      Xzm.map PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
    rw [show Xzm = B * Yz from rfl, Matrix.map_mul, hBmap, hYzmap]
    change
      Fq⁻¹ *
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) *
            (X : Matrix (Fin n) (Fin n) ℚ_[q.1])) =
        (X : Matrix (Fin n) (Fin n) ℚ_[q.1])
    calc
      Fq⁻¹ *
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) *
              (X : Matrix (Fin n) (Fin n) ℚ_[q.1])) =
          Fq⁻¹ * (Fq *
            (X : Matrix (Fin n) (Fin n) ℚ_[q.1])) := by
        congr 2
      _ = (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Fq hFqdet,
          Matrix.one_mul]
  have hXzmem : ∀ i j,
      Xzm i j ∈
        (Ideal.span {(q.1 : ℤ_[q.1]) ^ k} : Ideal ℤ_[q.1]) := by
    intro i j
    rw [show Xzm = B * Yz from rfl, Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    exact Ideal.mul_mem_left _ _ (hYzmem a j)
  have hXzskew :
      Xzm ∈ skewAdjointMatricesLieSubalgebra Fz := by
    apply
      (mem_ker_skewAdjointOperator_iff Fz Xzm).mp
    apply LinearMap.mem_ker.mpr
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    have hXop :
        skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))
            (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) = 0 :=
      LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))
          (X : Matrix (Fin n) (Fin n) ℚ_[q.1])).mpr X.property)
    have hmap :
        (skewAdjointOperator Fz Xzm).map PadicInt.Coe.ringHom =
          skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))
            (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
      have hFmap :
          Fz.map PadicInt.Coe.ringHom =
            L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]) := by
        exact
          L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField q.1
            |>.symm
      simp only [skewAdjointOperator_apply]
      rw [Matrix.map_add _ (fun a b ↦
        map_add PadicInt.Coe.ringHom a b),
        Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
        hXzmap, hFmap]
    change
      ((skewAdjointOperator Fz Xzm).map
        PadicInt.Coe.ringHom) i j = 0
    rw [hmap, hXop]
    rfl
  exact ⟨⟨Xzm, hXzskew⟩, hXzmap, hXzmem⟩

/-- At a Schulze--Pillot good prime, the form-adapted ball at the selected
density depth lies in the density-adapted inverse-Cayley kernel. -/
theorem
    skewAdjointFormElementaryPadicUniformCoordinateBall_subset_densityCongruenceSourceAmbientSet_of_not_mem_badPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L) :
    skewAdjointFormElementaryPadicUniformCoordinateBall
        q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ⊆
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        q.1 := by
  intro X hX
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1
  have hk : 1 ≤ k := by
    exact le_trans (by norm_num)
      (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
        q.1)
  obtain ⟨Xz, hXzmap, hXzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall
      q hq k X hX
  have hFmatrix :
      IsUnit (L.pairingMatrix_padic q.1) :=
    L.pairingMatrix_padic_isUnit_of_not_mem_massBadPrimeSet q hq
  have hFdet :
      IsUnit (L.pairingMatrix_padic q.1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hFmatrix
  obtain ⟨U, hU, hUreduce, hUmap⟩ :=
    exists_padicInt_cayley_GL_toZModPow_eq_one
      hk (L.pairingMatrix_padic q.1) hFdet Xz hXzmem
  have hdenom :
      IsUnit
        (1 -
          (X : Matrix (Fin n) (Fin n) ℚ_[q.1])) := by
    have hz :
        IsUnit
          (1 -
            (Xz : Matrix (Fin n) (Fin n) ℤ_[q.1])) :=
      padicIntMatrix_one_sub_isUnit_of_mem_span_pow
        hk (Xz : Matrix (Fin n) (Fin n) ℤ_[q.1]) hXzmem
    have hmap :=
      hz.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    change
      IsUnit
        ((1 -
          (Xz : Matrix (Fin n) (Fin n) ℤ_[q.1])).map
            PadicInt.Coe.ringHom) at hmap
    simpa only [
      Matrix.map_sub _ (fun a b ↦
        map_sub PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom)
        (map_one PadicInt.Coe.ringHom),
      hXzmap] using hmap
  let xSource :
      Matrix.skewAdjointPadicCayleySource
        L.rationalFormMatrix q.1 :=
    ⟨X, hdenom⟩
  let t :
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix q.1 1 :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix q.1
        L.rationalFormMatrix_det_ne_zero 1 xSource
  let g :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map
          (algebraMap ℚ ℚ_[q.1])) :=
    t.1
  let Uq : GL (Fin n) ℚ_[q.1] :=
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U
  have hUq :
      Uq.1 =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[q.1])
    rw [hUmap, hXzmap]
  have hg :
      g.1.1.1 =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
    change
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix q.1
          L.rationalFormMatrix_det_ne_zero 1 xSource).1.1.1.1 =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[q.1])
    rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
    change
      (1 : Matrix (Fin n) (Fin n) ℚ_[q.1]) *
          ((1 + (X : Matrix (Fin n) (Fin n) ℚ_[q.1])) *
            (1 - (X : Matrix (Fin n) (Fin n) ℚ_[q.1]))⁻¹) =
        (1 + (X : Matrix (Fin n) (Fin n) ℚ_[q.1])) *
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[q.1]))⁻¹
    rw [Matrix.one_mul]
  have hgunits : g.1.1 = Uq := by
    apply Units.ext
    exact hg.trans hUq.symm
  have hgint :
      g ∈
        L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
          q.1 := by
    apply
      (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
        q.1 g).2
    constructor
    · intro i j
      rw [hgunits, Matrix.GeneralLinearGroup.map_apply]
      exact (U.1 i j).property
    · intro i j
      rw [hgunits, ← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact ((U⁻¹).1 i j).property
  let gd :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup q.1 :=
    ⟨g, hgint⟩
  have hgkernel :
      gd ∈
        L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          q.1 k := by
    apply
      (L.mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
        q.1 k gd).2
    apply
      (L.mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
        q.1 k
        (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
          q.1 gd)).2
    intro i j
    have hint :
        L.localPadicLatticeStabilizerIntegralGL q.1
            (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
              q.1 gd).1 i j =
          U.1 i j := by
      apply PadicInt.ext
      rw [L.localPadicLatticeStabilizerIntegralGL_apply]
      change g.1.1.1 i j =
        ((U.1 i j : ℤ_[q.1]) : ℚ_[q.1])
      rw [hgunits, Matrix.GeneralLinearGroup.map_apply]
      rfl
    rw [hint]
    exact hUreduce i j
  refine ⟨xSource, ?_, rfl⟩
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix q.1
        L.rationalFormMatrix_det_ne_zero 1 xSource).1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
        q.1
  exact ⟨gd, hgkernel, rfl⟩

/-- At a Schulze--Pillot good prime, the density-adapted inverse-Cayley
kernel is exactly the form-adapted uniform coordinate ball at the selected
principal-congruence depth. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_eq_formElementaryUniformCoordinateBall_of_not_mem_badPrimeSet
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    [Fact (Nat.Prime q.1)]
    (hq : q ∉ massBadPrimeSet L) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        q.1 =
      skewAdjointFormElementaryPadicUniformCoordinateBall
        q.1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth q.1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
  apply Set.Subset.antisymm
  · exact
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall
        q.1
        (L.not_mem_massBadPrimeSet_ne_two hq)
  · exact
      L.skewAdjointFormElementaryPadicUniformCoordinateBall_subset_densityCongruenceSourceAmbientSet_of_not_mem_badPrimeSet
        q hq

end PositiveDefiniteIntegralLattice
