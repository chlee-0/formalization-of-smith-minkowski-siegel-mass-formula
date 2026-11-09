import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicCayleyDepth
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeResidue

/-!
# Dyadic translation for the density source

The one-power inverse-Cayley estimate gives here an integral skew-adjoint
representative of every dyadic source point.  This is the input
needed for an integral forward-Cayley comparison with a perturbation from the
selected determinant-loss inner ball.

No residue count or dyadic gauge value is asserted.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- Adding a depth-`k` dyadic perturbation to a matrix divisible at depth
`k - 1` preserves the integral forward-Cayley domain and changes the forward
transform only by entries divisible at depth `k`.  The proof keeps both
noncommuting denominator factors and removes them only as integral matrix
units. -/
theorem entriesMemIdeal_cayleyRingForwardMatrix_add_sub_dyadic
    (k : ℕ) (hk : 2 ≤ k)
    (X Y : Matrix (Fin n) (Fin n) ℤ_[2])
    (hX : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)}) X)
    (hY : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ k}) Y) :
    IsUnit (1 - X) ∧
      IsUnit (1 - (X + Y)) ∧
      entriesMemIdeal
        (Ideal.span {(2 : ℤ_[2]) ^ k})
        (cayleyRingForwardMatrix (X + Y) -
          cayleyRingForwardMatrix X) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkpred : 1 ≤ k - 1 := by omega
  have hYpred : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)}) Y := by
    intro i j
    rcases (Ideal.mem_span_singleton.mp (hY i j)) with ⟨z, hz⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(2 : ℤ_[2]) * z, ?_⟩
    rw [hz, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hXY : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)}) (X + Y) := by
    intro i j
    exact Ideal.add_mem _ (hX i j) (hYpred i j)
  have hXunit : IsUnit (1 - X) :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow hkpred X hX
  have hXYunit : IsUnit (1 - (X + Y)) :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow hkpred (X + Y) hXY
  refine ⟨hXunit, hXYunit, ?_⟩
  let UX : GL (Fin n) ℤ_[2] := hXunit.unit
  let UXY : GL (Fin n) ℤ_[2] := hXYunit.unit
  have hUX : UX.1 = 1 - X := hXunit.unit_spec
  have hUXY : UXY.1 = 1 - (X + Y) := hXYunit.unit_spec
  have hcross := cayleyRingForwardMatrix_sub_cross
    (X + Y) X hXYunit hXunit
  have hright : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ k})
      (cayleyRingTwoMatrix * ((X + Y) - X)) := by
    apply entriesMemIdeal_mul_left
    simpa using hY
  have hequiv :
      entriesMemIdeal
          (Ideal.span {(2 : ℤ_[2]) ^ k})
          (cayleyRingForwardMatrix (X + Y) - cayleyRingForwardMatrix X) ↔
        entriesMemIdeal
          (Ideal.span {(2 : ℤ_[2]) ^ k})
          ((1 - (X + Y)) *
            (cayleyRingForwardMatrix (X + Y) - cayleyRingForwardMatrix X) *
              (1 - X)) := by
    rw [← hUXY, ← hUX,
      entriesMemIdeal_mul_unit_iff,
      entriesMemIdeal_unit_mul_iff]
  apply hequiv.mpr
  rw [hcross]
  exact hright

/-- Package an integral forward Cayley matrix as a matrix unit when its
denominator is already known to be a unit and its numerator and denominator
determinants agree.  The unit has the same given finite reduction. -/
theorem exists_padicInt_cayley_GL_of_source_and_reduction
    {p k : ℕ} [Fact (Nat.Prime p)]
    (X : Matrix (Fin n) (Fin n) ℤ_[p])
    (hX : X ∈ cayleyRingSource)
    (hdet : (1 + X).det = (1 - X).det)
    (hreduce : ∀ i j,
      PadicInt.toZModPow k (cayleyRingForwardMatrix X i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j) :
    ∃ U : GL (Fin n) ℤ_[p],
      U.1 = cayleyRingForwardMatrix X ∧
      (∀ i j,
        PadicInt.toZModPow k (U.1 i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j) ∧
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix (X.map PadicInt.Coe.ringHom) := by
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := 1 - X
  have hA : IsUnit A := hX
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  let C : Matrix (Fin n) (Fin n) ℤ_[p] := cayleyRingForwardMatrix X
  have hCdet : C.det = 1 := by
    change ((1 + X) * A⁻¹).det = 1
    rw [Matrix.det_mul, hdet, mul_comm]
    exact Matrix.det_nonsing_inv_mul_det A hAdet
  have hCunit : IsUnit C := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [hCdet]
    exact isUnit_one
  let U : GL (Fin n) ℤ_[p] := hCunit.unit
  have hU : U.1 = C := hCunit.unit_spec
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
        cayleyRingForwardMatrix (X.map PadicInt.Coe.ringHom) := by
    change U.1.map PadicInt.Coe.ringHom =
      cayleyRingForwardMatrix (X.map PadicInt.Coe.ringHom)
    rw [hU]
    change
      ((1 + X) * A⁻¹).map PadicInt.Coe.ringHom =
        (1 + X.map PadicInt.Coe.ringHom) *
          (1 - X.map PadicInt.Coe.ringHom)⁻¹
    rw [Matrix.map_mul, hAinvmap]
    congr 1
    · rw [Matrix.map_add _ (fun a b ↦
        map_add PadicInt.Coe.ringHom a b),
        Matrix.map_one PadicInt.Coe.ringHom
          (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]
    · congr 1
      rw [show A = 1 - X from rfl,
        Matrix.map_sub _ (fun a b ↦
          map_sub PadicInt.Coe.ringHom a b),
        Matrix.map_one PadicInt.Coe.ringHom
          (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]
  refine ⟨U, hU, ?_, hmap⟩
  intro i j
  rw [hU]
  exact hreduce i j

/-- Scalar extension commutes with the integral forward Cayley formula once
the integral denominator is a matrix unit. -/
theorem map_cayleyRingForwardMatrix_padicInt
    {p : ℕ} [Fact (Nat.Prime p)]
    (X : Matrix (Fin n) (Fin n) ℤ_[p])
    (hX : X ∈ cayleyRingSource) :
    (cayleyRingForwardMatrix X).map PadicInt.Coe.ringHom =
      cayleyRingForwardMatrix (X.map PadicInt.Coe.ringHom) := by
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := 1 - X
  have hA : IsUnit A := hX
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
  change
    ((1 + X) * A⁻¹).map PadicInt.Coe.ringHom =
      (1 + X.map PadicInt.Coe.ringHom) *
        (1 - X.map PadicInt.Coe.ringHom)⁻¹
  rw [Matrix.map_mul, hAinvmap]
  congr 1
  · rw [Matrix.map_add _ (fun a b ↦
      map_add PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]
  · congr 1
    rw [show A = 1 - X from rfl,
      Matrix.map_sub _ (fun a b ↦
        map_sub PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A skew-adjoint integral coordinate belongs to the selected density source
whenever its integral forward Cayley transform has the selected principal
reduction.  Unlike the earlier inner-ball constructor, this interface does
not require the coordinate itself to be divisible by the full selected prime
power. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_forwardCayley_reduction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (Xz :
      (skewAdjointMatricesLieSubalgebra
        (L.pairingMatrix_padic p)).toSubmodule)
    (hXzmap :
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]))
    (hXzsource :
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) ∈ Matrix.cayleyRingSource)
    (hreduce : ∀ i j,
      PadicInt.toZModPow
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
          (cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
        (1 : Matrix (Fin n) (Fin n)
          (ZMod
            (p ^
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p))) i j) :
    X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  have hdet :
      (1 + (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).det =
        (1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).det := by
    apply PadicInt.ext
    calc
      ((1 + (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).det : ℚ_[p]) =
          ((1 + (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map
            PadicInt.Coe.ringHom).det :=
        PadicInt.Coe.ringHom.map_det _
      _ = (1 + (X : Matrix (Fin n) (Fin n) ℚ_[p])).det := by
        rw [Matrix.map_add _ (fun a b ↦
          map_add PadicInt.Coe.ringHom a b),
          Matrix.map_one PadicInt.Coe.ringHom
            (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
          hXzmap]
      _ = (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])).det := by
        apply skewAdjointCayleyRing_det_one_add_eq_det_one_sub
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
        exact (isUnit_iff_ne_zero).2 (by
          change
            ((algebraMap ℚ ℚ_[p]).mapMatrix
              L.rationalFormMatrix).det ≠ 0
          rw [← RingHom.map_det]
          intro hzero
          apply L.rationalFormMatrix_det_ne_zero
          apply (algebraMap ℚ ℚ_[p]).injective
          simpa using hzero)
      _ = ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map
            PadicInt.Coe.ringHom).det := by
        rw [Matrix.map_sub _ (fun a b ↦
          map_sub PadicInt.Coe.ringHom a b),
          Matrix.map_one PadicInt.Coe.ringHom
            (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
          hXzmap]
      _ = ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).det : ℚ_[p]) :=
        (PadicInt.Coe.ringHom.map_det _).symm
  obtain ⟨U, hU, hUreduce, hUmap⟩ :=
    Matrix.exists_padicInt_cayley_GL_of_source_and_reduction
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) hXzsource hdet hreduce
  have hdenom :
      IsUnit (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) := by
    have hmap := hXzsource.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    change IsUnit
      ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map
        PadicInt.Coe.ringHom) at hmap
    simpa only [Matrix.map_sub _ (fun a b ↦
      map_sub PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
      hXzmap] using hmap
  let xSource : Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
    ⟨X, hdenom⟩
  let t :
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1 :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 xSource
  let g :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) := t.1
  let Uq : GL (Fin n) ℚ_[p] :=
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U
  have hUq :
      Uq.1 = cayleyRingForwardMatrix
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[p])
    rw [hUmap, hXzmap]
  have hg :
      g.1.1.1 = cayleyRingForwardMatrix
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    change
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1
          xSource).1.1.1.1 =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[p])
    rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
    change
      (1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
          ((1 + (X : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹) = _
    rw [Matrix.one_mul]
    rfl
  have hgunits : g.1.1 = Uq := by
    apply Units.ext
    exact hg.trans hUq.symm
  have hgint :
      g ∈ L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p := by
    apply
      (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
        p g).2
    constructor
    · intro i j
      rw [hgunits, Matrix.GeneralLinearGroup.map_apply]
      exact (U.1 i j).property
    · intro i j
      rw [hgunits, ← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact ((U⁻¹).1 i j).property
  let gd :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p :=
    ⟨g, hgint⟩
  have hgkernel :
      gd ∈
        L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p k := by
    apply
      (L.mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
        p k gd).2
    apply
      (L.mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
        p k
        (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
          p gd)).2
    intro i j
    have hint :
        L.localPadicLatticeStabilizerIntegralGL p
            (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
              p gd).1 i j = U.1 i j := by
      apply PadicInt.ext
      rw [L.localPadicLatticeStabilizerIntegralGL_apply]
      change g.1.1.1 i j = ((U.1 i j : ℤ_[p]) : ℚ_[p])
      rw [hgunits, Matrix.GeneralLinearGroup.map_apply]
      rfl
    rw [hint]
    exact hUreduce i j
  refine ⟨xSource, ?_, rfl⟩
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1
        xSource).1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet p
  exact ⟨gd, hgkernel, rfl⟩

/-- Every point of the dyadic density source has an integral skew-adjoint
representative divisible by one less power of two than the selected
principal-congruence depth. -/
theorem
    exists_integral_skewAdjoint_lift_mem_span_pow_pred_of_mem_dyadicDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n)
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hX : X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2) :
    ∃ Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic 2)).toSubmodule,
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map
          PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[2]) ∧
      ∀ i j,
        (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) i j ∈
          (Ideal.span
            {(2 : ℤ_[2]) ^
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2 - 1)} : Ideal ℤ_[2]) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  rcases
      L.exists_densityCongruenceKernel_inverse_formula_and_reduction_of_mem_sourceAmbientSet
        2 X hX with
    ⟨g, hg, hformula, hreduction⟩
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical 2 g
  let G : GL (Fin n) ℤ_[2] :=
    L.localPadicLatticeStabilizerIntegralGL 2 h.1
  have hbound0 :=
    Matrix.norm_integralMatrix_mul_dyadicIntegralCayleyInverse_le_pow_pred
      k
      (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
      (1 : Matrix (Fin n) (Fin n) ℤ_[2]) G hreduction
  have hGmap :
      G.1.map PadicInt.Coe.ringHom =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]) := by
    ext i j
    exact L.localPadicLatticeStabilizerIntegralGL_apply 2 h.1 i j
  have hbound : ∀ i j,
      ‖(X : Matrix (Fin n) (Fin n) ℚ_[2]) i j‖ ≤
        ‖(2 : ℚ_[2]) ^ (k - 1)‖ := by
    intro i j
    have hij := hbound0 i j
    rw [hGmap, ← hformula] at hij
    simpa using hij
  have hpow_le_one : ‖(2 : ℚ_[2]) ^ (k - 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (le_of_lt Padic.norm_p_lt_one)
  let Xzm : Matrix (Fin n) (Fin n) ℤ_[2] :=
    fun i j ↦
      ⟨(X : Matrix (Fin n) (Fin n) ℚ_[2]) i j,
        (PadicInt.mem_subring_iff 2).2 ((hbound i j).trans hpow_le_one)⟩
  have hXzmap :
      Xzm.map PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    rfl
  have hnormpow :
      (2 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) =
        ‖(2 : ℚ_[2]) ^ (k - 1)‖ := by
    rw [norm_pow, Matrix.norm_two_dyadic]
    simp [inv_pow]
  have hXzmem : ∀ i j,
      Xzm i j ∈
        (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)} : Ideal ℤ_[2]) := by
    intro i j
    apply (PadicInt.norm_le_pow_iff_mem_span_pow (Xzm i j) (k - 1)).1
    change
      ‖(X : Matrix (Fin n) (Fin n) ℚ_[2]) i j‖ ≤
        (2 : ℝ) ^ (-((k - 1 : ℕ) : ℤ))
    rw [hnormpow]
    exact hbound i j
  have hXzskew :
      Xzm ∈ skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic 2) := by
    apply (mem_ker_skewAdjointOperator_iff _ _).mp
    apply LinearMap.mem_ker.mpr
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    have hXop :
        skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))
            (X : Matrix (Fin n) (Fin n) ℚ_[2]) = 0 :=
      LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))
          (X : Matrix (Fin n) (Fin n) ℚ_[2])).mpr X.property)
    have hmap :
        (skewAdjointOperator (L.pairingMatrix_padic 2) Xzm).map
            PadicInt.Coe.ringHom =
          skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))
            (X : Matrix (Fin n) (Fin n) ℚ_[2]) := by
      have hFmap :
          (L.pairingMatrix_padic 2).map PadicInt.Coe.ringHom =
            L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]) :=
        (L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField 2).symm
      simp only [skewAdjointOperator_apply]
      rw [Matrix.map_add _ (fun a b ↦
        map_add PadicInt.Coe.ringHom a b),
        Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
        hXzmap, hFmap]
    change
      ((skewAdjointOperator (L.pairingMatrix_padic 2) Xzm).map
        PadicInt.Coe.ringHom) i j = 0
    rw [hmap, hXop]
    rfl
  exact ⟨⟨Xzm, hXzskew⟩, hXzmap, hXzmem⟩

/-- Adding a perturbation from the selected determinant-loss inner ball
preserves the dyadic density source.  The source coordinate itself is only
known integral at depth `k - 1`; the exact forward-Cayley comparison recovers
the full depth-`k` principal reduction after the perturbation. -/
theorem
    add_mem_dyadicDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_add_pairingDeterminantVal
    (L : PositiveDefiniteIntegralLattice n)
    (X Y :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hX : X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2)
    (hY : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
          padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    X + Y ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  obtain ⟨Xz, hXzmap, hXzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_pred_of_mem_dyadicDensityCongruenceSourceAmbientSet
      X hX
  obtain ⟨Yz, hYzmap, hYzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
      2 k Y hY
  obtain ⟨hXzsource, hsumsource, hforwardDiff⟩ :=
    Matrix.entriesMemIdeal_cayleyRingForwardMatrix_add_sub_dyadic
      k
      (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2])
      (Yz : Matrix (Fin n) (Fin n) ℤ_[2])
      hXzmem hYzmem
  obtain ⟨g, hg, hXinv⟩ :=
    L.exists_densityCongruenceKernel_eq_inverseCayley_of_mem_sourceAmbientSet
      2 X hX
  let e :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix 2 L.rationalFormMatrix_det_ne_zero 1
  let target :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint
      2 g hg
  have happly :
      e (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
        2 g hg) = target := by
    exact e.apply_symm_apply target
  have hforwardq :
      cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[2]) =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]) := by
    rw [hXinv]
    calc
      cayleyRingForwardMatrix
          (((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
              2 g hg).1 : Matrix (Fin n) (Fin n) ℚ_[2])) =
        (e
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
            2 g hg)).1.1.1.1 := by
          rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
          change _ =
            (1 : Matrix (Fin n) (Fin n) ℚ_[2]) * _
          rw [Matrix.one_mul]
          rfl
      _ = target.1.1.1.1 := congrArg (fun z ↦ z.1.1.1.1) happly
      _ = _ := rfl
  let gh :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical 2 g
  let G : GL (Fin n) ℤ_[2] :=
    L.localPadicLatticeStabilizerIntegralGL 2 gh.1
  have hGmap :
      G.1.map PadicInt.Coe.ringHom =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]) := by
    ext i j
    exact L.localPadicLatticeStabilizerIntegralGL_apply 2 gh.1 i j
  have hforwardXz :
      cayleyRingForwardMatrix
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) = G.1 := by
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    have hmap := Matrix.map_cayleyRingForwardMatrix_padicInt
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) hXzsource
    have hmap' :
        (cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
              PadicInt.Coe.ringHom =
          ((g :
            specialFormPreservingMatrixSubgroup
              (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
                Matrix (Fin n) (Fin n) ℚ_[2]) := by
      exact hmap.trans (by rw [hXzmap, hforwardq])
    exact congrFun (congrFun (hmap'.trans hGmap.symm) i) j
  have hreduceSum : ∀ i j,
      PadicInt.toZModPow k
          (cayleyRingForwardMatrix
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]) +
              (Yz : Matrix (Fin n) (Fin n) ℤ_[2])) i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (2 ^ k))) i j := by
    intro i j
    have hker := hforwardDiff i j
    have hker' :
        ((cayleyRingForwardMatrix
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]) +
              (Yz : Matrix (Fin n) (Fin n) ℤ_[2])) -
          cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) i j) ∈
          RingHom.ker (PadicInt.toZModPow k) := by
      simpa only [PadicInt.ker_toZModPow] using hker
    rw [RingHom.mem_ker] at hker'
    change
      PadicInt.toZModPow k
        (cayleyRingForwardMatrix
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]) +
              (Yz : Matrix (Fin n) (Fin n) ℤ_[2])) i j -
          cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) i j) = 0 at hker'
    rw [map_sub] at hker'
    rw [sub_eq_zero.mp hker', hforwardXz]
    exact
      L.localPadicSpecialOrthogonalDifferentialDensityCongruence_reduction_apply
        2 g hg i j
  have hsumMap :
      (((Xz + Yz :
          (skewAdjointMatricesLieSubalgebra
            (L.pairingMatrix_padic 2)).toSubmodule) :
          Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom) =
        ((X + Y :
          (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[2]) := by
    simp only [Submodule.coe_add, Matrix.map_add _ (fun a b ↦
      map_add PadicInt.Coe.ringHom a b), hXzmap, hYzmap]
  exact
    L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_forwardCayley_reduction
      2 (X + Y) (Xz + Yz) hsumMap hsumsource hreduceSum

/-- The selected determinant-loss inner ball acts by additive translations on
the dyadic density source. -/
theorem
    add_mem_dyadicDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_add_pairingDeterminantVal
    (L : PositiveDefiniteIntegralLattice n)
    (X Y :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hY : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
          padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    X + Y ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2 ↔
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnegY : -Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
          padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
    apply
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
          padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero (-Y)).2
    intro q
    have hq :=
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
          padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero Y).1 hY q
    simpa using hq
  constructor
  · intro hXY
    have h :=
      L.add_mem_dyadicDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_add_pairingDeterminantVal
        (X + Y) (-Y) hXY hnegY
    simpa [add_assoc] using h
  · intro hX
    exact
      L.add_mem_dyadicDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_add_pairingDeterminantVal
        X Y hX hY

end PositiveDefiniteIntegralLattice
