import SMSFormula.PadicSpecialOrthogonalDifferentialBadPrimeFiniteReductionBoundary
import SMSFormula.SkewAdjointPadicMeasureDilation
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityQuotientFiber
import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizerVolumeIntrinsicCoordinateMass
import SMSFormula.PadicSpecialOrthogonalDifferentialBadPrimeGaugeDefect
import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizerVolumeExtraction
import SMSFormula.PadicSpecialOrthogonalDifferentialGoodPrimeDensityCongruenceElementaryBall

/-!
# An explicit selected-depth coordinate carrier for the density kernel

The density-congruence source contains some noncanonically chosen
form-elementary coordinate ball.  This module makes the
denominator loss explicit.  If `k` is the selected principal-congruence depth
and `v = padicValInt p L.pairingDeterminant`, then the form-elementary ball of level
`k + v` lies in the inverse-Cayley density source.

The proof uses the adjugate identity to show that multiplication by `p ^ v`
sends the local dual lattice into the integral lattice.  It then constructs
the integral Cayley transform directly.  The determinant-one argument is
checked after scalar extension to `Q_p`, so it does not assume that the Gram
matrix is a unit over `Z_p`.

This gives an explicit inner level at every prime.  It does not
assert that the nonlinear inverse-Cayley source is saturated by this additive
ball, identify the source with a finite residue preimage, or evaluate its
measure.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Multiplication by the prime power at the determinant valuation sends the
local dual lattice into the integral lattice. -/
theorem exists_padicIntVector_eq_primePow_mul_of_isLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p v : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant ≤ v)
    (y : Fin n → ℚ_[p]) (hy : L.IsLocalDualPadicVector p y) :
    ∃ u : Fin n → ℤ_[p], ∀ i : Fin n,
      (p : ℚ_[p]) ^ v * y i = (u i : ℚ_[p]) := by
  let z : Fin n → ℤ_[p] := fun i ↦ ⟨_, hy i⟩
  let w : Fin n → ℤ_[p] := (L.pairingMatrix_padic p).adjugate.mulVec z
  have hz : padicIntVectorToPadic p z =
      (L.pairingMatrix_padicField p).mulVec y := rfl
  have hw : padicIntVectorToPadic p w =
      (L.pairingMatrix_padicField p).adjugate.mulVec
        ((L.pairingMatrix_padicField p).mulVec y) := by
    ext i
    change PadicInt.Coe.ringHom
        (((L.pairingMatrix_padic p).adjugate.mulVec z) i) = _
    rw [RingHom.map_mulVec]
    change (((L.pairingMatrix_padic p).adjugate.map PadicInt.Coe.ringHom).mulVec
      (padicIntVectorToPadic p z)) i = _
    have hadj :
        (L.pairingMatrix_padic p).adjugate.map PadicInt.Coe.ringHom =
          (L.pairingMatrix_padicField p).adjugate :=
      PadicInt.Coe.ringHom.map_adjugate _
    rw [hadj, hz]
  have hw_det : ∀ i : Fin n,
      (w i : ℚ_[p]) = (L.pairingDeterminant : ℚ_[p]) * y i := by
    intro i
    have hvec :
        (L.pairingMatrix_padicField p).adjugate.mulVec
            ((L.pairingMatrix_padicField p).mulVec y) =
          fun j ↦ (L.pairingDeterminant : ℚ_[p]) * y j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
        L.pairingMatrix_padicField_det p, Matrix.smul_mulVec, Matrix.one_mulVec]
      rfl
    exact congr_fun (hw.trans hvec) i
  let a : ℤ_[p] :=
    ⟨(p : ℚ_[p]) ^ v * (L.pairingDeterminant : ℚ_[p])⁻¹,
      primePow_mul_inv_intCast_mem_padicInt_subring_of_padicValInt_le
        p v L.pairingDeterminant (ne_of_gt L.pairingDeterminant_pos) hval⟩
  refine ⟨fun i ↦ a * w i, ?_⟩
  intro i
  change (p : ℚ_[p]) ^ v * y i =
    ((p : ℚ_[p]) ^ v * (L.pairingDeterminant : ℚ_[p])⁻¹) * (w i : ℚ_[p])
  rw [hw_det]
  field_simp [ne_of_gt L.pairingDeterminant_pos]

/-- A form-elementary ball whose level includes the determinant valuation has
an integral skew-adjoint lift divisible by the unshifted prime power. -/
theorem
    exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p (k + padicValInt p L.pairingDeterminant)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero) :
    ∃ Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic p)).toSubmodule,
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map
          PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) ∧
      ∀ i j,
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
          (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
  rcases hX with ⟨Z, hZ, hZX⟩
  rw [skewAdjointPadicUniformCoordinateDilation_apply] at hZX
  let Y :=
    skewAdjointFormPadicSkewSymmetricLinearEquiv
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero Z
  have hYupper : ∀ q : StrictUpperPair n,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[p]) q.1.1 q.1.2‖ ≤ 1 := by
    intro q
    have hq :=
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff_upper
        p L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero Z).1 hZ q
    simpa only [
      coe_skewAdjointFormPadicSkewSymmetricLinearEquiv_apply] using hq
  have hYall : ∀ i j,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[p]) i j‖ ≤ 1 :=
    by
      simpa using
        (norm_apply_le_of_skewSymmetric_upper
          (p := p) (k := 0) Y (by simpa using hYupper))
  have hdual : ∀ j : Fin n,
      L.IsLocalDualPadicVector p
        (fun i ↦ (Z : Matrix (Fin n) (Fin n) ℚ_[p]) i j) := by
    intro j i
    apply (PadicInt.mem_subring_iff p).2
    change
      ‖(L.pairingMatrix_padicField p *
        (Z : Matrix (Fin n) (Fin n) ℚ_[p])) i j‖ ≤ 1
    simpa only [
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p] using
        hYall i j
  choose u hu using fun j ↦
    L.exists_padicIntVector_eq_primePow_mul_of_isLocalDual
      p (padicValInt p L.pairingDeterminant) (le_refl _) _ (hdual j)
  let Xzm : Matrix (Fin n) (Fin n) ℤ_[p] :=
    fun i j ↦ (p : ℤ_[p]) ^ k * u j i
  have hXzmap :
      Xzm.map PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    ext i j
    change
      (p : ℚ_[p]) ^ k * (u j i : ℚ_[p]) =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) i j
    rw [← hu j i]
    have hentry := congrArg
      (fun A :
          (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule ↦
        (A : Matrix (Fin n) (Fin n) ℚ_[p]) i j) hZX
    simpa [pow_add, mul_assoc] using hentry
  have hXzmem : ∀ i j,
      Xzm i j ∈
        (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    exact (Ideal.mem_span_singleton).2 ⟨u j i, rfl⟩
  have hXzskew :
      Xzm ∈ skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic p) := by
    apply (mem_ker_skewAdjointOperator_iff _ _).mp
    apply LinearMap.mem_ker.mpr
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    have hXop :
        skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
            (X : Matrix (Fin n) (Fin n) ℚ_[p]) = 0 :=
      LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
          (X : Matrix (Fin n) (Fin n) ℚ_[p])).mpr X.property)
    have hmap :
        (skewAdjointOperator (L.pairingMatrix_padic p) Xzm).map
            PadicInt.Coe.ringHom =
          skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
            (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
      have hFmap :
          (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom =
            L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) :=
        (L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p).symm
      simp only [skewAdjointOperator_apply]
      rw [Matrix.map_add _ (fun a b ↦
        map_add PadicInt.Coe.ringHom a b),
        Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
        hXzmap, hFmap]
    change
      ((skewAdjointOperator (L.pairingMatrix_padic p) Xzm).map
        PadicInt.Coe.ringHom) i j = 0
    rw [hmap, hXop]
    rfl
  exact ⟨⟨Xzm, hXzskew⟩, hXzmap, hXzmem⟩

end PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ}

/-- An integral Cayley transform is an integral matrix unit congruent to one
as soon as the numerator and denominator determinants agree.  This version
does not require the integral form matrix to be a unit. -/
theorem exists_padicInt_cayley_GL_toZModPow_eq_one_of_det_one_add_eq_det_one_sub
    {p k : ℕ} [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (X : Matrix (Fin n) (Fin n) ℤ_[p])
    (hX : ∀ i j,
      X i j ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]))
    (hdet : (1 + X).det = (1 - X).det) :
    ∃ U : GL (Fin n) ℤ_[p],
      U.1 = cayleyRingForwardMatrix X ∧
      (∀ i j,
        PadicInt.toZModPow k (U.1 i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j) ∧
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix (X.map PadicInt.Coe.ringHom) := by
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := 1 - X
  have hA : IsUnit A :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow hk X hX
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
  have htwoX : ∀ i j,
      (cayleyRingTwoMatrix (ι := Fin n) (R := ℤ_[p]) * X) i j ∈
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
    rw [show C = cayleyRingForwardMatrix X from rfl,
      cayleyRingForwardMatrix_sub_one X hA, Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    exact Ideal.mul_mem_right _ _ (htwoX i a)
  have hreduce : ∀ i j,
      PadicInt.toZModPow k (U.1 i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
    intro i j
    have hker := hD i j
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker] at hker
    change
      PadicInt.toZModPow k
        (C i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0 at hker
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
  exact ⟨U, hU, hreduce, hmap⟩

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- An integral skew-adjoint lift divisible by the selected prime power maps
under the integral Cayley transform into the selected density kernel. -/
theorem
    mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_skewAdjoint_lift_mem_span_pow
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (Xz :
      (skewAdjointMatricesLieSubalgebra
        (L.pairingMatrix_padic p)).toSubmodule)
    (hXzmap :
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map
          PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]))
    (hXzmem : ∀ i j,
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
        (Ideal.span
          {(p : ℤ_[p]) ^
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p} :
          Ideal ℤ_[p])) :
    X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  have hk : 1 ≤ k := le_trans (by norm_num)
    (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
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
    exists_padicInt_cayley_GL_toZModPow_eq_one_of_det_one_add_eq_det_one_sub
      hk (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) hXzmem hdet
  have hdenom :
      IsUnit (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) := by
    have hz :
        IsUnit (1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) :=
      padicIntMatrix_one_sub_isUnit_of_mem_span_pow
        hk (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) hXzmem
    have hmap := hz.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    change IsUnit
      ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map
        PadicInt.Coe.ringHom) at hmap
    simpa only [Matrix.map_sub _ (fun a b ↦
      map_sub PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
      hXzmap] using hmap
  let xSource :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
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

/-- The selected principal density kernel contains the explicit
form-elementary ball obtained by adding the determinant valuation to the
selected congruence depth. -/
theorem
    skewAdjointFormElementaryPadicUniformCoordinateBall_add_pairingDeterminantVal_subset_densityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ⊆
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  intro X hX
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  obtain ⟨Xz, hXzmap, hXzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
      p k X hX
  exact
    L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_skewAdjoint_lift_mem_span_pow
      p X Xz hXzmap hXzmem

/-- At an odd prime the density source is explicitly sandwiched between the
form-elementary balls at levels `depth + v_p(det F)` and `depth`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruence_explicit_formElementaryUniformCoordinateBall_sandwich
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ⊆
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ∧
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ⊆
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
  ⟨L.skewAdjointFormElementaryPadicUniformCoordinateBall_add_pairingDeterminantVal_subset_densityCongruenceSourceAmbientSet
      p,
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall
      p hp2⟩

end PositiveDefiniteIntegralLattice
