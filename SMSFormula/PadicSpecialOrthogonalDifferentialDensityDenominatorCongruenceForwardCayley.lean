import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceCayleyBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceSelectedDepthCarrier

/-!
# Forward Cayley transform for the denominator-congruence subgroup

This module proves the converse of the inverse-Cayley result for `H_k`.
A form-adapted coordinate at the selected level has an integral skew-adjoint
lift.  Its entrywise integrality loses the form-determinant valuation, but its
columns retain the full selected local-dual denominator condition.

This column denominator condition, rather than merely entrywise divisibility,
is the input needed to show that the integral forward Cayley transform belongs
to `H_k`.  The forward and inverse transforms are proved mutually inverse,
giving an exact equivalence between `H_k` and the selected-level form-adapted
ball.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Right multiplication in the forward Cayley formula preserves any
columnwise submodule condition already satisfied by `X`. -/
theorem cayleyRingForwardMatrix_sub_one_column_mem_submodule
    (D : Submodule R (Fin n → R)) (X : Matrix (Fin n) (Fin n) R)
    (hsource : X ∈ cayleyRingSource)
    (hX : ∀ j : Fin n, (fun i ↦ X i j) ∈ D) :
    ∀ j : Fin n,
      (fun i ↦ (cayleyRingForwardMatrix X - 1) i j) ∈ D := by
  let P : Matrix (Fin n) (Fin n) R := cayleyRingTwoMatrix * X
  let B : Matrix (Fin n) (Fin n) R := (1 - X)⁻¹
  have hP : ∀ j : Fin n, (fun i ↦ P i j) ∈ D := by
    intro j
    have hsmul := D.smul_mem (2 : R) (hX j)
    change (fun i ↦
      (cayleyRingTwoMatrix (ι := Fin n) (R := R) * X) i j) ∈ D
    rw [show cayleyRingTwoMatrix (ι := Fin n) (R := R) * X =
        (2 : R) • X by
      rw [smul_eq_diagonal_mul]
      rfl]
    simpa [Matrix.smul_apply, Pi.smul_apply] using hsmul
  intro j
  rw [cayleyRingForwardMatrix_sub_one X hsource]
  have hsum : (∑ l : Fin n, B l j • (fun i ↦ P i l)) ∈ D :=
    D.sum_mem fun l _ ↦ D.smul_mem (B l j) (hP l)
  convert hsum using 1
  funext i
  simp [P, B, Matrix.mul_apply, Pi.smul_apply, mul_comm]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A level-`k` form-adapted coordinate, beyond the form-determinant
valuation, has an integral skew-adjoint lift whose columns retain the full
level-`k` local-dual denominator.  Entrywise, the certified integral lift is
divisible by `p^(k-v_p(det F))`. -/
theorem
    exists_integral_skewAdjoint_lift_mem_denominator_of_mem_formElementaryUniformCoordinateBall
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hval : padicValInt p L.pairingDeterminant < k)
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p k L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    ∃ Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic p)).toSubmodule,
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom =
          (X : Matrix (Fin n) (Fin n) ℚ_[p]) ∧
      (∀ j : Fin n,
        (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
          localDualPadicDenominator L p k) ∧
      ∀ i j,
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
          (Ideal.span
            {(p : ℤ_[p]) ^ (k - padicValInt p L.pairingDeterminant)} :
            Ideal ℤ_[p]) := by
  have hvle : padicValInt p L.pairingDeterminant ≤ k := Nat.le_of_lt hval
  have hlevel :
      k - padicValInt p L.pairingDeterminant + padicValInt p L.pairingDeterminant = k :=
    Nat.sub_add_cancel hvle
  obtain ⟨Xz, hXzmap, hXzdiv⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
      p (k - padicValInt p L.pairingDeterminant) X (by simpa [hlevel] using hX)
  refine ⟨Xz, hXzmap, ?_, hXzdiv⟩
  let Y :=
    skewAdjointFormPadicSkewSymmetricLinearEquiv
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero X
  have hYupper : ∀ q : StrictUpperPair n,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[p]) q.1.1 q.1.2‖ ≤
        ‖(p : ℚ_[p]) ^ k‖ := by
    intro q
    have hq :=
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        p k L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero X).1 hX q
    simpa only [coe_skewAdjointFormPadicSkewSymmetricLinearEquiv_apply] using hq
  have hYall : ∀ i j,
      ‖(Y : Matrix (Fin n) (Fin n) ℚ_[p]) i j‖ ≤
        ‖(p : ℚ_[p]) ^ k‖ :=
    norm_apply_le_of_skewSymmetric_upper Y hYupper
  have hFXmap :
      (L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])).map PadicInt.Coe.ringHom =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
          (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    rw [Matrix.map_mul]
    exact congrArg₂ (fun A B : Matrix (Fin n) (Fin n) ℚ_[p] ↦ A * B)
      (L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p).symm hXzmap
  have hFXdiv : ∀ i j,
      (L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) i j ∈
          (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    apply (PadicInt.norm_le_pow_iff_mem_span_pow _ k).1
    have hij := hYall i j
    change
      ‖(L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p])) i j‖ ≤
          ‖(p : ℚ_[p]) ^ k‖ at hij
    rw [← hFXmap] at hij
    change
      ‖(((L.pairingMatrix_padic p *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) i j : ℤ_[p]) : ℚ_[p])‖ ≤
          ‖(p : ℚ_[p]) ^ k‖ at hij
    rw [show
      ‖(((L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) i j : ℤ_[p]) : ℚ_[p])‖ =
        ‖(L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) i j‖ from rfl] at hij
    calc
      ‖(L.pairingMatrix_padic p *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p])) i j‖ ≤
          ‖(p : ℚ_[p]) ^ k‖ := hij
      _ = (p : ℝ) ^ (-(k : ℤ)) := by
        rw [norm_pow, Padic.norm_p]
        simp [inv_pow]
  intro j
  rw [L.mem_localDualPadicDenominator_iff_forall_padic]
  intro x
  rw [dotProduct]
  apply Finset.dvd_sum
  intro i _
  apply dvd_mul_of_dvd_right
  rw [Matrix.mulVec, dotProduct]
  simpa using Ideal.mem_span_singleton.mp (hFXdiv i j)

/-- Every selected-level form-adapted coordinate has a literal integral
forward Cayley transform in `H_k`.  The constructed stabilizer has the stated
integral matrix, and the completed inverse-Cayley coordinate recovers `X`. -/
theorem
    exists_densityDenominatorCongruence_forwardCayley_of_mem_formElementaryUniformCoordinateBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    ∃ (Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic p)).toSubmodule)
      (g :
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p),
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom =
          (X : Matrix (Fin n) (Fin n) ℚ_[p]) ∧
      (∀ j : Fin n,
        (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j) ∈
          localDualPadicDenominator L p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) ∧
      (L.localPadicLatticeStabilizerIntegralGL p g.1).1 =
        cayleyRingForwardMatrix
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) ∧
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
          p hp2 g = X := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  let v := padicValInt p L.pairingDeterminant
  let e := k - v
  have hvk : v < k :=
    L.padicValInt_pairingDeterminant_lt_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  have he : 1 ≤ e := by omega
  obtain ⟨Xz, hXzmap, hXzcols, hXzdiv⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_denominator_of_mem_formElementaryUniformCoordinateBall
      p k hvk X hX
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
  obtain ⟨U, hU, _hUreduce, hUmap⟩ :=
    exists_padicInt_cayley_GL_toZModPow_eq_one_of_det_one_add_eq_det_one_sub
      he (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) hXzdiv hdet
  have hsourceZ :
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) ∈ cayleyRingSource :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow
      he (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) hXzdiv
  have hsourceQ :
      (X : Matrix (Fin n) (Fin n) ℚ_[p]) ∈ cayleyRingSource := by
    have hmap := hsourceZ.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
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
    ⟨X, hsourceQ⟩
  let t :
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1 :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 xSource
  let gq :
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
  have hgq :
      gq.1.1.1 = cayleyRingForwardMatrix
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
  have hgqunits : gq.1.1 = Uq := by
    apply Units.ext
    exact hgq.trans hUq.symm
  have hgqint :
      gq ∈ L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p := by
    apply
      (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
        p gq).2
    constructor
    · intro i j
      rw [hgqunits, Matrix.GeneralLinearGroup.map_apply]
      exact (U.1 i j).property
    · intro i j
      rw [hgqunits, ← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact ((U⁻¹).1 i j).property
  let gd :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p :=
    ⟨gq, hgqint⟩
  let s : L.localPadicLatticeStabilizerSubgroup p :=
    (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
      p gd).1
  have hsU :
      (L.localPadicLatticeStabilizerIntegralGL p s).1 = U.1 := by
    ext i j
    apply PadicInt.ext
    rw [L.localPadicLatticeStabilizerIntegralGL_apply]
    change gq.1.1.1 i j = ((U.1 i j : ℤ_[p]) : ℚ_[p])
    rw [hgqunits, Matrix.GeneralLinearGroup.map_apply]
    rfl
  have hforwardCols : ∀ j : Fin n,
      (fun i ↦
        (cayleyRingForwardMatrix
          (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) - 1) i j) ∈
        localDualPadicDenominator L p k :=
    cayleyRingForwardMatrix_sub_one_column_mem_submodule
      (localDualPadicDenominator L p k)
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) hsourceZ hXzcols
  have hsH :
      s ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p := by
    rw [localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup,
      L.mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
    intro j
    rw [hsU, hU]
    exact hforwardCols j
  let g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p :=
    ⟨s, hsH⟩
  have hsmap :
      (L.localPadicLatticeStabilizerIntegralGL p s).1.map
          PadicInt.Coe.ringHom =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    rw [hsU]
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 = _
    exact hUq
  have hinverse :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
          p hp2 g = X := by
    apply Subtype.ext
    rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_eq_ringFormula]
    change
      cayleyRingInverseMatrix
          ((L.localPadicLatticeStabilizerIntegralGL p s).1.map
            PadicInt.Coe.ringHom) =
        (X : Matrix (Fin n) (Fin n) ℚ_[p])
    rw [hsmap]
    exact cayleyRingInverseMatrix_forward
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[p]) ≠ 0))
      (X : Matrix (Fin n) (Fin n) ℚ_[p]) hsourceQ
  exact ⟨Xz, g, hXzmap, hXzcols, hsU.trans hU, hinverse⟩

/-- The selected-level form-adapted coordinate ball, as a type. -/
abbrev
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFormCoordinateBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :=
  {X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule //
    X ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero}

/-- The chosen integral forward Cayley transform from the selected-level
form-adapted ball into `H_k`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFormCoordinateBall p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p :=
  Classical.choose (Classical.choose_spec
    (L.exists_densityDenominatorCongruence_forwardCayley_of_mem_formElementaryUniformCoordinateBall
      p hp2 X.1 X.2))

/-- Inverse Cayley after the chosen forward Cayley transform is literally the
original selected-level coordinate. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_forwardCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFormCoordinateBall p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2
        (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley
          p hp2 X) = X.1 := by
  let h :=
    L.exists_densityDenominatorCongruence_forwardCayley_of_mem_formElementaryUniformCoordinateBall
      p hp2 X.1 X.2
  change
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 (Classical.choose (Classical.choose_spec h)) = X.1
  exact (Classical.choose_spec (Classical.choose_spec h)).2.2.2

/-- The inverse-Cayley coordinate is injective on `H_k` at an odd prime. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_injective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Function.Injective
      (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2) := by
  intro g h hgh
  let G := (L.localPadicLatticeStabilizerIntegralGL p g.1).1
  let H := (L.localPadicLatticeStabilizerIntegralGL p h.1).1
  have hGz : IsUnit (G + 1) :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 g
  have hHz : IsUnit (H + 1) :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 h
  have hGq :
      G.map PadicInt.Coe.ringHom ∈ cayleyRingInverseDomain := by
    have hm := hGz.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    change IsUnit ((G + 1).map PadicInt.Coe.ringHom) at hm
    simpa only [Matrix.map_add _ (fun a b ↦
      map_add PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)] using hm
  have hHq :
      H.map PadicInt.Coe.ringHom ∈ cayleyRingInverseDomain := by
    have hm := hHz.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    change IsUnit ((H + 1).map PadicInt.Coe.ringHom) at hm
    simpa only [Matrix.map_add _ (fun a b ↦
      map_add PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)] using hm
  have h2q : IsUnit (2 : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hmap : G.map PadicInt.Coe.ringHom = H.map PadicInt.Coe.ringHom := by
    calc
      G.map PadicInt.Coe.ringHom =
          cayleyRingForwardMatrix
            (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
              p hp2 g : Matrix (Fin n) (Fin n) ℚ_[p]) := by
        rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_eq_ringFormula]
        exact (cayleyRingForwardMatrix_inverse h2q _ hGq).symm
      _ = cayleyRingForwardMatrix
            (L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
              p hp2 h : Matrix (Fin n) (Fin n) ℚ_[p]) := by rw [hgh]
      _ = H.map PadicInt.Coe.ringHom := by
        rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_eq_ringFormula]
        exact cayleyRingForwardMatrix_inverse h2q _ hHq
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  change g.1.1.1.1 i j = h.1.1.1.1 i j
  change
    (((G i j : ℤ_[p]) : ℚ_[p])) = (((H i j : ℤ_[p]) : ℚ_[p]))
  exact congr_fun (congr_fun hmap i) j

/-- The chosen forward Cayley transform is also a left inverse of the
completed inverse-Cayley coordinate on `H_k`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley_inverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley
        p hp2
        ⟨L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
            p hp2 g,
          L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
            p hp2 g⟩ = g := by
  apply
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_injective
      p hp2
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_forwardCayley
      p hp2 _

/-- At an odd prime, inverse Cayley identifies `H_k` exactly with the
selected-level form-adapted coordinate ball. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceCayleyEquiv
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p ≃
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceFormCoordinateBall p where
  toFun g :=
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley
        p hp2 g,
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_mem_formElementaryUniformCoordinateBall
        p hp2 g⟩
  invFun :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley
      p hp2
  left_inv :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley_inverseCayley
      p hp2
  right_inv X := by
    apply Subtype.ext
    exact
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayley_forwardCayley
        p hp2 X

end PositiveDefiniteIntegralLattice
