import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDoubledAttainedResidueCardinality
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley

/-!
# Forward Cayley construction for the shifted dyadic denominator subgroup

The complete shifted dyadic subgroup `H₂` is naturally reached from the
form-coordinate ball two levels below the selected ordinary reduction depth.
For such a coordinate `X`, an integral skew-adjoint lift has columns in the
local-dual denominator at depth `k - 2`.  The literal numerator two in

`cayleyForward(X) - 1 = 2 X (1 - X)⁻¹`

raises those columns to depth `k - 1`, which is exactly the condition defining
`H₂`.  This module constructs the resulting integral stabilizer and proves
that its scaled inverse-Cayley coordinate is literally `2 X`.

No finite-residue surjectivity, additive closure, quotient descent,
cardinality identity, or dyadic gauge value is asserted.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_dyadic_forward_cayley : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The numerator two in the forward Cayley difference raises a columnwise
local-dual denominator condition by one level. -/
theorem
    cayleyRingForwardMatrix_sub_one_column_mem_localDualPadicDenominator_succ
    (L : PositiveDefiniteIntegralLattice n) (r : ℕ)
    (hr : L.IsHenselLatticeDepth 2 r)
    (X : Matrix (Fin n) (Fin n) ℤ_[2])
    (hsource : X ∈ cayleyRingSource)
    (hX : ∀ j : Fin n,
      (fun i ↦ X i j) ∈ localDualPadicDenominator L 2 r) :
    ∀ j : Fin n,
      (fun i ↦ (cayleyRingForwardMatrix X - 1) i j) ∈
        localDualPadicDenominator L 2 (r + 1) := by
  let P : Matrix (Fin n) (Fin n) ℤ_[2] := cayleyRingTwoMatrix * X
  let B : Matrix (Fin n) (Fin n) ℤ_[2] := (1 - X)⁻¹
  have hP : ∀ j : Fin n,
      (fun i ↦ P i j) ∈ localDualPadicDenominator L 2 (r + 1) := by
    intro j
    rw [L.localDualPadicDenominator_succ_eq_map_prime_smul 2 r hr]
    refine ⟨fun i ↦ X i j, hX j, ?_⟩
    funext i
    change (2 : ℤ_[2]) * X i j = P i j
    rw [show P = (2 : ℤ_[2]) • X by
      rw [smul_eq_diagonal_mul]
      rfl]
    rfl
  intro j
  rw [cayleyRingForwardMatrix_sub_one X hsource]
  have hsum :
      (∑ l : Fin n, B l j • (fun i ↦ P i l)) ∈
        localDualPadicDenominator L 2 (r + 1) :=
    (localDualPadicDenominator L 2 (r + 1)).sum_mem fun l _ ↦
      (localDualPadicDenominator L 2 (r + 1)).smul_mem (B l j) (hP l)
  convert hsum using 1
  funext i
  simp [P, B, Matrix.mul_apply, Pi.smul_apply, mul_comm]

/-- Every form-adapted coordinate in the ball at depth `k - 2` has an
integral forward Cayley transform in the shifted dyadic subgroup `H₂`.  The
scaled inverse-Cayley coordinate of the constructed element is exactly twice
the original coordinate. -/
theorem
    exists_densityDyadicDenominatorCongruence_forwardCayley_of_mem_formElementaryUniformCoordinateBall_pred_pred
    (L : PositiveDefiniteIntegralLattice n)
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hX : X ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    ∃ (Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic 2)).toSubmodule)
      (g :
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup),
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom =
          (X : Matrix (Fin n) (Fin n) ℚ_[2]) ∧
      (∀ j : Fin n,
        (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) i j) ∈
          localDualPadicDenominator L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2)) ∧
      (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1 =
        cayleyRingForwardMatrix
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) ∧
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
          g = 2 • X := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let v := padicValInt 2 L.pairingDeterminant
  let r := k - 2
  let e := r - v
  have hdepth : v + 3 ≤ k :=
    L.padicValInt_pairingDeterminant_add_three_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_dyadic
  have hvr : v < r := by omega
  have he : 1 ≤ e := by omega
  have hrHensel : L.IsHenselLatticeDepth 2 r :=
    L.isHenselLatticeDepth_of_pairingDeterminant_val_lt 2 r hvr
  obtain ⟨Xz, hXzmap, hXzcols, hXzdiv⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_denominator_of_mem_formElementaryUniformCoordinateBall
      2 r hvr X (by simpa only [r, k] using hX)
  have hdet :
      (1 + (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).det =
        (1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).det := by
    apply PadicInt.ext
    calc
      ((1 + (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).det : ℚ_[2]) =
          ((1 + (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
            PadicInt.Coe.ringHom).det :=
        PadicInt.Coe.ringHom.map_det _
      _ = (1 + (X : Matrix (Fin n) (Fin n) ℚ_[2])).det := by
        rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
          Matrix.map_one PadicInt.Coe.ringHom
            (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
          hXzmap]
      _ = (1 - (X : Matrix (Fin n) (Fin n) ℚ_[2])).det := by
        apply skewAdjointCayleyRing_det_one_add_eq_det_one_sub
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))
        exact (isUnit_iff_ne_zero).2 (by
          change
            ((algebraMap ℚ ℚ_[2]).mapMatrix
              L.rationalFormMatrix).det ≠ 0
          rw [← RingHom.map_det]
          intro hzero
          apply L.rationalFormMatrix_det_ne_zero
          apply (algebraMap ℚ ℚ_[2]).injective
          simpa using hzero)
      _ = ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
            PadicInt.Coe.ringHom).det := by
        rw [Matrix.map_sub _ (fun a b ↦ map_sub PadicInt.Coe.ringHom a b),
          Matrix.map_one PadicInt.Coe.ringHom
            (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
          hXzmap]
      _ = ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).det : ℚ_[2]) :=
        (PadicInt.Coe.ringHom.map_det _).symm
  obtain ⟨U, hU, _hUreduce, hUmap⟩ :=
    exists_padicInt_cayley_GL_toZModPow_eq_one_of_det_one_add_eq_det_one_sub
      he (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) (by simpa only [e, r, v] using hXzdiv) hdet
  have hsourceZ :
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) ∈ cayleyRingSource :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow
      he (Xz : Matrix (Fin n) (Fin n) ℤ_[2])
        (by simpa only [e, r, v] using hXzdiv)
  have hsourceQ :
      (X : Matrix (Fin n) (Fin n) ℚ_[2]) ∈ cayleyRingSource := by
    have hmap := hsourceZ.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    change IsUnit
      ((1 - (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
        PadicInt.Coe.ringHom) at hmap
    simpa only [Matrix.map_sub _ (fun a b ↦
      map_sub PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
      hXzmap] using hmap
  let xSource : Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix 2 :=
    ⟨X, hsourceQ⟩
  let t :
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix 2 1 :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix 2 L.rationalFormMatrix_det_ne_zero 1 xSource
  let gq :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) := t.1
  let Uq : GL (Fin n) ℚ_[2] :=
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U
  have hUq :
      Uq.1 = cayleyRingForwardMatrix
        (X : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 =
        cayleyRingForwardMatrix (X : Matrix (Fin n) (Fin n) ℚ_[2])
    rw [hUmap, hXzmap]
  have hgq :
      gq.1.1.1 = cayleyRingForwardMatrix
        (X : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    change
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix 2 L.rationalFormMatrix_det_ne_zero 1
          xSource).1.1.1.1 =
        cayleyRingForwardMatrix (X : Matrix (Fin n) (Fin n) ℚ_[2])
    rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
    change
      (1 : Matrix (Fin n) (Fin n) ℚ_[2]) *
          ((1 + (X : Matrix (Fin n) (Fin n) ℚ_[2])) *
            (1 - (X : Matrix (Fin n) (Fin n) ℚ_[2]))⁻¹) = _
    rw [Matrix.one_mul]
    rfl
  have hgqunits : gq.1.1 = Uq := by
    apply Units.ext
    exact hgq.trans hUq.symm
  have hgqint :
      gq ∈ L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup 2 := by
    apply
      (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
        2 gq).2
    constructor
    · intro i j
      rw [hgqunits, Matrix.GeneralLinearGroup.map_apply]
      exact (U.1 i j).property
    · intro i j
      rw [hgqunits, ← map_inv, Matrix.GeneralLinearGroup.map_apply]
      exact ((U⁻¹).1 i j).property
  let gd :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup 2 :=
    ⟨gq, hgqint⟩
  let s : L.localPadicLatticeStabilizerSubgroup 2 :=
    (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
      2 gd).1
  have hsU :
      (L.localPadicLatticeStabilizerIntegralGL 2 s).1 = U.1 := by
    ext i j
    apply PadicInt.ext
    rw [L.localPadicLatticeStabilizerIntegralGL_apply]
    change gq.1.1.1 i j = ((U.1 i j : ℤ_[2]) : ℚ_[2])
    rw [hgqunits, Matrix.GeneralLinearGroup.map_apply]
    rfl
  have hforwardCols : ∀ j : Fin n,
      (fun i ↦
        (cayleyRingForwardMatrix
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) - 1) i j) ∈
        localDualPadicDenominator L 2 (r + 1) :=
    L.cayleyRingForwardMatrix_sub_one_column_mem_localDualPadicDenominator_succ
      r hrHensel (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) hsourceZ hXzcols
  have hsH :
      s ∈
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup := by
    rw [localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup,
      L.mem_localPadicLatticeStabilizerLocalDualDenominatorCongruenceSubgroup_iff]
    intro j
    rw [hsU, hU]
    simpa only [r, k, show (k - 2) + 1 = k - 1 by omega] using hforwardCols j
  let g :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup :=
    ⟨s, hsH⟩
  have hsmap :
      (L.localPadicLatticeStabilizerIntegralGL 2 s).1.map
          PadicInt.Coe.ringHom =
        cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    rw [hsU]
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U).1 = _
    exact hUq
  have hinverse :
      cayleyRingInverseMatrix
          ((L.localPadicLatticeStabilizerIntegralGL 2 s).1.map
            PadicInt.Coe.ringHom) =
        (X : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    rw [hsmap]
    exact cayleyRingInverseMatrix_forward
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[2]) ≠ 0))
      (X : Matrix (Fin n) (Fin n) ℚ_[2]) hsourceQ
  have hscaled :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
          g = 2 • X := by
    apply Subtype.ext
    rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley_eq_two_smul_ringFormula]
    change
      (2 : ℚ_[2]) •
          cayleyRingInverseMatrix
            ((L.localPadicLatticeStabilizerIntegralGL 2 s).1.map
              PadicInt.Coe.ringHom) =
        (2 : ℚ_[2]) • (X : Matrix (Fin n) (Fin n) ℚ_[2])
    rw [hinverse]
  exact ⟨Xz, g, hXzmap, hXzcols, hsU.trans hU, hscaled⟩

/-- The scaled dyadic Cayley residue map covers the complete enlarged
determinant-loss carrier `T₂`.  A target residue is first lifted to an
integral form coordinate in the depth-`k - 1` ball.  Lowering its literal
uniform-coordinate dilation by one level gives a point in the depth-`k - 2`
ball whose scaled forward Cayley residue is the prescribed target. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue := by
  intro t
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let m :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      2
  obtain ⟨Y, hYred⟩ :=
    skewAdjointFormElementaryPadicCoordinateReduction_surjective
      2 m L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero t.1
  have hYred' :
      skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero Y = t.1 := by
    simpa only [m] using hYred
  have hYzero :
      skewAdjointFormElementaryPadicCoordinateReduction
          2 (k - 1) L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero Y = 0 := by
    rw [←
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction_reduction,
      hYred']
    exact t.2
  have hYball : Y.1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2 (k - 1) L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      2 (k - 1) L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero Y).2 hYzero
  rcases hYball with ⟨Z, hZ, hZY⟩
  let X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule :=
    skewAdjointPadicUniformCoordinateDilation
      L.rationalFormMatrix 2 (k - 2) Z
  have hXball : X ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2 (k - 2) L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    ⟨Z, hZ, rfl⟩
  have hk : 2 ≤ k := by
    dsimp [k]
    exact
      L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hlevel : (k - 2) + 1 = k - 1 := by omega
  have htwoX : 2 • X = Y.1 := by
    rw [← hZY]
    simp only [X, skewAdjointPadicUniformCoordinateDilation_apply]
    rw [← hlevel, pow_succ]
    change
      (2 : ℚ_[2]) • ((2 : ℚ_[2]) ^ (k - 2) • Z) =
        ((2 : ℚ_[2]) ^ (k - 2) * 2) • Z
    rw [smul_smul, mul_comm]
  obtain ⟨Xz, g, _hXzmap, _hXzcols, _hgmatrix, hgscaled⟩ :=
    L.exists_densityDyadicDenominatorCongruence_forwardCayley_of_mem_formElementaryUniformCoordinateBall_pred_pred
      X (by simpa only [k] using hXball)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change
    skewAdjointFormElementaryPadicCoordinateReduction
        2 m L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
          g) = t.1
  rw [← hYred]
  congr 1
  apply Subtype.ext
  change
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
        g = Y.1
  exact hgscaled.trans htwoX

end PositiveDefiniteIntegralLattice
