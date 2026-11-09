import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceForwardCayley
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeCayleyAlgebra
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledCayley
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicFormCoordinateMass
import SMSFormula.PadicSpecialOrthogonalDifferentialSignSeparatedDensityDepth

/-!
# Relative Cayley algebra for the shifted dyadic denominator subgroup

For an element of the shifted dyadic denominator-congruence subgroup, the
chosen factorization `G - 1 = 2E` leaves `1 + E` integrally invertible.  This
module defines the integral unscaled coordinate

`U(G) = E * (1 + E)⁻¹`.

Its double is the scaled coordinate, and scalar
extension identifies it with the field-valued inverse-Cayley matrix.
The final theorem descends the exact relative Cayley identity from `ℚ₂` to
`ℤ₂`, keeping every noncommuting factor.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_relative_cayley : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The integral unscaled inverse-Cayley matrix obtained after cancelling the
common dyadic scalar in `G+1 = 2(1+E)`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    Matrix (Fin n) (Fin n) ℤ_[2] :=
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  E * (1 + E)⁻¹

/-- Doubling the unscaled integral coordinate gives the existing scaled
coordinate literally. -/
theorem
    two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (2 : ℤ_[2]) •
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
          g =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        g := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have htwo : (2 : ℤ_[2]) • E = G - 1 := by
    simpa only [E, G] using
      L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  change (2 : ℤ_[2]) • (E * A⁻¹) = (G - 1) * A⁻¹
  rw [← Matrix.smul_mul, htwo]

/-- Every column of the unscaled coordinate lies in the exact shifted
denominator at depth `k-2`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_column_mem_denominator
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    ∀ j : Fin n,
      (fun i ↦
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
          g i j) ∈
        localDualPadicDenominator L 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2) := by
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let B : Matrix (Fin n) (Fin n) ℤ_[2] := (1 + E)⁻¹
  have hE : ∀ j : Fin n, (fun i ↦ E i j) ∈
      localDualPadicDenominator L 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2) :=
    (Classical.choose_spec
      (L.exists_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g)).2.1
  intro j
  change (fun i ↦ (E * B) i j) ∈ _
  have hsum :
      (∑ l : Fin n, B l j • (fun i ↦ E i l)) ∈
        localDualPadicDenominator L 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2) := by
    exact
      (localDualPadicDenominator L 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2)).sum_mem
          fun l _ ↦
            (localDualPadicDenominator L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 2)).smul_mem
                (B l j) (hE l)
  convert hsum using 1
  funext i
  simp [Matrix.mul_apply, Pi.smul_apply, mul_comm]

/-- Scalar extension of the integral unscaled coordinate is the literal
field-valued inverse-Cayley matrix. -/
theorem
    map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_eq_ringFormula
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
        g).map PadicInt.Coe.ringHom =
      cayleyRingInverseMatrix
        ((L.localPadicLatticeStabilizerIntegralGL 2 g.1).1.map
          PadicInt.Coe.ringHom) := by
  let U :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      g
  let S :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
      g
  let C :=
    cayleyRingInverseMatrix
      ((L.localPadicLatticeStabilizerIntegralGL 2 g.1).1.map PadicInt.Coe.ringHom)
  have htwo : (2 : ℤ_[2]) • U = S := by
    simpa only [U, S] using
      L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
        g
  have htwoMap := congrArg (fun M ↦ M.map PadicInt.Coe.ringHom) htwo
  have hscaled : S.map PadicInt.Coe.ringHom = (2 : ℚ_[2]) • C := by
    simpa only [S, C] using
      L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_eq_two_smul_ringFormula
        g
  apply Matrix.ext
  intro i j
  have hij := congr_fun (congr_fun htwoMap i) j
  have hsij := congr_fun (congr_fun hscaled i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij hsij
  apply (mul_left_cancel₀ (show (2 : ℚ_[2]) ≠ 0 by norm_num))
  calc
    2 * (U.map PadicInt.Coe.ringHom) i j =
        (S.map PadicInt.Coe.ringHom) i j := hij
    _ = 2 * C i j := hsij

/-- The unscaled integral coordinate is skew-adjoint for the integral form. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_mem_skewAdjoint
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
        g ∈ skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic 2) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let U :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      g
  let Gq := G.map PadicInt.Coe.ringHom
  let Uq := U.map PadicInt.Coe.ringHom
  have hGunit : IsUnit (Gq + 1) := by
    simpa only [Gq, G] using
      L.isUnit_map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one
        g
  have hformz := L.localPadicLatticeStabilizerIntegralGL_preserves_form 2 g.1
  have hformq :
      Gqᵀ * (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) * Gq =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]) := by
    have hmap := congrArg (fun M ↦ M.map PadicInt.Coe.ringHom) hformz
    simpa only [Gq, G, Matrix.map_mul, Matrix.transpose_map,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField] using hmap
  have hcayley :
      skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))
          (cayleyRingInverseMatrix Gq) = 0 :=
    Matrix.skewAdjointOperator_cayleyRingInverseMatrix_eq_zero_of_formPreserving
      _ Gq hGunit hformq
  have hUq : Uq = cayleyRingInverseMatrix Gq := by
    simpa only [Uq, U, Gq, G] using
      L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_eq_ringFormula
        g
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  apply LinearMap.mem_ker.mpr
  apply Matrix.ext
  intro i j
  apply PadicInt.ext
  have hmap :
      (skewAdjointOperator (L.pairingMatrix_padic 2) U).map
          PadicInt.Coe.ringHom =
        skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) Uq := by
    simp only [skewAdjointOperator_apply]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    rfl
  change
    ((skewAdjointOperator (L.pairingMatrix_padic 2) U).map
      PadicInt.Coe.ringHom) i j = 0
  rw [hmap, hUq, hcayley]
  rfl

/-- The exact relative identity for integral unscaled coordinates.  Its proof
uses the ordinary Cayley identity over `ℚ₂`, where the relative denominator is
invertible, and then descends through the injective map `ℤ₂ → ℚ₂`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceRelativeUnscaledInverseCayley_cross_sub
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    let X :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
        g
    let Y :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
        h
    let R := (L.localPadicLatticeStabilizerIntegralGL 2 (g * h⁻¹).1).1
    let Z :=
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
        (g * h⁻¹)
    (1 - X) * (R + 1) * Z * (1 + Y) =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          g -
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          h := by
  dsimp only
  let G := L.localPadicLatticeStabilizerIntegralGL 2 g.1
  let H := L.localPadicLatticeStabilizerIntegralGL 2 h.1
  let R := L.localPadicLatticeStabilizerIntegralGL 2 (g * h⁻¹).1
  let Hq := Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom H
  let X :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      g
  let Y :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      h
  let Z :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      (g * h⁻¹)
  let Xq := X.map PadicInt.Coe.ringHom
  let Yq := Y.map PadicInt.Coe.ringHom
  let Zq := Z.map PadicInt.Coe.ringHom
  let Gq := G.1.map PadicInt.Coe.ringHom
  let Rq := R.1.map PadicInt.Coe.ringHom
  have hXmap : X.map PadicInt.Coe.ringHom = Xq := rfl
  have hYmap : Y.map PadicInt.Coe.ringHom = Yq := rfl
  have hZmap : Z.map PadicInt.Coe.ringHom = Zq := rfl
  have hRmap : R.1.map PadicInt.Coe.ringHom = Rq := rfl
  have htwoUnit : IsUnit (2 : ℚ_[2]) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hGdomain : Gq ∈ Matrix.cayleyRingInverseDomain := by
    simpa only [Gq, G] using
      L.isUnit_map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one
        g
  have hHdomain : Hq.1 ∈ Matrix.cayleyRingInverseDomain := by
    change IsUnit (H.1.map PadicInt.Coe.ringHom + 1)
    simpa only [H] using
      L.isUnit_map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one
        h
  have hRdomain : Rq ∈ Matrix.cayleyRingInverseDomain := by
    simpa only [Rq, R] using
      L.isUnit_map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one
        (g * h⁻¹)
  have hXeq : Xq = Matrix.cayleyRingInverseMatrix Gq := by
    simpa only [Xq, X, Gq, G] using
      L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_eq_ringFormula
        g
  have hYeq : Yq = Matrix.cayleyRingInverseMatrix Hq.1 := by
    change Y.map PadicInt.Coe.ringHom = Matrix.cayleyRingInverseMatrix
      (H.1.map PadicInt.Coe.ringHom)
    simpa only [Y, H] using
      L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_eq_ringFormula
        h
  have hZeq : Zq = Matrix.cayleyRingInverseMatrix Rq := by
    simpa only [Zq, Z, Rq, R] using
      L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix_eq_ringFormula
        (g * h⁻¹)
  have hXsource : Xq ∈ Matrix.cayleyRingSource := by
    rw [hXeq]
    exact Matrix.cayleyRingInverseMatrix_mem_source htwoUnit Gq hGdomain
  have hYsource : Yq ∈ Matrix.cayleyRingSource := by
    rw [hYeq]
    exact Matrix.cayleyRingInverseMatrix_mem_source htwoUnit Hq.1 hHdomain
  have hGforward : Matrix.cayleyRingForwardMatrix Xq = Gq := by
    rw [hXeq]
    exact Matrix.cayleyRingForwardMatrix_inverse htwoUnit Gq hGdomain
  have hHforward : Hq.1 = Matrix.cayleyRingForwardMatrix Yq := by
    rw [hYeq]
    exact (Matrix.cayleyRingForwardMatrix_inverse htwoUnit Hq.1 hHdomain).symm
  have hHinv :
      L.localPadicLatticeStabilizerIntegralGL 2 h.1⁻¹ = H⁻¹ := by
    simpa only [H] using
      (L.localPadicLatticeStabilizerIntegralGLHom 2).map_inv h.1
  have hRmatrix : R.1 = G.1 * (H⁻¹).1 := by
    calc
      R.1 = (G * (L.localPadicLatticeStabilizerIntegralGL 2 h.1⁻¹)).1 := by
        exact congrArg Units.val
          ((L.localPadicLatticeStabilizerIntegralGLHom 2).map_mul g.1 h.1⁻¹)
      _ = (G * H⁻¹).1 := by rw [hHinv]
      _ = G.1 * (H⁻¹).1 := rfl
  have hmapinv :
      Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom (H⁻¹) = Hq⁻¹ := by
    simpa only [Hq] using
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom).map_inv H
  have hmapinvVal :
      (H⁻¹).1.map PadicInt.Coe.ringHom = (Hq⁻¹).1 := by
    exact congrArg Units.val hmapinv
  have hRqmatrix : Rq = Gq * (Hq⁻¹).1 := by
    have hm := congrArg (fun M ↦ M.map PadicInt.Coe.ringHom) hRmatrix
    calc
      Rq = (G.1 * (H⁻¹).1).map PadicInt.Coe.ringHom := hm
      _ = Gq * ((H⁻¹).1.map PadicInt.Coe.ringHom) := by
        rw [Matrix.map_mul]
      _ = Gq * (Hq⁻¹).1 := by rw [hmapinvVal]
  have hmain :=
    Matrix.cayleyRingRelativeInverse_cross_sub
      Xq Yq hXsource hYsource Hq hHforward (by
        rw [hGforward, ← hRqmatrix]
        exact hRdomain)
  rw [hGforward, ← hRqmatrix, ← hZeq] at hmain
  have hmainTwo :
      (1 - Xq) * (Rq + 1) * Zq * (1 + Yq) =
        (2 : ℚ_[2]) • (Xq - Yq) := by
    calc
      (1 - Xq) * (Rq + 1) * Zq * (1 + Yq) =
          (@Matrix.cayleyRingTwoMatrix (Fin n) ℚ_[2] _ _ _) * (Xq - Yq) :=
        hmain
      _ = (2 : ℚ_[2]) • (Xq - Yq) := by
        rw [smul_eq_diagonal_mul]
        rfl
  have hintegral :
      (1 - X) * (R.1 + 1) * Z * (1 + Y) =
        (2 : ℤ_[2]) • (X - Y) := by
    have hleft :
        ((1 - X) * (R.1 + 1) * Z * (1 + Y)).map PadicInt.Coe.ringHom =
          (1 - Xq) * (Rq + 1) * Zq * (1 + Yq) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
        Matrix.map_sub _ (fun a b ↦ map_sub PadicInt.Coe.ringHom a b),
        Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
        Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
        Matrix.map_one PadicInt.Coe.ringHom
          (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
        hXmap, hYmap, hZmap, hRmap]
    have hright :
        ((2 : ℤ_[2]) • (X - Y)).map PadicInt.Coe.ringHom =
          (2 : ℚ_[2]) • (Xq - Yq) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul]
      rfl
    exact Matrix.map_injective (f := PadicInt.Coe.ringHom) (by
      intro a b hab
      exact PadicInt.ext hab) (hleft.trans (hmainTwo.trans hright.symm))
  calc
    (1 - X) * (R.1 + 1) * Z * (1 + Y) =
        (2 : ℤ_[2]) • (X - Y) := hintegral
    _ = (2 : ℤ_[2]) • X - (2 : ℤ_[2]) • Y := by rw [smul_sub]
    _ =
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            g -
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            h := by
      rw [L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
          g,
        L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
          h]

end PositiveDefiniteIntegralLattice
