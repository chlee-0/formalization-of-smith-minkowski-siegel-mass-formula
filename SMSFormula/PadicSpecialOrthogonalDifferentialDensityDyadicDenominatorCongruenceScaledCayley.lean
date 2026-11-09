import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceCayleyDepth
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDeterminantLossResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceCayleyBoundary

/-!
# Scaled Cayley coordinates for the shifted dyadic denominator subgroup

For `g : H₂`, write `G - 1 = 2E` with `1 + E` an integral matrix unit.  The
unscaled inverse-Cayley coordinate loses one denominator level.  The scaled
coordinate

`(G - 1) * (1 + E)⁻¹ = 2 * inverseCayley(G)`

retains the full shifted local-dual denominator at depth `k - 1`.  This module
packages that coordinate, proves its exact scalar-extension and skew-adjoint
properties, and reduces it into the enlarged dyadic determinant-loss carrier.

No assertion is made here about the image of the principal kernel, additive
closure of attained residues, a quotient equivalence, or the dyadic gauge
value.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_scaled_cayley : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The chosen integral half-difference `E` in `G - 1 = 2E`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    Matrix (Fin n) (Fin n) ℤ_[2] :=
  Classical.choose
    (L.exists_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
      g)

/-- The chosen half-difference recovers the complete integral matrix
difference after multiplication by two. -/
theorem
    two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (2 : ℤ_[2]) •
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g =
      (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1 - 1 :=
  (Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
      g)).1

/-- The residual dyadic denominator `1 + E` is an integral matrix unit. -/
theorem
    isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    IsUnit
      (1 +
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g) :=
  (Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
      g)).2.2

/-- The integral matrix representing twice the field-valued inverse-Cayley
coordinate.  The difference is placed on the left so its denominator columns
are preserved under right multiplication. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    Matrix (Fin n) (Fin n) ℤ_[2] :=
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  (G - 1) * (1 + E)⁻¹

/-- Every column of the scaled integral coordinate remains in the shifted
local-dual denominator at depth `k - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_column_mem_denominator
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    ∀ j : Fin n,
      (fun i ↦
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          g i j) ∈
        localDualPadicDenominator L 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let D : Matrix (Fin n) (Fin n) ℤ_[2] := G - 1
  let B : Matrix (Fin n) (Fin n) ℤ_[2] := (1 + E)⁻¹
  have hD : ∀ j : Fin n, (fun i ↦ D i j) ∈
      localDualPadicDenominator L 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) := by
    intro j
    simpa only [D, G, Matrix.sub_apply] using g.2 j
  intro j
  change (fun i ↦ (D * B) i j) ∈ _
  have hsum :
      (∑ l : Fin n, B l j • (fun i ↦ D i l)) ∈
        localDualPadicDenominator L 2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1) := by
    exact
      (localDualPadicDenominator L 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)).sum_mem
          fun l _ ↦
            (localDualPadicDenominator L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)).smul_mem
                (B l j) (hD l)
  convert hsum using 1
  funext i
  simp [Matrix.mul_apply, Pi.smul_apply, mul_comm]

/-- Scalar extension of the scaled integral coordinate is twice
the field-valued inverse-Cayley matrix of the stabilizer element. -/
theorem
    map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_eq_two_smul_ringFormula
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        g).map PadicInt.Coe.ringHom =
      (2 : ℚ_[2]) •
        cayleyRingInverseMatrix
          ((L.localPadicLatticeStabilizerIntegralGL 2 g.1).1.map
            PadicInt.Coe.ringHom) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have hA : IsUnit A := by
    simpa only [A, E] using
      L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have htwo : (2 : ℤ_[2]) • E = G - 1 := by
    simpa only [E, G] using
      L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have hGadd : G + 1 = (2 : ℤ_[2]) • A := by
    ext i j
    have hij := congr_fun (congr_fun htwo i) j
    simp only [A, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] at hij ⊢
    simp only [smul_eq_mul] at hij ⊢
    calc
      G i j + (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j =
          (G i j - (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j) +
            2 * (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by ring
      _ = 2 * E i j +
            2 * (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by rw [← hij]
      _ = 2 * ((1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j + E i j) := by ring
  have hAinvmap :
      A⁻¹.map PadicInt.Coe.ringHom =
        (A.map PadicInt.Coe.ringHom)⁻¹ := by
    rw [show A⁻¹ = (hA.unit⁻¹).1 by
      rw [Matrix.coe_units_inv, hA.unit_spec]]
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom hA.unit⁻¹).1 =
        (A.map PadicInt.Coe.ringHom)⁻¹
    rw [map_inv, Matrix.coe_units_inv]
    congr 1
  have hAmap :
      (2 : ℚ_[2]) • A.map PadicInt.Coe.ringHom =
        G.map PadicInt.Coe.ringHom + 1 := by
    have := congrArg (fun M ↦ M.map PadicInt.Coe.ringHom) hGadd
    simpa only [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
      Matrix.map_smul] using this.symm
  have hGunit : IsUnit (G.map PadicInt.Coe.ringHom + 1) := by
    rw [← hAmap]
    have htwoUnit : IsUnit (2 : ℚ_[2]) :=
      isUnit_iff_ne_zero.mpr (by norm_num)
    have hAmapUnit : IsUnit (A.map PadicInt.Coe.ringHom) :=
      hA.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
    rw [show (2 : ℚ_[2]) • A.map PadicInt.Coe.ringHom =
        Matrix.scalar (Fin n) (2 : ℚ_[2]) * A.map PadicInt.Coe.ringHom by
      ext i j
      rw [Matrix.scalar_apply, Matrix.diagonal_mul]
      rfl]
    exact (htwoUnit.map (Matrix.scalar (Fin n))).mul hAmapUnit
  change ((G - 1) * A⁻¹).map PadicInt.Coe.ringHom = _
  rw [Matrix.map_mul, hAinvmap,
    Matrix.map_sub _ (fun a b ↦ map_sub PadicInt.Coe.ringHom a b),
    Matrix.map_one PadicInt.Coe.ringHom
      (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom)]
  apply hGunit.mul_right_cancel
  have hAdet : IsUnit (A.map PadicInt.Coe.ringHom).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (hA.map (RingHom.mapMatrix PadicInt.Coe.ringHom))
  have hGdet : IsUnit (G.map PadicInt.Coe.ringHom + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hGunit
  calc
    ((G.map PadicInt.Coe.ringHom - 1) *
          (A.map PadicInt.Coe.ringHom)⁻¹) *
        (G.map PadicInt.Coe.ringHom + 1) =
      ((G.map PadicInt.Coe.ringHom - 1) *
          (A.map PadicInt.Coe.ringHom)⁻¹) *
        ((2 : ℚ_[2]) • A.map PadicInt.Coe.ringHom) := by rw [hAmap]
    _ = (2 : ℚ_[2]) • (G.map PadicInt.Coe.ringHom - 1) := by
      rw [Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.nonsing_inv_mul _ hAdet, Matrix.mul_one]
    _ = ((2 : ℚ_[2]) •
          cayleyRingInverseMatrix (G.map PadicInt.Coe.ringHom)) *
        (G.map PadicInt.Coe.ringHom + 1) := by
      rw [Matrix.smul_mul,
        Matrix.cayleyRingInverseMatrix_eq_sub_mul_nonsing_inv _ hGunit,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGdet, Matrix.mul_one]

/-- The field-valued denominator `G + 1` is invertible after the certified
common scalar two is allowed to become a unit. -/
theorem
    isUnit_map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    IsUnit
      ((L.localPadicLatticeStabilizerIntegralGL 2 g.1).1.map
          PadicInt.Coe.ringHom + 1) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have hA : IsUnit A := by
    simpa only [A, E] using
      L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have htwo : (2 : ℤ_[2]) • E = G - 1 := by
    simpa only [E, G] using
      L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have hGadd : G + 1 = (2 : ℤ_[2]) • A := by
    ext i j
    have hij := congr_fun (congr_fun htwo i) j
    simp only [A, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] at hij ⊢
    simp only [smul_eq_mul] at hij ⊢
    calc
      G i j + (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j =
          (G i j - (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j) +
            2 * (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by ring
      _ = 2 * E i j +
            2 * (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by rw [← hij]
      _ = 2 * ((1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j + E i j) := by ring
  have hmap := congrArg (fun M ↦ M.map PadicInt.Coe.ringHom) hGadd
  have hformula :
      G.map PadicInt.Coe.ringHom + 1 =
        (2 : ℚ_[2]) • A.map PadicInt.Coe.ringHom := by
    simpa only [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_one PadicInt.Coe.ringHom
        (map_zero PadicInt.Coe.ringHom) (map_one PadicInt.Coe.ringHom),
      Matrix.map_smul] using hmap
  rw [hformula]
  have htwoUnit : IsUnit (2 : ℚ_[2]) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hAmapUnit : IsUnit (A.map PadicInt.Coe.ringHom) :=
    hA.map (RingHom.mapMatrix PadicInt.Coe.ringHom)
  rw [show (2 : ℚ_[2]) • A.map PadicInt.Coe.ringHom =
      Matrix.scalar (Fin n) (2 : ℚ_[2]) * A.map PadicInt.Coe.ringHom by
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_mul]
    rfl]
  exact (htwoUnit.map (Matrix.scalar (Fin n))).mul hAmapUnit

/-- The scaled integral Cayley matrix is skew-adjoint for the integral form. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_mem_skewAdjoint
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        g ∈
      skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic 2) := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let Xz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
      g
  let Gq := G.map PadicInt.Coe.ringHom
  let Xq := Xz.map PadicInt.Coe.ringHom
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
  have hscaled :
      skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) Xq = 0 := by
    have hXq : Xq = (2 : ℚ_[2]) • cayleyRingInverseMatrix Gq := by
      simpa only [Xq, Xz, Gq, G] using
        L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_eq_two_smul_ringFormula
          g
    rw [hXq, LinearMap.map_smul, hcayley, smul_zero]
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  apply LinearMap.mem_ker.mpr
  apply Matrix.ext
  intro i j
  apply PadicInt.ext
  have hmap :
      (skewAdjointOperator (L.pairingMatrix_padic 2) Xz).map
          PadicInt.Coe.ringHom =
        skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) Xq := by
    simp only [skewAdjointOperator_apply]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    rfl
  change
    ((skewAdjointOperator (L.pairingMatrix_padic 2) Xz).map
      PadicInt.Coe.ringHom) i j = 0
  rw [hmap, hscaled]
  rfl

/-- The scaled integral coordinate as an integral skew-adjoint point. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic 2)).toSubmodule :=
  ⟨L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
      g,
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_mem_skewAdjoint
      g⟩

@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
        g : Matrix (Fin n) (Fin n) ℤ_[2]) =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        g :=
  rfl

/-- Scalar extension of the scaled integral coordinate to the rational dyadic
form-coordinate space. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (skewAdjointMatricesLieSubalgebra
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule := by
  let Xz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
      g
  let Xq : Matrix (Fin n) (Fin n) ℚ_[2] :=
    (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom
  refine ⟨Xq, ?_⟩
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  apply LinearMap.mem_ker.mpr
  have hXz : skewAdjointOperator (L.pairingMatrix_padic 2)
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) = 0 :=
    LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff _ _).mpr Xz.property)
  have hmap :
      (skewAdjointOperator (L.pairingMatrix_padic 2)
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map PadicInt.Coe.ringHom =
        skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) Xq := by
    simp only [skewAdjointOperator_apply]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    rfl
  rw [← hmap, hXz]
  simp

/-- The rational scaled coordinate is literally twice the original
field-valued inverse-Cayley expression.  In particular, any later comparison
with the original attained residue must retain this factor two. -/
theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley_eq_two_smul_ringFormula
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
        g : Matrix (Fin n) (Fin n) ℚ_[2]) =
      (2 : ℚ_[2]) •
        cayleyRingInverseMatrix
          ((L.localPadicLatticeStabilizerIntegralGL 2 g.1).1.map
            PadicInt.Coe.ringHom) := by
  change
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        g).map PadicInt.Coe.ringHom = _
  exact
    L.map_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_eq_two_smul_ringFormula
      g

/-- The scaled rational coordinate lies in the certified outer
form-coordinate ball at depth `k - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley_mem_formElementaryUniformCoordinateBall_pred
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
        g ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
  apply
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero _).2
  intro q
  let Xz :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
      g
  have hcol :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_column_mem_denominator
      g q.1.2
  have hdiv :=
    (L.mem_localDualPadicDenominator_iff_forall_padic
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) i q.1.2)).1
      hcol ((Pi.basisFun ℤ_[2] (Fin n)) q.1.1)
  have hdot :
      dotProduct ((Pi.basisFun ℤ_[2] (Fin n)) q.1.1)
          ((L.pairingMatrix_padic 2).mulVec
            (fun i ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) i q.1.2)) =
        (L.pairingMatrix_padic 2 *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2 := by
    rw [dotProduct]
    calc
      (∑ i,
          ((Pi.basisFun ℤ_[2] (Fin n)) q.1.1) i *
            (L.pairingMatrix_padic 2).mulVec
              (fun a ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) a q.1.2) i) =
          ((Pi.basisFun ℤ_[2] (Fin n)) q.1.1) q.1.1 *
            (L.pairingMatrix_padic 2).mulVec
              (fun a ↦ (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) a q.1.2) q.1.1 := by
        exact Finset.sum_eq_single q.1.1
          (by
            intro i _ hi
            simp [Pi.basisFun, hi])
          (by simp)
      _ = (L.pairingMatrix_padic 2 *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2 := by
        simp [Pi.basisFun, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [hdot] at hdiv
  have hmem :
      (L.pairingMatrix_padic 2 *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2 ∈
        (Ideal.span
          {(2 : ℤ_[2]) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)} :
          Ideal ℤ_[2]) :=
    (Ideal.mem_span_singleton).2 hdiv
  have hnorm :=
    (PadicInt.norm_le_pow_iff_mem_span_pow
      ((L.pairingMatrix_padic 2 *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2)
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)).2
      hmem
  have hmap :
      ((L.pairingMatrix_padic 2 *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map PadicInt.Coe.ringHom) =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]) *
          (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
            g : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    rw [Matrix.map_mul]
    have hFmap :
        (L.pairingMatrix_padic 2).map PadicInt.Coe.ringHom =
          L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]) :=
      (L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField 2).symm
    calc
      (L.pairingMatrix_padic 2).map PadicInt.Coe.ringHom *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom =
        L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]) *
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom := by
            rw [hFmap]
      _ = L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]) *
          (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
            g : Matrix (Fin n) (Fin n) ℚ_[2]) := rfl
  rw [← hmap]
  change
    ‖(((L.pairingMatrix_padic 2 *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2 : ℤ_[2]) : ℚ_[2])‖ ≤
      ‖(2 : ℚ_[2]) ^
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)‖
  rw [show
    ‖(((L.pairingMatrix_padic 2 *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2 : ℤ_[2]) : ℚ_[2])‖ =
      ‖(L.pairingMatrix_padic 2 *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2‖ from rfl]
  calc
    ‖(L.pairingMatrix_padic 2 *
        (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) q.1.1 q.1.2‖ ≤
        (2 : ℝ) ^
          (-((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1 : ℕ) : ℤ)) :=
      hnorm
    _ = ‖(2 : ℚ_[2]) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)‖ := by
      rw [norm_pow, Matrix.norm_two_dyadic]
      simp [inv_pow]

/-- The scaled coordinate as a point of the integral form-coordinate
lattice. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      2 L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero := by
  refine
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley
      g, ?_⟩
  apply
    skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley_mem_formElementaryUniformCoordinateBall_pred
      g

/-- The scaled Cayley coordinate reduced at the original dyadic attained
residue level. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    skewAdjointFormElementaryPadicCoordinateResidue
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel 2)
      L.rationalFormMatrix :=
  skewAdjointFormElementaryPadicCoordinateReduction
    2
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel 2)
    L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
      g)

/-- The scaled residue restricts to zero at the certified dyadic outer depth
`k - 1`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue_restrictsToZero
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue
          g) = 0 := by
  unfold
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue
  rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossRestriction_reduction]
  apply
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero _).1
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayley_mem_formElementaryUniformCoordinateBall_pred
      g

/-- The literal scaled Cayley residue map from `H₂` into the enlarged dyadic
determinant-loss carrier `T₂`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup →
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
  fun g ↦
    ⟨L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue
        g,
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue_restrictsToZero
        g⟩

@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
        g).1 =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinateResidue
        g :=
  rfl

end PositiveDefiniteIntegralLattice
