import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceRelativeCayley
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeResidue

/-!
# Integral unit factors in the shifted dyadic relative Cayley identity

For `G - 1 = 2E`, put `A = 1 + E`.  The unscaled integral coordinate is
`U = E A⁻¹`.  This module proves the literal unit identities

`1-U = A⁻¹`,  `1+U = G A⁻¹`,  `G+1 = 2A`.

They rewrite the completed relative Cayley identity as a left/right integral
unit translate of the relative scaled coordinate.  Consequently entrywise
membership in every ideal is preserved and reflected.  At the selected depth
this gives an exact criterion for the relative principal kernel in terms of
the difference of the two absolute scaled coordinates.

No form-coordinate residue action, attained-image closure, quotient,
cardinality, or gauge value is asserted.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_relative_factor : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The residual integral unit `A(g)=1+E(g)` after cancelling the common
dyadic scalar from `G+1`. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    GL (Fin n) ℤ_[2] :=
  (L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
    g).unit

/-- The matrix of the residual unit is `1+E`. -/
@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
        g).1 =
      1 +
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
          g :=
  (L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
    g).unit_spec

/-- The lower Cayley denominator is the inverse residual unit. -/
theorem
    one_sub_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    1 -
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
          g =
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
          g)⁻¹.1 := by
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have hA : IsUnit A := by
    simpa only [A, E] using
      L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hunit :
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
          g)⁻¹.1 = A⁻¹ := by
    rw [Matrix.coe_units_inv]
    congr 1
  change 1 - E * A⁻¹ = _
  rw [hunit]
  apply hA.mul_right_cancel
  rw [sub_mul, one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul A hAdet, Matrix.mul_one]
  dsimp only [A]
  noncomm_ring

/-- The upper Cayley numerator is the stabilizer matrix times the inverse
residual unit. -/
theorem
    one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    1 +
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
          g =
      (L.localPadicLatticeStabilizerIntegralGL 2 g.1 *
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
          g)⁻¹).1 := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have hA : IsUnit A := by
    simpa only [A, E] using
      L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have htwo : (2 : ℤ_[2]) • E = G - 1 := by
    simpa only [E, G] using
      L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have hunit :
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
          g)⁻¹.1 = A⁻¹ := by
    rw [Matrix.coe_units_inv]
    congr 1
  change 1 + E * A⁻¹ = G * _
  rw [hunit]
  apply hA.mul_right_cancel
  rw [add_mul, one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul A hAdet, Matrix.mul_one]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAdet, Matrix.mul_one]
  apply Matrix.ext
  intro i j
  have hij := congr_fun (congr_fun htwo i) j
  simp only [A, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul] at hij ⊢
  calc
    (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j + E i j + E i j =
        (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j + 2 * E i j := by ring
    _ = G i j := by rw [hij]; ring

/-- The full dyadic inverse-Cayley denominator has the exact common scalar
two and residual unit `A`. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one_eq_two_smul_residualUnit
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1 + 1 =
      (2 : ℤ_[2]) •
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
          g).1 := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  have htwo : (2 : ℤ_[2]) • E = G - 1 := by
    simpa only [E, G] using
      L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit]
  apply Matrix.ext
  intro i j
  have hij := congr_fun (congr_fun htwo i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul] at hij ⊢
  calc
    G i j + (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j =
        (G i j - (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j) +
          2 * (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by ring
    _ = 2 * E i j +
          2 * (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j := by rw [← hij]
    _ = 2 * ((1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j + E i j) := by ring

/-- Multiplying the scaled coordinate by its residual unit recovers the
complete matrix difference from one. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_mul_residualUnit
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          g *
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
          g).1 =
      (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1 - 1 := by
  let G := (L.localPadicLatticeStabilizerIntegralGL 2 g.1).1
  let E :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference g
  let A : Matrix (Fin n) (Fin n) ℤ_[2] := 1 + E
  have hA : IsUnit A := by
    simpa only [A, E] using
      L.isUnit_one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceHalfDifference
        g
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  change ((G - 1) * A⁻¹) * A = G - 1
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAdet, Matrix.mul_one]

/-- The relative scaled-coordinate difference is a literal left/right unit
translate of the scaled coordinate of the relative stabilizer. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_sub_eq_relative_unit_mul
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    let r := g * h⁻¹
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          g -
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          h =
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            g)⁻¹.1 *
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            r).1 *
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          r *
        (L.localPadicLatticeStabilizerIntegralGL 2 h.1 *
          (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            h)⁻¹).1 := by
  dsimp only
  let r := g * h⁻¹
  let X :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      g
  let Y :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      h
  let Z :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      r
  let R := (L.localPadicLatticeStabilizerIntegralGL 2 r.1).1
  have hrelative :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceRelativeUnscaledInverseCayley_cross_sub
      g h
  change (1 - X) * (R + 1) * Z * (1 + Y) = _ at hrelative
  rw [L.one_sub_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      g,
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceIntegralGL_add_one_eq_two_smul_residualUnit
      r,
    L.one_add_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      h] at hrelative
  have hmiddle :
      (2 : ℤ_[2]) •
          (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            r).1 * Z =
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            r).1 *
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            r := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul]
    rw [L.two_smul_localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceUnscaledInverseCayleyMatrix
      r]
  calc
    _ =
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            g)⁻¹.1 *
          (((2 : ℤ_[2]) •
              (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
                r).1) * Z) *
          (L.localPadicLatticeStabilizerIntegralGL 2 h.1 *
            (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
              h)⁻¹).1 := by simpa only [Matrix.mul_assoc] using hrelative.symm
    _ = _ := by rw [hmiddle]; simp only [Matrix.mul_assoc, r]

/-- Left/right relative Cayley factors preserve and reflect entrywise
membership in every ideal. -/
theorem
    entriesMemIdeal_scaledInverseCayley_sub_iff_relative
    (L : PositiveDefiniteIntegralLattice n)
    (I : Ideal ℤ_[2])
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    Matrix.entriesMemIdeal I
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            g -
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            h) ↔
      Matrix.entriesMemIdeal I
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          (g * h⁻¹)) := by
  rw [L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_sub_eq_relative_unit_mul]
  change Matrix.entriesMemIdeal I
      (((L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            g)⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            (g * h⁻¹)).1 *
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          (g * h⁻¹) *
        (L.localPadicLatticeStabilizerIntegralGL 2 h.1 *
          (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
            h)⁻¹).1) ↔ _
  rw [Matrix.entriesMemIdeal_mul_unit_iff,
    Matrix.entriesMemIdeal_unit_mul_iff]

/-- At the complete selected depth, relative principal-kernel membership is
exactly entrywise divisibility of the difference of the two absolute scaled
Cayley coordinates. -/
theorem
    mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledInverseCayley_sub_entriesMemIdeal
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence ↔
      Matrix.entriesMemIdeal
        (Ideal.span
          {(2 : ℤ_[2]) ^
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2})
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            g -
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
            h) := by
  let r := g * h⁻¹
  let I : Ideal ℤ_[2] :=
    Ideal.span
      {(2 : ℤ_[2]) ^
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2}
  rw [L.entriesMemIdeal_scaledInverseCayley_sub_iff_relative I g h]
  rw [L.mem_localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence_iff]
  rw [L.mem_localPadicPrincipalCongruenceSubgroup_iff_entriesMemIdeal_sub_one]
  change Matrix.entriesMemIdeal I
      ((L.localPadicLatticeStabilizerIntegralGL 2 r.1).1 - 1) ↔
    Matrix.entriesMemIdeal I
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        r)
  rw [←
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix_mul_residualUnit
      r]
  exact
    Matrix.entriesMemIdeal_mul_unit_iff I
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
        r)
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceResidualUnit
        r)

end PositiveDefiniteIntegralLattice
