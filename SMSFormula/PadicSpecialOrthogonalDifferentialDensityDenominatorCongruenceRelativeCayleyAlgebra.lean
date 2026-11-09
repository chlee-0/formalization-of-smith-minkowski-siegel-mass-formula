import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceForwardCayley
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidue
import SMSFormula.PadicCayleyTranslatedChartOverlapAlgebra

/-!
# Relative Cayley algebra for the denominator-congruence chart

This module clears the noncommuting denominators in the difference of two
forward Cayley transforms.  It then combines that identity with the inverse
Cayley equation for a relative group element.  The final specialization is an
exact integral identity for two odd-prime elements of `H_k`.

No finite residue relation, quotient equivalence, cardinality, or gauge value
is asserted.
-/

noncomputable section

open scoped Matrix

namespace Matrix

set_option maxHeartbeats 3000000

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Right multiplication by the Cayley denominator clears the forward
fraction. -/
theorem cayleyRingForwardMatrix_mul_one_sub
    (X : Matrix ι ι R) (hX : X ∈ cayleyRingSource) :
    cayleyRingForwardMatrix X * (1 - X) = 1 + X := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hX
  change (B * A⁻¹) * A = B
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAdet, Matrix.mul_one]

/-- Left multiplication by the Cayley denominator also clears the forward
fraction; the numerator and denominator commute because both are polynomials
in the same matrix. -/
theorem one_sub_mul_cayleyRingForwardMatrix
    (X : Matrix ι ι R) (hX : X ∈ cayleyRingSource) :
    (1 - X) * cayleyRingForwardMatrix X = 1 + X := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hAB : A * B = B * A := by
    dsimp [A, B]
    noncomm_ring
  change A * (B * A⁻¹) = B
  rw [← Matrix.mul_assoc, hAB, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv A hAdet, Matrix.mul_one]

/-- The exact noncommutative difference identity for two forward Cayley
transforms.  Both denominators are retained on their natural sides. -/
theorem cayleyRingForwardMatrix_sub_cross
    (X Y : Matrix ι ι R)
    (hX : X ∈ cayleyRingSource) (hY : Y ∈ cayleyRingSource) :
    (1 - X) * (cayleyRingForwardMatrix X - cayleyRingForwardMatrix Y) *
        (1 - Y) =
      cayleyRingTwoMatrix * (X - Y) := by
  calc
    (1 - X) * (cayleyRingForwardMatrix X - cayleyRingForwardMatrix Y) *
          (1 - Y) =
        ((1 - X) * cayleyRingForwardMatrix X) * (1 - Y) -
          (1 - X) * (cayleyRingForwardMatrix Y * (1 - Y)) := by
            noncomm_ring
    _ = (1 + X) * (1 - Y) - (1 - X) * (1 + Y) := by
      rw [one_sub_mul_cayleyRingForwardMatrix X hX,
        cayleyRingForwardMatrix_mul_one_sub Y hY]
    _ = (X - Y) + (X - Y) := by noncomm_ring
    _ = (2 : R) • (X - Y) := (two_smul R (X - Y)).symm
    _ = cayleyRingTwoMatrix * (X - Y) := by
      rw [smul_eq_diagonal_mul]
      rfl

/-- Clearing the relative inverse-Cayley equation against an actual matrix
unit gives the literal difference of the two target matrices. -/
theorem cayleyRingInverseMatrix_mul_unit_inv_cross_sub
    (G : Matrix ι ι R) (H : GL ι R)
    (hR : G * (H⁻¹).1 ∈ cayleyRingInverseDomain) :
    ((G * (H⁻¹).1 + 1) *
          cayleyRingInverseMatrix (G * (H⁻¹).1)) * H.1 =
      G - H.1 := by
  have hcross :=
    cayleyRingInverseMatrix_cross (G * (H⁻¹).1) hR
  have hinv_mul : (H⁻¹).1 * H.1 = 1 := H.inv_val
  calc
    ((G * (H⁻¹).1 + 1) *
          cayleyRingInverseMatrix (G * (H⁻¹).1)) * H.1 =
        (G * (H⁻¹).1 - 1) * H.1 := by rw [hcross]
    _ = G - H.1 := by
      rw [sub_mul, one_mul, Matrix.mul_assoc, hinv_mul, Matrix.mul_one]

/-- The combined absolute/relative Cayley identity.  It relates the inverse
Cayley coordinate of `cayley(X) * cayley(Y)⁻¹` directly to `X-Y`, while
retaining every noncommuting unit factor. -/
theorem cayleyRingRelativeInverse_cross_sub
    (X Y : Matrix ι ι R)
    (hX : X ∈ cayleyRingSource) (hY : Y ∈ cayleyRingSource)
    (H : GL ι R) (hH : H.1 = cayleyRingForwardMatrix Y)
    (hR : cayleyRingForwardMatrix X * (H⁻¹).1 ∈ cayleyRingInverseDomain) :
    (1 - X) *
          (cayleyRingForwardMatrix X * (H⁻¹).1 + 1) *
          cayleyRingInverseMatrix
            (cayleyRingForwardMatrix X * (H⁻¹).1) *
          (1 + Y) =
      cayleyRingTwoMatrix * (X - Y) := by
  have hrelative :=
    cayleyRingInverseMatrix_mul_unit_inv_cross_sub
      (cayleyRingForwardMatrix X) H hR
  calc
    (1 - X) *
          (cayleyRingForwardMatrix X * (H⁻¹).1 + 1) *
          cayleyRingInverseMatrix
            (cayleyRingForwardMatrix X * (H⁻¹).1) *
          (1 + Y) =
        (1 - X) *
          ((cayleyRingForwardMatrix X * (H⁻¹).1 + 1) *
              cayleyRingInverseMatrix
                (cayleyRingForwardMatrix X * (H⁻¹).1)) *
          (H.1 * (1 - Y)) := by
            rw [hH, cayleyRingForwardMatrix_mul_one_sub Y hY]
            noncomm_ring
    _ =
        (1 - X) *
          (((cayleyRingForwardMatrix X * (H⁻¹).1 + 1) *
              cayleyRingInverseMatrix
                (cayleyRingForwardMatrix X * (H⁻¹).1)) * H.1) *
          (1 - Y) := by
            noncomm_ring
    _ = (1 - X) *
          (cayleyRingForwardMatrix X - cayleyRingForwardMatrix Y) *
          (1 - Y) := by rw [hrelative, hH]
    _ = cayleyRingTwoMatrix * (X - Y) :=
      cayleyRingForwardMatrix_sub_cross X Y hX hY

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The combined relative Cayley identity specialized to the literal integral
inverse-Cayley coordinates of two odd-prime denominator-congruence
stabilizers. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceRelativeInverseCayleyIntegral_cross_sub
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceSubgroup p) :
    let X : Matrix (Fin n) (Fin n) ℤ_[p] :=
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 g
    let Y : Matrix (Fin n) (Fin n) ℤ_[p] :=
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 h
    let R : Matrix (Fin n) (Fin n) ℤ_[p] :=
      (L.localPadicLatticeStabilizerIntegralGL p (g * h⁻¹).1).1
    let Z : Matrix (Fin n) (Fin n) ℤ_[p] :=
      L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 (g * h⁻¹)
    (1 - X) * (R + 1) * Z * (1 + Y) =
      (@Matrix.cayleyRingTwoMatrix (Fin n) ℤ_[p] _ _ _) * (X - Y) := by
  dsimp only
  let G := L.localPadicLatticeStabilizerIntegralGL p g.1
  let H := L.localPadicLatticeStabilizerIntegralGL p h.1
  let R := L.localPadicLatticeStabilizerIntegralGL p (g * h⁻¹).1
  let X : Matrix (Fin n) (Fin n) ℤ_[p] :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 g
  let Y : Matrix (Fin n) (Fin n) ℤ_[p] :=
    L.localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
      p hp2 h
  have h2 : IsUnit (2 : ℤ_[p]) := two_isUnit_padicInt_of_ne_two p hp2
  have hGdomain : G.1 ∈ Matrix.cayleyRingInverseDomain :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 g
  have hHdomain : H.1 ∈ Matrix.cayleyRingInverseDomain :=
    L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
      p hp2 h
  have hXeq : X = Matrix.cayleyRingInverseMatrix G.1 := by
    exact
      L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 g
  have hYeq : Y = Matrix.cayleyRingInverseMatrix H.1 := by
    exact
      L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral
        p hp2 h
  have hXsource : X ∈ Matrix.cayleyRingSource := by
    rw [hXeq]
    exact Matrix.cayleyRingInverseMatrix_mem_source h2 G.1 hGdomain
  have hYsource : Y ∈ Matrix.cayleyRingSource := by
    rw [hYeq]
    exact Matrix.cayleyRingInverseMatrix_mem_source h2 H.1 hHdomain
  have hGforward : Matrix.cayleyRingForwardMatrix X = G.1 := by
    rw [hXeq]
    exact Matrix.cayleyRingForwardMatrix_inverse h2 G.1 hGdomain
  have hHforward : H.1 = Matrix.cayleyRingForwardMatrix Y := by
    rw [hYeq]
    exact (Matrix.cayleyRingForwardMatrix_inverse h2 H.1 hHdomain).symm
  have hHinv :
      L.localPadicLatticeStabilizerIntegralGL p h.1⁻¹ = H⁻¹ := by
    simpa only [H] using
      (L.localPadicLatticeStabilizerIntegralGLHom p).map_inv h.1
  have hRmatrix : R.1 = G.1 * (H⁻¹).1 := by
    calc
      R.1 = (G * (L.localPadicLatticeStabilizerIntegralGL p h.1⁻¹)).1 := by
        exact congrArg Units.val
          ((L.localPadicLatticeStabilizerIntegralGLHom p).map_mul g.1 h.1⁻¹)
      _ = (G * H⁻¹).1 := by
        rw [hHinv]
      _ = G.1 * (H⁻¹).1 := rfl
  have hRdomain : Matrix.cayleyRingForwardMatrix X * (H⁻¹).1 ∈
      Matrix.cayleyRingInverseDomain := by
    rw [hGforward, ← hRmatrix]
    exact
      L.isUnit_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceIntegralGL_add_one
        p hp2 (g * h⁻¹)
  have hmain :=
    Matrix.cayleyRingRelativeInverse_cross_sub
      X Y hXsource hYsource H hHforward hRdomain
  rw [hGforward, ← hRmatrix] at hmain
  change
    (1 - X) * (R.1 + 1) *
          Matrix.cayleyRingInverseMatrix R.1 * (1 + Y) =
      Matrix.cayleyRingTwoMatrix * (X - Y) at hmain
  simpa only [X, Y, R,
    L.coe_localPadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceInverseCayleyIntegral]
    using hmain

end PositiveDefiniteIntegralLattice
