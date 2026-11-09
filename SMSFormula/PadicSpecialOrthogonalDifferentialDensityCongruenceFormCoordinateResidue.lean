import SMSFormula.SkewAdjointFormElementaryPadicCoordinateResidue

/-!
# Odd-prime density kernels as form-coordinate residue preimages

At an odd prime, the density-congruence source lies in the form-adapted
integral coordinate lattice and is invariant under translation by the
explicit determinant-loss ball.  Reducing the integral form coordinates at
that level therefore identifies the source exactly as the preimage of its
finite residue image.

No cardinality of this image is compared with an ordinary-reduction or
associated-bilinear carrier in this module.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The explicit form-coordinate residue level at which the odd-prime density
source is translation invariant. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
    padicValInt p L.pairingDeterminant

/-- Regard an odd-prime density-source point as a point of the form-adapted
integral coordinate lattice. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinatePoint
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      p) :
    skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero := by
  refine ⟨X.1, ?_⟩
  apply
    skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall
      p hp2 X.2

/-- Integral form-coordinate points whose ambient values belong to the
density-congruence source. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :=
  Subtype.val ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet p

/-- The finite residue image of the odd-prime density source at the explicit
determinant-loss level. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (skewAdjointFormElementaryPadicCoordinateResidue
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix) :=
  skewAdjointFormElementaryPadicCoordinateReduction
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
        p)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero ''
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
      p

/-- The form-coordinate residue image is finite because it lies in the
canonical finite residue carrier. -/
theorem
    finite_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      p).Finite :=
  Set.toFinite _

/-- Every odd-prime ambient density-source point has its literal integral
form-coordinate representative in the integral source. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinatePoint_mem_source
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      p) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinatePoint
        p hp2 X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
        p :=
  X.2

/-- At an odd prime, the integral form-coordinate density source is exactly
the preimage of its finite residue image at the explicit determinant-loss
level. -/
theorem
    preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_eq_source
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    skewAdjointFormElementaryPadicCoordinateReduction
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            p)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero ⁻¹'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          p =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
        p := by
  ext x
  constructor
  · rintro ⟨y, hy, hred⟩
    change
      x.1 ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p
    have hdiff :
        x.1 - y.1 ∈
          skewAdjointFormElementaryPadicUniformCoordinateBall
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              p)
            L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero :=
      (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_sub_mem_uniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero y x).1 hred.symm
    have hadd :=
      (L.add_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_add_pairingDeterminantVal
        p hp2 y.1 (x.1 - y.1) hdiff).2 hy
    have heq : y.1 + (x.1 - y.1) = x.1 := by abel
    rw [heq] at hadd
    exact hadd
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Mapping the integral form-coordinate density source to the ambient
skew-adjoint carrier recovers the literal ambient density source. -/
theorem
    image_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource_eq_ambientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Subtype.val ''
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
          p =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  ext X
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hX
    let XL :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinatePoint
        p hp2 ⟨X, hX⟩
    refine ⟨XL, ?_, rfl⟩
    exact hX

/-- The ambient odd-prime density source is the ambient image of the preimage
of its canonical finite form-coordinate residue image. -/
theorem
    image_preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_eq_ambientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    Subtype.val ''
        (skewAdjointFormElementaryPadicCoordinateReduction
              p
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
                p)
              L.rationalFormMatrix (L.form_symm.map _)
                L.rationalFormMatrix_det_ne_zero ⁻¹'
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
            p) =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  rw [L.preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage_eq_source
    p hp2]
  exact
    L.image_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource_eq_ambientSet
      p hp2

end PositiveDefiniteIntegralLattice
