import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicTranslation
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateMass

/-!
# Dyadic form-coordinate mass of the density source

The completed dyadic outer containment places every source coordinate in the
form-adapted integral lattice.  Translation saturation by the selected
determinant-loss ball then identifies the complete source as the preimage of
its attained residues at the prescribed level.  The existing prime-independent
finite disjoint-ball and Haar-measure calculations evaluate its coordinate
mass.

No dyadic stabilizer/associated-bilinear count or gauge value is asserted.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped BigOperators Matrix Matrix.Norms.Operator ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Regard a dyadic density-source point as a point of the form-adapted
integral coordinate lattice. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint
    (L : PositiveDefiniteIntegralLattice n)
    (X : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      2) :
    skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      2 L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨X.1, ?_⟩
  apply
    skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
      2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)
      L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
  exact
    L.localPadicSpecialOrthogonalDifferentialDyadicDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall_pred
      X.2

/-- The dyadic source point in the form-coordinate lattice belongs
to the integral density source. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint_mem_source
    (L : PositiveDefiniteIntegralLattice n)
    (X : L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint
        X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
        2 :=
  X.2

/-- At two, the integral form-coordinate density source is exactly the
preimage of its attained finite residue image at level
`densityDepth + v₂(pairingDeterminant)`. -/
theorem
    preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueImage_eq_source
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero ⁻¹'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2 =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
        2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  constructor
  · rintro ⟨y, hy, hred⟩
    change
      x.1 ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2
    have hdiff :
        x.1 - y.1 ∈
          skewAdjointFormElementaryPadicUniformCoordinateBall
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2)
            L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero :=
      (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_sub_mem_uniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero y x).1 hred.symm
    have hadd :=
      (L.add_mem_dyadicDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_add_pairingDeterminantVal
        y.1 (x.1 - y.1) hdiff).2 hy
    have heq : y.1 + (x.1 - y.1) = x.1 := by abel
    rwa [heq] at hadd
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Mapping the integral dyadic form-coordinate source to the ambient
skew-adjoint carrier recovers the literal ambient source. -/
theorem
    image_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateSource_eq_ambientSet
    (L : PositiveDefiniteIntegralLattice n) :
    Subtype.val ''
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateSource
          2 =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext X
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hX
    let XL :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint
        ⟨X, hX⟩
    refine ⟨XL, ?_, rfl⟩
    exact hX

/-- The ambient dyadic source is the ambient image of the preimage of its
canonical finite form-coordinate residue image. -/
theorem
    image_preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueImage_eq_ambientSet
    (L : PositiveDefiniteIntegralLattice n) :
    Subtype.val ''
        (skewAdjointFormElementaryPadicCoordinateReduction
              2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
                2)
              L.rationalFormMatrix (L.form_symm.map _)
                L.rationalFormMatrix_det_ne_zero ⁻¹'
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
            2) =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [L.preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueImage_eq_source]
  exact
    L.image_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateSource_eq_ambientSet

/-- The union of the translated prescribed-level balls indexed by attained
dyadic residues is exactly the ambient dyadic density source. -/
theorem
    iUnion_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueBall_eq_ambientSet
    (L : PositiveDefiniteIntegralLattice n) :
    (⋃ a :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          2,
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
        2 a) =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext X
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨a, hXa⟩
    let ca :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
        2 a
    have hdiff : X - ca.1 ∈
        skewAdjointFormElementaryPadicUniformCoordinateBall
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero :=
      (mem_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall_iff
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ca.1 X).1 hXa
    have hadd :=
      (L.add_mem_dyadicDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_add_pairingDeterminantVal
        ca.1 (X - ca.1) hdiff).2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
          2 a)
    have heq : ca.1 + (X - ca.1) = X := by abel
    rwa [heq] at hadd
  · intro hX
    let XL :=
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint
        ⟨X, hX⟩
    have hres :
        skewAdjointFormElementaryPadicCoordinateReduction
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2)
            L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero XL ∈
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
            2 :=
      ⟨XL, hX, rfl⟩
    let a :
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
          2 :=
      ⟨skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero XL,
        hres⟩
    rw [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    apply
      (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
          2 a) XL).1
    rw [L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
      2 a]

local instance dyadicFormCoordinateMassMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule :=
  borel _

local instance dyadicFormCoordinateMassBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule :=
  ⟨rfl⟩

/-- The dyadic form-coordinate comparison mass is the attained residue count
times the explicit mass of one ball at level
`densityDepth + v₂(pairingDeterminant)`. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_residueImage_ncard_mul
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointFormElementaryPadicCoordinateMeasure
        2 L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
        ((2 : ℝ≥0∞) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        2) :=
    (L.finite_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      2).fintype
  rw [←
    L.iUnion_localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinateResidueBall_eq_ambientSet]
  calc
    skewAdjointFormElementaryPadicCoordinateMeasure
        2 L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (⋃ a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            2,
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
            2 a) =
        ∑' a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            2,
          skewAdjointFormElementaryPadicCoordinateMeasure
            2 L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
              2 a) := by
      exact measure_iUnion
        (fun a b hab ↦
          L.pairwise_disjoint_localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueBall
            2 hab)
        (fun a ↦
          measurableSet_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
            2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2)
            L.rationalFormMatrix (L.form_symm.map _)
              L.rationalFormMatrix_det_ne_zero
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
              2 a).1)
    _ = ∑ a :
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
            2,
        ((2 : ℝ≥0∞) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro a _
      exact
        skewAdjointFormElementaryPadicCoordinateMeasure_translatedUniformCoordinateBall_explicit
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
            2 a).1
    _ =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
        ((2 : ℝ≥0∞) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
              2 *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
      have hcard :
          Fintype.card
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
                2) =
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              2).ncard := by
        rw [Set.ncard_eq_toFinset_card']
        simp
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ, hcard]

/-- The dyadic source mass formula with the prescribed residue level unfolded
literally as `densityDepth + v₂(pairingDeterminant)`. -/
theorem
    skewAdjointFormElementaryPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_residueImage_ncard_mul_explicit
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointFormElementaryPadicCoordinateMeasure
        2 L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2) =
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
        ((2 : ℝ≥0∞) ^
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
              padicValInt 2 L.pairingDeterminant) *
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel]
    using
      L.skewAdjointFormElementaryPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_residueImage_ncard_mul

end PositiveDefiniteIntegralLattice
