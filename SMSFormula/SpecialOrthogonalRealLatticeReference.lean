import SMSFormula.SpecialOrthogonalRealDifferentialHaar
import SMSFormula.AdelicProperFullPresentation

/-!
# Lattice specialization of the real differential Haar measure

The rational differential construction reaches the real place by first
mapping the lattice form matrix through `ℚ`; the existing compact reference
Haar uses the direct integer-to-real form matrix. These matrices agree.
This module transports the differential Haar across the resulting
identity-on-matrices continuous group equivalence and compares it with the
existing probability Haar.

The comparison scalar is not evaluated as a gamma product here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance latticeRealReferenceSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

local instance latticeRealReferenceSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Scalar extension through `ℚ` gives the same real form matrix as direct
scalar extension from `ℤ`. -/
theorem rationalFormMatrix_map_real (L : PositiveDefiniteIntegralLattice n) :
    L.rationalFormMatrix.map (algebraMap ℚ ℝ) = L.pairingMatrix_real := by
  ext i j
  simp [rationalFormMatrix, pairingMatrix_real]

/-- The real special-orthogonal carrier used by the rational differential
construction is continuously multiplicatively equivalent to the existing
lattice real carrier. -/
def rationalDifferentialSpecialOrthogonalContinuousEquivReal
    (L : PositiveDefiniteIntegralLattice n) :
    specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℝ)) ≃ₜ*
      L.ConcreteRealSpecialOrthogonalGroup := by
  rw [L.rationalFormMatrix_map_real]
  exact ContinuousMulEquiv.refl _

/-- The carrier equivalence is the identity on the underlying real matrix. -/
@[simp]
theorem coe_rationalDifferentialSpecialOrthogonalContinuousEquivReal_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℝ))) :
    ((L.rationalDifferentialSpecialOrthogonalContinuousEquivReal g).1.1.1 :
      Matrix (Fin n) (Fin n) ℝ) = g.1.1.1 := by
  have h := L.rationalFormMatrix_map_real
  cases h
  rfl

/-- The inverse carrier equivalence is also the identity on the underlying
real matrix. -/
@[simp]
theorem coe_rationalDifferentialSpecialOrthogonalContinuousEquivReal_symm_apply
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteRealSpecialOrthogonalGroup) :
    ((L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.symm g).1.1.1 :
      Matrix (Fin n) (Fin n) ℝ) = g.1.1.1 := by
  have h := L.rationalFormMatrix_map_real
  cases h
  rfl

/-- The rationally normalized differential Haar transported to the exact
real special-orthogonal carrier already used by the lattice adelic route. -/
def concreteRealSpecialOrthogonalDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.ConcreteRealSpecialOrthogonalGroup :=
  Measure.map
    L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.toHomeomorph
    (specialFormPreservingSmoothRealDifferentialMeasure
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero)

/-- Inverse transport recovers the rationally normalized differential Haar. -/
theorem map_concreteRealSpecialOrthogonalDifferentialMeasure_symm
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.map
        L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.symm.toHomeomorph
        L.concreteRealSpecialOrthogonalDifferentialMeasure =
      specialFormPreservingSmoothRealDifferentialMeasure
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero := by
  rw [concreteRealSpecialOrthogonalDifferentialMeasure]
  exact MeasurableEquiv.map_map_symm
    L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.symm.toMeasurableEquiv

/-- Transport to the exact lattice carrier preserves total mass. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ =
      specialFormPreservingSmoothRealDifferentialMeasure
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero Set.univ := by
  rw [concreteRealSpecialOrthogonalDifferentialMeasure,
    Measure.map_apply
      L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.toHomeomorph.measurable
      MeasurableSet.univ]
  simp

/-- The transported differential measure is Haar at the scale fixed by the
rational invariant differential. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_isHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsHaarMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure := by
  letI : Measure.IsHaarMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure
        L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero) :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero
  exact
    L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.toMulEquiv
      |>.isHaarMeasure_map
        (specialFormPreservingSmoothRealDifferentialMeasure
          L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero)
        L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.continuous
        L.rationalDifferentialSpecialOrthogonalContinuousEquivReal.symm.continuous

instance concreteRealSpecialOrthogonalDifferentialMeasure_instHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsHaarMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
  L.concreteRealSpecialOrthogonalDifferentialMeasure_isHaarMeasure

/-- The existing probability-normalized real reference measure is Haar. -/
theorem concreteRealSpecialOrthogonalNormalizedHaarMeasure_isHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsHaarMeasure
      L.concreteRealSpecialOrthogonalNormalizedHaarMeasure := by
  unfold concreteRealSpecialOrthogonalNormalizedHaarMeasure
  infer_instance

instance concreteRealSpecialOrthogonalNormalizedHaarMeasure_instHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsHaarMeasure
      L.concreteRealSpecialOrthogonalNormalizedHaarMeasure :=
  L.concreteRealSpecialOrthogonalNormalizedHaarMeasure_isHaarMeasure

/-- The concrete lattice real group is second countable. -/
theorem concreteRealSpecialOrthogonalGroup_secondCountable
    (L : PositiveDefiniteIntegralLattice n) :
    SecondCountableTopology L.ConcreteRealSpecialOrthogonalGroup := by
  change SecondCountableTopology
    (specialFormPreservingMatrixSubgroup L.pairingMatrix_real)
  rw [← L.rationalFormMatrix_map_real]
  exact specialFormPreservingRealGroup_secondCountable L.rationalFormMatrix

/-- Haar uniqueness compares the transported differential measure with the
existing probability Haar by its canonical scalar factor. -/
theorem concreteRealSpecialOrthogonalDifferentialMeasure_eq_haarScalarFactor_smul
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteRealSpecialOrthogonalDifferentialMeasure =
      Measure.haarScalarFactor
          L.concreteRealSpecialOrthogonalDifferentialMeasure
          L.concreteRealSpecialOrthogonalNormalizedHaarMeasure •
        L.concreteRealSpecialOrthogonalNormalizedHaarMeasure := by
  letI : SecondCountableTopology L.ConcreteRealSpecialOrthogonalGroup :=
    L.concreteRealSpecialOrthogonalGroup_secondCountable
  exact Measure.isMulLeftInvariant_eq_smul
    L.concreteRealSpecialOrthogonalDifferentialMeasure
    L.concreteRealSpecialOrthogonalNormalizedHaarMeasure

/-- Because the reference Haar has total mass one, the comparison scalar is
exactly the total mass of the transported differential measure. -/
theorem coe_haarScalarFactor_concreteRealSpecialOrthogonal_eq_differential_univ
    (L : PositiveDefiniteIntegralLattice n) :
    (Measure.haarScalarFactor
        L.concreteRealSpecialOrthogonalDifferentialMeasure
        L.concreteRealSpecialOrthogonalNormalizedHaarMeasure : ℝ≥0∞) =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ := by
  have h := congrArg
    (fun μ : Measure L.ConcreteRealSpecialOrthogonalGroup => μ Set.univ)
    L.concreteRealSpecialOrthogonalDifferentialMeasure_eq_haarScalarFactor_smul
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    L.concreteRealSpecialOrthogonalNormalizedHaarMeasure_univ, mul_one] using h.symm

end PositiveDefiniteIntegralLattice
