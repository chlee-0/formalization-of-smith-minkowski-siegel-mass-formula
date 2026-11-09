import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteAdelicStabilizerCarrier
import SMSFormula.PadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
import Mathlib.Topology.Bases

/-!
# Differential measure on the concrete finite-adelic special stabilizer

The absolutely scaled product of the local differential stabilizer
measures is pushed across the canonical continuous multiplicative carrier
equivalence.  The resulting measure on the concrete finite-adelic special
stabilizer has the internally computed total mass and is left invariant.

No comparison with, or rescaling of, the finite-adelic reference Haar
measure occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasurePrimeFact
    (q : {p : ℕ // Nat.Prime p}) : Fact (Nat.Prime q.1) :=
  ⟨q.2⟩

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  ⟨rfl⟩

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureMatrixSecondCountable
    (q : {p : ℕ // Nat.Prime p}) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[q.1]) := by
  change SecondCountableTopology (Fin n → Fin n → ℚ_[q.1])
  infer_instance

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureMatrixMulOppositeSecondCountable
    (q : {p : ℕ // Nat.Prime p}) :
    SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[q.1])ᵐᵒᵖ :=
  (@MulOpposite.opHomeomorph
    (Matrix (Fin n) (Fin n) ℚ_[q.1]) _).symm.secondCountableTopology

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureGLSecondCountable
    (q : {p : ℕ // Nat.Prime p}) :
    SecondCountableTopology (GL (Fin n) ℚ_[q.1]) :=
  Units.isEmbedding_embedProduct.secondCountableTopology

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureFormSecondCountable
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    SecondCountableTopology
      (formPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (formPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1])) :
        Set (GL (Fin n) ℚ_[q.1]))

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureSpecialSecondCountable
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1])) :
        Set
          (formPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))))

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureOpensMeasurable
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    OpensMeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  ⟨le_rfl⟩

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureLocalSecondCountable
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    SecondCountableTopology
      (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q :
      Set
        (specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))))

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureLocalBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    BorelSpace
      (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q) :=
  Subtype.borelSpace _

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureLocalOpensMeasurable
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    OpensMeasurableSpace
      (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q) :=
  BorelSpace.opensMeasurable

local instance
    localPadicSpecialOrthogonalDifferentialFiniteAdelicMeasureProductOpensMeasurable
    (L : PositiveDefiniteIntegralLattice n) :
    OpensMeasurableSpace
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct :=
  Pi.opensMeasurableSpace

/-- The internally normalized differential measure on the concrete
finite-adelic special stabilizer.  It is the literal pushforward of the
all-prime product measure through the carrier equivalence. -/
noncomputable def
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  Measure.map
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerContinuousMulEquiv
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
      P)

/-- Transport across the carrier equivalence preserves the total mass. -/
@[simp]
theorem
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P Set.univ =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  let e :=
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerContinuousMulEquiv
  let μ :=
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure P
  have he : AEMeasurable (fun x => e x) μ :=
    e.continuous.measurable.aemeasurable
  calc
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P Set.univ =
        (Measure.map (fun x => e x) μ) Set.univ := by
      rfl
    _ = μ ((fun x => e x) ⁻¹' Set.univ) :=
      Measure.map_apply_of_aemeasurable he MeasurableSet.univ
    _ = μ Set.univ := by rw [Set.preimage_univ]
    _ =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P :=
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ
        P

/-- The transported finite-adelic differential measure has nonzero total
mass. -/
theorem
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P Set.univ ≠
      0 := by
  rw [L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ P]
  exact
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P

/-- The transported measure itself is nonzero. -/
theorem
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P ≠ 0 := by
  intro hzero
  apply
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ_ne_zero P
  rw [hzero]
  rfl

/-- A positive cutoff-product limit makes the transported total mass finite. -/
theorem
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ_ne_top
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P Set.univ ≠
      ⊤ := by
  rw [L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ P]
  exact
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP

/-- Under a positive cutoff-product limit, the transported differential
measure is finite. -/
theorem
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    IsFiniteMeasure
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) where
  measure_univ_lt_top :=
    (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ_ne_top
      hP).lt_top

/-- The reciprocal total mass is the named differential inverse volume. -/
theorem
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ_inv
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure
        P Set.univ)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
        P := by
  rw [L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_univ P]
  exact
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume
      P).symm

/-- The transported finite-adelic differential measure is left invariant.
This follows functorially from the multiplicative carrier equivalence and the
literal source-product invariance. -/
instance
    finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure.IsMulLeftInvariant
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) := by
  unfold finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure
  exact isMulLeftInvariant_map
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerContinuousMulEquiv.toMulHom
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerContinuousMulEquiv.continuous.measurable
    L.localPadicSpecialOrthogonalDifferentialAllPrimeFiniteAdelicStabilizerContinuousMulEquiv.surjective

end PositiveDefiniteIntegralLattice
