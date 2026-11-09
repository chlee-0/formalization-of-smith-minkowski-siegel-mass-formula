import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteStabilizerCarrier

/-!
# Differential measure on the full-adelic real/finite stabilizer subgroup

The literal product of the internally constructed real and finite differential
measures is pushed across the continuous multiplicative carrier
equivalence.  The resulting measure lives only on the natural full-adelic
stabilizer subgroup.

It is not asserted to be a Haar measure on the ambient full adelic group, and
no comparison with reference Haar or quotient measure occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    fullAdelicRealFiniteDifferentialStabilizerMeasureRealSecondCountable
    (L : PositiveDefiniteIntegralLattice n) :
    SecondCountableTopology L.ConcreteRealSpecialOrthogonalGroup := by
  exact L.concreteRealSpecialOrthogonalGroup_secondCountable

local instance
    fullAdelicRealFiniteDifferentialStabilizerMeasureRealOpensMeasurable
    (L : PositiveDefiniteIntegralLattice n) :
    OpensMeasurableSpace L.ConcreteRealSpecialOrthogonalGroup := by
  infer_instance

local instance
    fullAdelicRealFiniteDifferentialStabilizerMeasureFiniteOpensMeasurable
    (L : PositiveDefiniteIntegralLattice n) :
    OpensMeasurableSpace
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
  infer_instance

local instance
    fullAdelicRealFiniteDifferentialStabilizerMeasureSecondCountableEither
    (L : PositiveDefiniteIntegralLattice n) :
    SecondCountableTopologyEither
      L.ConcreteRealSpecialOrthogonalGroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  ⟨Or.inl L.concreteRealSpecialOrthogonalGroup_secondCountable⟩

local instance
    fullAdelicRealFiniteDifferentialStabilizerMeasureProductOpensMeasurable
    (L : PositiveDefiniteIntegralLattice n) :
    OpensMeasurableSpace
      (L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) := by
  infer_instance

/-- The internally normalized differential measure on the natural
real-times-integral-finite subgroup of the full adelic special orthogonal
group. -/
noncomputable def fullAdelicRealFiniteDifferentialStabilizerMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
  Measure.map
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
    (L.realFiniteDifferentialStabilizerProductMeasure P)

/-- Transport to the full-adelic stabilizer subgroup preserves the exact
literal real-times-finite differential mass. -/
@[simp]
theorem fullAdelicRealFiniteDifferentialStabilizerMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure P Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  let e :=
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
  let μ :=
    L.realFiniteDifferentialStabilizerProductMeasure P
  have he : AEMeasurable (fun x => e x) μ :=
    e.continuous.measurable.aemeasurable
  calc
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure P Set.univ =
        (Measure.map (fun x => e x) μ) Set.univ := by
      rfl
    _ = μ ((fun x => e x) ⁻¹' Set.univ) :=
      Measure.map_apply_of_aemeasurable he MeasurableSet.univ
    _ = μ Set.univ := by rw [Set.preimage_univ]
    _ =
        L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
          L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P :=
      L.realFiniteDifferentialStabilizerProductMeasure_univ hP

/-- The transported subgroup differential measure has nonzero total mass. -/
theorem fullAdelicRealFiniteDifferentialStabilizerMeasure_univ_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure P Set.univ ≠ 0 := by
  rw [L.fullAdelicRealFiniteDifferentialStabilizerMeasure_univ hP]
  exact mul_ne_zero
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P)

/-- The transported subgroup differential measure itself is nonzero. -/
theorem fullAdelicRealFiniteDifferentialStabilizerMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure P ≠ 0 := by
  intro hzero
  apply L.fullAdelicRealFiniteDifferentialStabilizerMeasure_univ_ne_zero hP
  rw [hzero]
  rfl

/-- A positive cutoff-product limit makes the transported subgroup
differential measure finite. -/
theorem fullAdelicRealFiniteDifferentialStabilizerMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    IsFiniteMeasure
      (L.fullAdelicRealFiniteDifferentialStabilizerMeasure P) where
  measure_univ_lt_top := by
    rw [L.fullAdelicRealFiniteDifferentialStabilizerMeasure_univ hP]
    letI : IsFiniteMeasure
        L.concreteRealSpecialOrthogonalDifferentialMeasure :=
      L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
    exact ENNReal.mul_lt_top
      IsFiniteMeasure.measure_univ_lt_top
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top
        hP).lt_top

/-- The transported differential measure is left invariant under the
full-adelic stabilizer subgroup. -/
theorem fullAdelicRealFiniteDifferentialStabilizerMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.IsMulLeftInvariant
      (L.fullAdelicRealFiniteDifferentialStabilizerMeasure P) := by
  letI : Measure.IsMulLeftInvariant
      (L.realFiniteDifferentialStabilizerProductMeasure P) :=
    L.realFiniteDifferentialStabilizerProductMeasure_isMulLeftInvariant hP
  unfold fullAdelicRealFiniteDifferentialStabilizerMeasure
  exact isMulLeftInvariant_map
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.toMulHom
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.continuous.measurable
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.surjective

end PositiveDefiniteIntegralLattice
