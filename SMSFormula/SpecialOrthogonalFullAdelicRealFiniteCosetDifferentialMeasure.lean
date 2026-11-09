import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteCosetTransport
import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteDifferentialStabilizerMeasure

/-!
# One translated full-adelic stabilizer-coset differential measure

For each quotient index, the internally constructed differential measure on
the open real/unrestricted, finite/integral stabilizer is transported through
the literal coset homeomorphism.  Mapping that coset-subtype measure through
the subtype inclusion gives a measure on the ambient full-adelic group
supported on exactly one chosen left coset.

This is one translated coset measure, not ambient Haar.  No sum over quotient
indices, reference-Haar comparison, quotient measure, or Tamagawa theorem
occurs here.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The differential stabilizer measure transported to one chosen left-coset
subtype. -/
noncomputable def fullAdelicRealFiniteCosetDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    Measure (L.FullAdelicRealFiniteLatticeStabilizerCoset C) :=
  Measure.map
    (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C)
    (L.fullAdelicRealFiniteDifferentialStabilizerMeasure P)

/-- Transport to a chosen coset preserves the subgroup measure's total
mass. -/
@[simp]
theorem fullAdelicRealFiniteCosetDifferentialMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteCosetDifferentialMeasure P C Set.univ =
      L.fullAdelicRealFiniteDifferentialStabilizerMeasure P Set.univ := by
  unfold fullAdelicRealFiniteCosetDifferentialMeasure
  rw [Measure.map_apply
    (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).measurable
    MeasurableSet.univ, Set.preimage_univ]

/-- The chosen-coset measure has the exact internally computed
real-times-finite stabilizer mass. -/
theorem fullAdelicRealFiniteCosetDifferentialMeasure_univ_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteCosetDifferentialMeasure P C Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  rw [L.fullAdelicRealFiniteCosetDifferentialMeasure_univ P C,
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure_univ hP]

/-- A positive cutoff limit makes every chosen-coset measure nonzero. -/
theorem fullAdelicRealFiniteCosetDifferentialMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteCosetDifferentialMeasure P C ≠ 0 := by
  intro hzero
  apply L.fullAdelicRealFiniteDifferentialStabilizerMeasure_univ_ne_zero hP
  rw [← L.fullAdelicRealFiniteCosetDifferentialMeasure_univ P C, hzero]
  rfl

/-- A positive cutoff limit makes every chosen-coset measure finite. -/
theorem fullAdelicRealFiniteCosetDifferentialMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    IsFiniteMeasure (L.fullAdelicRealFiniteCosetDifferentialMeasure P C) := by
  letI : IsFiniteMeasure
      (L.fullAdelicRealFiniteDifferentialStabilizerMeasure P) :=
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure_isFinite hP
  refine ⟨?_⟩
  rw [L.fullAdelicRealFiniteCosetDifferentialMeasure_univ P C]
  exact IsFiniteMeasure.measure_univ_lt_top

/-- The one-coset differential measure regarded as an ambient full-adelic
measure.  It remains supported on that one coset. -/
noncomputable def fullAdelicRealFiniteAmbientCosetDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    Measure L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  Measure.map Subtype.val
    (L.fullAdelicRealFiniteCosetDifferentialMeasure P C)

/-- The ambient one-coset measure is literally the pushforward by left
multiplication with the selected quotient representative. -/
theorem fullAdelicRealFiniteAmbientCosetDifferentialMeasure_eq_map_mul_left
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C =
      Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out C * h)
        (L.fullAdelicRealFiniteDifferentialStabilizerMeasure P) := by
  unfold fullAdelicRealFiniteAmbientCosetDifferentialMeasure
    fullAdelicRealFiniteCosetDifferentialMeasure
  rw [Measure.map_map
    continuous_subtype_val.measurable
    (L.fullAdelicRealFiniteLatticeStabilizerCosetHomeomorph C).measurable]
  rfl

/-- Passing from the coset subtype to the ambient group preserves total
mass. -/
@[simp]
theorem fullAdelicRealFiniteAmbientCosetDifferentialMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C Set.univ =
      L.fullAdelicRealFiniteCosetDifferentialMeasure P C Set.univ := by
  unfold fullAdelicRealFiniteAmbientCosetDifferentialMeasure
  rw [Measure.map_apply continuous_subtype_val.measurable
    MeasurableSet.univ, Set.preimage_univ]

/-- The ambient one-coset measure has the exact real-times-finite
stabilizer mass. -/
theorem
    fullAdelicRealFiniteAmbientCosetDifferentialMeasure_univ_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  rw [L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_univ P C,
    L.fullAdelicRealFiniteCosetDifferentialMeasure_univ_eq_real_mul_finite
      hP C]

/-- A positive cutoff limit makes the ambient one-coset measure nonzero. -/
theorem fullAdelicRealFiniteAmbientCosetDifferentialMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C ≠ 0 := by
  intro hzero
  apply L.fullAdelicRealFiniteDifferentialStabilizerMeasure_univ_ne_zero hP
  rw [← L.fullAdelicRealFiniteCosetDifferentialMeasure_univ P C,
    ← L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_univ P C, hzero]
  rfl

/-- A positive cutoff limit makes the ambient one-coset measure finite. -/
theorem fullAdelicRealFiniteAmbientCosetDifferentialMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    IsFiniteMeasure
      (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C) := by
  letI : IsFiniteMeasure
      (L.fullAdelicRealFiniteCosetDifferentialMeasure P C) :=
    L.fullAdelicRealFiniteCosetDifferentialMeasure_isFinite hP C
  refine ⟨?_⟩
  rw [L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_univ P C]
  exact IsFiniteMeasure.measure_univ_lt_top

/-- The ambient one-coset measure vanishes on every measurable set disjoint
from its selected coset. -/
theorem fullAdelicRealFiniteAmbientCosetDifferentialMeasure_apply_eq_zero_of_disjoint
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
    {A : Set L.ConcreteFullAdelicSpecialOrthogonalGroup}
    (hA : MeasurableSet A)
    (hdisj : Disjoint A (L.fullAdelicRealFiniteLatticeStabilizerCoset C)) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C A = 0 := by
  unfold fullAdelicRealFiniteAmbientCosetDifferentialMeasure
  rw [Measure.map_apply continuous_subtype_val.measurable hA]
  have hpre :
      ((↑) :
        L.FullAdelicRealFiniteLatticeStabilizerCoset C →
          L.ConcreteFullAdelicSpecialOrthogonalGroup) ⁻¹' A = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hg
    exact Set.disjoint_left.mp hdisj hg g.property
  rw [hpre, measure_empty]

/-- In particular, the ambient one-coset measure gives zero mass to the
complement of its selected coset. -/
theorem fullAdelicRealFiniteAmbientCosetDifferentialMeasure_compl
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C)ᶜ = 0 := by
  apply
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_apply_eq_zero_of_disjoint
      P C
      (L.measurableSet_fullAdelicRealFiniteLatticeStabilizerCoset C).compl
  rw [Set.disjoint_left]
  intro g hg hgc
  exact hg hgc

/-- Restriction to the selected coset does not change the ambient one-coset
measure. -/
theorem restrict_fullAdelicRealFiniteAmbientCosetDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C).restrict
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) =
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact mem_ae_iff.mpr
    (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_compl P C)

/-- Pulling the ambient one-coset measure back through the measurable coset
inclusion recovers exactly the subtype measure transported by the chosen
homeomorphism. -/
theorem comap_fullAdelicRealFiniteAmbientCosetDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    Measure.comap
        ((↑) :
          L.FullAdelicRealFiniteLatticeStabilizerCoset C →
            L.ConcreteFullAdelicSpecialOrthogonalGroup)
        (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C) =
      L.fullAdelicRealFiniteCosetDifferentialMeasure P C := by
  unfold fullAdelicRealFiniteAmbientCosetDifferentialMeasure
  exact
    (MeasurableEmbedding.subtype_coe
      (L.measurableSet_fullAdelicRealFiniteLatticeStabilizerCoset C)).comap_map _

end PositiveDefiniteIntegralLattice
