import SMSFormula.SpecialOrthogonalFullAdelicDifferentialInvariance
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Regular Haar certification for the full-adelic differential measure

The natural real/unrestricted, finite/integral stabilizer is compact as well
as open.  Hence every chosen left coset is compact-open.  Exact restriction
of the ambient differential measure to such a coset identifies its mass with
the already computed real differential mass times finite differential
stabilizer volume.  This mass is positive and finite for a positive cutoff
limit.

Together with the internally proved ambient left invariance, this gives a
direct `Measure.IsHaarMeasure` certificate and regularity.  No Haar
uniqueness, reference-Haar comparison, quotient measure, or Tamagawa theorem
is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The full-adelic real/unrestricted, finite/integral lattice stabilizer is
compact. -/
theorem isCompact_fullAdelicRealFiniteLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsCompact
      (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup) := by
  letI : CompactSpace
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
    isCompact_iff_compactSpace.mp
      L.isCompact_finiteSpecialOrthogonalLatticeStabilizerSubgroup
  let e :=
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
  have hcompact :
      IsCompact
        (Set.univ :
          Set
            (L.ConcreteRealSpecialOrthogonalGroup ×
              L.finiteSpecialOrthogonalLatticeStabilizerSubgroup)) :=
    isCompact_univ
  have himage :=
    hcompact.image
      (continuous_subtype_val.comp e.continuous)
  change IsCompact
    ((fun x :
        L.ConcreteRealSpecialOrthogonalGroup ×
          L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
        (e x :
          L.ConcreteFullAdelicSpecialOrthogonalGroup)) '' Set.univ) at himage
  have hrange :
      (fun x :
        L.ConcreteRealSpecialOrthogonalGroup ×
          L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
          (e x : L.ConcreteFullAdelicSpecialOrthogonalGroup)) ''
          Set.univ =
        (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
          Set L.ConcreteFullAdelicSpecialOrthogonalGroup) := by
    ext g
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (e x).property
    · intro hg
      let h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
        ⟨g, hg⟩
      refine ⟨e.symm h, Set.mem_univ _, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply h)
  rw [hrange] at himage
  exact himage

/-- Every chosen left coset of the natural stabilizer is compact. -/
theorem isCompact_fullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    IsCompact (L.fullAdelicRealFiniteLatticeStabilizerCoset C) := by
  unfold fullAdelicRealFiniteLatticeStabilizerCoset
  exact
    L.isCompact_fullAdelicRealFiniteLatticeStabilizerSubgroup.image
      (continuous_const.mul continuous_id)

/-- Every chosen stabilizer coset has nonempty interior. -/
theorem fullAdelicRealFiniteLatticeStabilizerCoset_interior_nonempty
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    (interior
      (L.fullAdelicRealFiniteLatticeStabilizerCoset C)).Nonempty := by
  rw [L.isOpen_fullAdelicRealFiniteLatticeStabilizerCoset C |>.interior_eq]
  exact
    ⟨Quotient.out C,
      (L.mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff C
        (Quotient.out C)).mpr (Quotient.out_eq C)⟩

/-- The ambient differential mass of a chosen coset is the total mass of its
one-coset contribution. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_coset
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) =
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C Set.univ := by
  calc
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) =
        ((L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
          (L.fullAdelicRealFiniteLatticeStabilizerCoset C)) Set.univ := by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ =
        L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C
          Set.univ := by
      rw [L.restrict_fullAdelicSpecialOrthogonalDifferentialMeasure_coset P C]

/-- Every chosen compact-open coset has the exact internally computed
real-times-finite differential mass. -/
theorem
    fullAdelicSpecialOrthogonalDifferentialMeasure_coset_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  rw [L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset P C]
  exact
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_univ_eq_real_mul_finite
      hP C

/-- Under a positive cutoff limit, every chosen compact-open coset has
nonzero differential mass. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_coset_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) ≠ 0 := by
  rw [
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset_eq_real_mul_finite
      hP C]
  exact mul_ne_zero
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P)

/-- Under a positive cutoff limit, every chosen compact-open coset has finite
differential mass. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_coset_ne_top
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) ≠ ∞ := by
  rw [
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset_eq_real_mul_finite
      hP C]
  letI : IsFiniteMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
  exact
    (ENNReal.mul_lt_top
      IsFiniteMeasure.measure_univ_lt_top
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top
        hP).lt_top).ne

/-- The internally constructed ambient differential measure is a Haar
measure, proved directly from its compact-open stabilizer coset. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_isHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.IsHaarMeasure
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
  letI : Measure.IsMulLeftInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isMulLeftInvariant hP
  let C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
    ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
      L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
  let K := L.fullAdelicRealFiniteLatticeStabilizerCoset C
  have hK : IsCompact K :=
    L.isCompact_fullAdelicRealFiniteLatticeStabilizerCoset C
  have hK_nonempty : (interior K).Nonempty :=
    L.fullAdelicRealFiniteLatticeStabilizerCoset_interior_nonempty C
  have hK_ne_zero :
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P K ≠ 0 :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset_ne_zero hP C
  have hK_ne_top :
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P K ≠ ∞ :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset_ne_top hP C
  exact
    { lt_top_of_isCompact := fun _A hA =>
        measure_lt_top_of_isCompact_of_isMulLeftInvariant'
          hK_nonempty hK_ne_top hA
      toIsOpenPosMeasure :=
        isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK hK_ne_zero }

/-- The internally constructed ambient differential Haar measure is regular.
This uses only the general regularity instance for locally finite measures on
sigma-compact pseudometrizable spaces. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_regular
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.Regular
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
  let μ := L.fullAdelicSpecialOrthogonalDifferentialMeasure P
  have hhaar : Measure.IsHaarMeasure μ :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isHaarMeasure hP
  letI : Measure.IsHaarMeasure
      μ := hhaar
  letI : IsFiniteMeasureOnCompacts μ :=
    hhaar.toIsFiniteMeasureOnCompacts
  letI : IsLocallyFiniteMeasure μ :=
    ⟨fun x => by
      let C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
        (x :
          L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
      refine
        ⟨L.fullAdelicRealFiniteLatticeStabilizerCoset C, ?_, ?_⟩
      · exact
          (L.isOpen_fullAdelicRealFiniteLatticeStabilizerCoset C).mem_nhds
            ((L.mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff C x).mpr
              rfl)
      · exact
          (L.fullAdelicSpecialOrthogonalDifferentialMeasure_coset_ne_top
            hP C).lt_top⟩
  letI : SigmaCompactSpace
      L.ConcreteFullAdelicSpecialOrthogonalGroup := by
    let S :
        Set
          (Set L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
      Set.range L.fullAdelicRealFiniteLatticeStabilizerCoset
    refine
      SigmaCompactSpace.of_countable S
        (by
          show
            (Set.range
              L.fullAdelicRealFiniteLatticeStabilizerCoset).Countable
          exact Set.countable_range _) ?_ ?_
    · rintro _ ⟨C, rfl⟩
      exact L.isCompact_fullAdelicRealFiniteLatticeStabilizerCoset C
    · simp only [S, Set.sUnion_range]
      exact L.iUnion_fullAdelicRealFiniteLatticeStabilizerCoset
  letI : RegularSpace
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    IsTopologicalGroup.regularSpace
      L.ConcreteFullAdelicSpecialOrthogonalGroup
  letI : TopologicalSpace.PseudoMetrizableSpace
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology
      L.ConcreteFullAdelicSpecialOrthogonalGroup
  exact
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure
      μ

end PositiveDefiniteIntegralLattice
