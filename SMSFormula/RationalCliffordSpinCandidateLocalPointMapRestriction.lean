import SMSFormula.RationalCliffordSpinCandidatePlacewiseFiniteSheetHaar
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockCylinderMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Local Spin point-map pushforwards as restricted `SO` measures

The two-sheet theorems first express the pushforward on the actual image
subgroup.  Mapping that image subgroup back into the ambient `SO` group turns
its comapped differential measure into the literal restriction of the
ambient differential measure.  The same argument is recorded for the good
integral local factors used in the finite-adelic tail.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance localPointRestrictionRealPointGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) := borel _

local instance localPointRestrictionRealPointGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) := ⟨rfl⟩

local instance localPointRestrictionRealSOGroupMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

local instance localPointRestrictionRealSOGroupBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

local instance localPointRestrictionPrimeFact
    (p : ℕ) [Fact (Nat.Prime p)] : Fact (Nat.Prime p) := inferInstance

local instance localPointRestrictionPadicSOGroupMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

local instance localPointRestrictionPadicSOGroupBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

/-- Mapping a range-restricted comap measure back through the range inclusion
is literal restriction of the ambient measure.  This small measure-theoretic
lemma keeps the placewise applications independent of their concrete matrix
carrier aliases. -/
theorem map_eq_smul_restrict_range_of_map_rangeRestrict_eq_smul_comap
    {G H : Type*} [Group G] [Group H]
    [MeasurableSpace G] [MeasurableSpace H]
    (f : G →* H) (hf : Measurable f) (i : MeasurableEmbedding f.range.subtype)
    (c : ENNReal) (mu : Measure G) (nu : Measure H)
    (h : Measure.map f.rangeRestrict mu = c • Measure.comap f.range.subtype nu) :
    Measure.map f mu = c • nu.restrict (f.range : Set H) := by
  have hfr : Measurable f.rangeRestrict := Measurable.subtype_mk hf
  calc
    Measure.map f mu = Measure.map f.range.subtype
        (Measure.map f.rangeRestrict mu) := by
      rw [Measure.map_map i.measurable hfr]
      rfl
    _ = Measure.map f.range.subtype
        (c • Measure.comap f.range.subtype nu) := congrArg _ h
    _ = c • Measure.map f.range.subtype
        (Measure.comap f.range.subtype nu) := by rw [Measure.map_smul]
    _ = c • nu.restrict (Set.range f.range.subtype) := by
      rw [i.map_comap]
    _ = c • nu.restrict (f.range : Set H) := by
      congr 2
      ext y
      simp

/-- The preceding range-comap calculation with the two scalar actions used by
the normalized integral factors kept separate. -/
theorem map_eq_smul_smul_restrict_range_of_map_rangeRestrict_eq_smul_smul_comap
    {G H : Type*} [Group G] [Group H]
    [MeasurableSpace G] [MeasurableSpace H]
    (f : G →* H) (hf : Measurable f) (i : MeasurableEmbedding f.range.subtype)
    (c : ENNReal) (d : NNReal) (mu : Measure G) (nu : Measure H)
    (h : Measure.map f.rangeRestrict mu =
      c • (d • Measure.comap f.range.subtype nu)) :
    Measure.map f mu = c • (d • nu.restrict (f.range : Set H)) := by
  have hfr : Measurable f.rangeRestrict := Measurable.subtype_mk hf
  calc
    Measure.map f mu = Measure.map f.range.subtype
        (Measure.map f.rangeRestrict mu) := by
      rw [Measure.map_map i.measurable hfr]
      rfl
    _ = Measure.map f.range.subtype
        (c • (d • Measure.comap f.range.subtype nu)) := congrArg _ h
    _ = c • (d • Measure.map f.range.subtype
        (Measure.comap f.range.subtype nu)) := by
      rw [Measure.map_smul, Measure.map_smul]
    _ = c • (d • nu.restrict (Set.range f.range.subtype)) := by
      rw [i.map_comap]
    _ = c • (d • nu.restrict (f.range : Set H)) := by
      congr 3
      ext y
      simp

/-- At the real place the point-map pushforward in the ambient `SO` group is
twice the fixed differential measure restricted to the actual Spin image. -/
theorem map_realCliffordSpinCandidateChartGluedMeasure_eq_two_smul_restrict_image :
    Measure.map V.realCliffordSpinCandidateToSpecialOrthogonalHom
        V.realCliffordSpinCandidateChartGluedMeasure =
      (2 : ENNReal) •
        (show Measure V.RealSpecialOrthogonalGroup from
          V.realInvariantDifferentialGroupMeasure).restrict
          (V.realCliffordSpinCandidateToSpecialOrthogonalHom.range :
            Set V.RealSpecialOrthogonalGroup) := by
  apply map_eq_smul_restrict_range_of_map_rangeRestrict_eq_smul_comap
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ).measurable
    (V.isOpen_realCliffordSpinCandidateImage
      |>.isOpenEmbedding_subtypeVal.measurableEmbedding)
    2 V.realCliffordSpinCandidateChartGluedMeasure
    (show Measure V.RealSpecialOrthogonalGroup from
      V.realInvariantDifferentialGroupMeasure)
  simpa [realCliffordSpinCandidateImageDifferentialMeasure] using
    V.map_realCliffordSpinCandidateChartGluedMeasure_eq_two_smul_imageMeasure

/-- At every p-adic place the point-map pushforward in ambient `SO` is twice
the fixed differential measure restricted to the actual Spin image. -/
theorem map_padicCliffordSpinCandidateChartGluedMeasure_eq_two_smul_restrict_image
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
        (V.padicCliffordSpinCandidateChartGluedMeasure p) =
      (2 : ENNReal) •
        (show Measure (V.specialOrthogonalMatrixGroup ℚ_[p]) from
          V.padicInvariantDifferentialGroupMeasure p).restrict
          ((V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).range :
            Set (V.specialOrthogonalMatrixGroup ℚ_[p])) := by
  apply map_eq_smul_restrict_range_of_map_rangeRestrict_eq_smul_comap
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).measurable
    ((V.isOpen_padicCliffordSpinCandidateImage p)
      |>.isOpenEmbedding_subtypeVal.measurableEmbedding)
    2 (V.padicCliffordSpinCandidateChartGluedMeasure p)
    (show Measure (V.specialOrthogonalMatrixGroup ℚ_[p]) from
      V.padicInvariantDifferentialGroupMeasure p)
  simpa [padicCliffordSpinCandidateImageDifferentialMeasure] using
    V.map_padicCliffordSpinCandidateChartGluedMeasure_eq_two_smul_imageMeasure p

local instance localPointRestrictionHeightPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance localPointRestrictionHeightSOGroupMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) := borel _

local instance localPointRestrictionHeightSOGroupBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) := ⟨rfl⟩

end RationalQuadraticSpaceMatrix
