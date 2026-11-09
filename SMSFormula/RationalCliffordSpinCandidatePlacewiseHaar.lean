import SMSFormula.RationalCliffordSpinCandidatePlacewiseChartMeasureGluing

/-!
# Placewise Haar measures for the Spin candidate

The translated-chart construction gives a full real or p-adic Spin
measure whose restriction to every translated chart is the prescribed local
measure.  This file proves that the glued measure is left invariant.

The argument is generic.  Left multiplication carries the source chart at
`g` to the source chart at `a * g`, and it carries the corresponding ambient
source measure to the ambient source measure at `a * g`.  The exact chart
recovery theorem therefore identifies every chart restriction of the
left-translated glued measure.  The countable disjoint chart cover then
promotes these local equalities to equality of the full measures.

Together with the local-finiteness and open-positivity theorems, this shows
that the real and p-adic glued measures are Haar measures.  This file does
not identify their local chart densities with the absolute-value densities of
the chosen Spin top forms; that needs a separate derivative and
change-of-variables argument.
-/

noncomputable section

open MeasureTheory
open Topology

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-! ## Translation of sources and their measures -/

/-- Left multiplication identifies the chart source at `g` with the chart
source at `a * g`. -/
def sourceLeftHomeomorphBetween (e : OpenPartialHomeomorph G H)
    (a g : G) : source e g ≃ₜ source e (a * g) where
  toFun x := ⟨a * x.1, by
    change (a * g)⁻¹ * (a * x.1) ∈ e.source
    have hx : g⁻¹ * x.1 ∈ e.source := x.2
    simpa [mul_assoc] using hx⟩
  invFun x := ⟨a⁻¹ * x.1, by
    change g⁻¹ * (a⁻¹ * x.1) ∈ e.source
    have hx : (a * g)⁻¹ * x.1 ∈ e.source := x.2
    simpa [mul_assoc] using hx⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The literal left multiplication map sends a translated source exactly to
the correspondingly translated source. -/
theorem image_source_mulLeft (e : OpenPartialHomeomorph G H)
    (a g : G) :
    Homeomorph.mulLeft a '' source e g = source e (a * g) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (a * g)⁻¹ * (a * y) ∈ e.source
    have hy' : g⁻¹ * y ∈ e.source := hy
    simpa [mul_assoc] using hy'
  · intro hx
    refine ⟨a⁻¹ * x, ?_, by simp⟩
    change g⁻¹ * (a⁻¹ * x) ∈ e.source
    have hx' : (a * g)⁻¹ * x ∈ e.source := hx
    simpa [mul_assoc] using hx'

/-- The preimage form of translated-source covariance. -/
theorem preimage_source_mulLeft (e : OpenPartialHomeomorph G H)
    (a g : G) :
    Homeomorph.mulLeft a ⁻¹' source e (a * g) = source e g := by
  ext x
  change (a * g)⁻¹ * (a * x) ∈ e.source ↔ g⁻¹ * x ∈ e.source
  simp [mul_assoc]

/-- Left multiplication transports the local source measure at `g` to the
local source measure at `a * g`. -/
theorem map_sourceMeasure_sourceLeftHomeomorphBetween
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (a g : G) (μ : Measure H) [Measure.IsMulLeftInvariant μ] :
    Measure.map (sourceLeftHomeomorphBetween e a g)
        (sourceMeasure f e g μ) =
      sourceMeasure f e (a * g) μ := by
  calc
    Measure.map (sourceLeftHomeomorphBetween e a g)
        (sourceMeasure f e g μ) =
        Measure.map (sourceLeftHomeomorphBetween e a g)
          (Measure.map (sourceLeftHomeomorph e g)
            (identitySourceMeasure e μ)) := by
      rw [map_identitySourceMeasure_sourceLeftHomeomorph f e g μ]
    _ = Measure.map (sourceLeftHomeomorph e (a * g))
        (identitySourceMeasure e μ) := by
      rw [Measure.map_map
        (sourceLeftHomeomorphBetween e a g).measurable
        (sourceLeftHomeomorph e g).measurable]
      congr 1
      funext x
      apply Subtype.ext
      simp [sourceLeftHomeomorphBetween, sourceLeftHomeomorph, mul_assoc]
    _ = sourceMeasure f e (a * g) μ :=
      map_identitySourceMeasure_sourceLeftHomeomorph f e (a * g) μ

/-- The ambient version of the preceding local translation theorem. -/
theorem map_ambientSourceMeasure_mulLeft
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (a g : G) (μ : Measure H) [Measure.IsMulLeftInvariant μ] :
    Measure.map (Homeomorph.mulLeft a)
        (ambientSourceMeasure f e g μ) =
      ambientSourceMeasure f e (a * g) μ := by
  let E := sourceLeftHomeomorphBetween e a g
  let jg : source e g → G := Subtype.val
  let jag : source e (a * g) → G := Subtype.val
  calc
    Measure.map (Homeomorph.mulLeft a)
        (ambientSourceMeasure f e g μ) =
        Measure.map (Homeomorph.mulLeft a)
          (Measure.map jg (sourceMeasure f e g μ)) := rfl
    _ = Measure.map (Homeomorph.mulLeft a ∘ jg)
        (sourceMeasure f e g μ) := by
      rw [Measure.map_map (Homeomorph.mulLeft a).measurable
        continuous_subtype_val.measurable]
    _ = Measure.map (jag ∘ E) (sourceMeasure f e g μ) := by
      congr 1
    _ = Measure.map jag
        (Measure.map E (sourceMeasure f e g μ)) := by
      rw [Measure.map_map continuous_subtype_val.measurable E.measurable]
    _ = Measure.map jag (sourceMeasure f e (a * g) μ) := by
      rw [map_sourceMeasure_sourceLeftHomeomorphBetween f e a g μ]
    _ = ambientSourceMeasure f e (a * g) μ := rfl

/-! ## Global invariance of the glued measure -/

private theorem measure_eq_sum_restrict_coverPiece
    (e : OpenPartialHomeomorph G H) (hone : (1 : G) ∈ e.source)
    (ν : Measure G) :
    ν = Measure.sum (fun k ↦ ν.restrict (coverPiece e k)) := by
  calc
    ν = ν.restrict Set.univ := Measure.restrict_univ.symm
    _ = ν.restrict (⋃ k, coverPiece e k) := by
      rw [iUnion_coverPiece e hone]
    _ = Measure.sum (fun k ↦ ν.restrict (coverPiece e k)) :=
      Measure.restrict_iUnion (pairwiseDisjoint_coverPiece e)
        (measurableSet_coverPiece e)

/-- Measures agreeing after restriction to every translated source are equal
globally. -/
theorem measure_eq_of_restrict_source_eq
    (e : OpenPartialHomeomorph G H) (hone : (1 : G) ∈ e.source)
    {ν ν' : Measure G}
    (h : ∀ g, ν.restrict (source e g) = ν'.restrict (source e g)) :
    ν = ν' := by
  rw [measure_eq_sum_restrict_coverPiece e hone ν,
    measure_eq_sum_restrict_coverPiece e hone ν']
  congr 1
  funext k
  let g := coverCenter e k
  let P := coverPiece e k
  let U := source e g
  have hP : MeasurableSet P := measurableSet_coverPiece e k
  have hPU : P ⊆ U := coverPiece_subset_source e k
  calc
    ν.restrict P = (ν.restrict U).restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact (Set.inter_eq_left.mpr hPU).symm
    _ = (ν'.restrict U).restrict P := by rw [h g]
    _ = ν'.restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_eq_left.mpr hPU

/-- Every translated chart restriction of a left translate of the glued
measure is the prescribed chart measure. -/
theorem restrict_map_mulLeft_gluedMeasure_source
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ]
    (a g : G) :
    (Measure.map (Homeomorph.mulLeft a) (gluedMeasure f e μ)).restrict
        (source e (a * g)) =
      ambientSourceMeasure f e (a * g) μ := by
  have hU : MeasurableSet (source e (a * g)) :=
    (isOpen_source e (a * g)).measurableSet
  calc
    (Measure.map (Homeomorph.mulLeft a) (gluedMeasure f e μ)).restrict
        (source e (a * g)) =
        Measure.map (Homeomorph.mulLeft a)
          ((gluedMeasure f e μ).restrict (source e g)) := by
      rw [Measure.restrict_map (Homeomorph.mulLeft a).measurable hU,
        preimage_source_mulLeft e a g]
    _ = Measure.map (Homeomorph.mulLeft a)
        (ambientSourceMeasure f e g μ) := by
      rw [restrict_gluedMeasure_source f e hfe hone μ g]
    _ = ambientSourceMeasure f e (a * g) μ :=
      map_ambientSourceMeasure_mulLeft f e a g μ

/-- The chart-glued measure is globally left invariant. -/
theorem gluedMeasure_isMulLeftInvariant
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ] :
    Measure.IsMulLeftInvariant (gluedMeasure f e μ) := by
  refine ⟨fun a ↦ ?_⟩
  change Measure.map (Homeomorph.mulLeft a) (gluedMeasure f e μ) =
    gluedMeasure f e μ
  apply measure_eq_of_restrict_source_eq e hone
  intro h
  let g := a⁻¹ * h
  have hag : a * g = h := by simp [g]
  calc
    (Measure.map (Homeomorph.mulLeft a) (gluedMeasure f e μ)).restrict
        (source e h) =
        ambientSourceMeasure f e h μ := by
      rw [← hag]
      exact restrict_map_mulLeft_gluedMeasure_source
        f e hfe hone μ a g
    _ = (gluedMeasure f e μ).restrict (source e h) :=
      (restrict_gluedMeasure_source f e hfe hone μ h).symm

/-- Local finiteness, open positivity, and target left invariance package the
glued source measure as a Haar measure. -/
theorem gluedMeasure_isHaarMeasure
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ]
    (hloc : IsLocallyFiniteMeasure (gluedMeasure f e μ))
    (hpos : Measure.IsOpenPosMeasure (gluedMeasure f e μ)) :
    Measure.IsHaarMeasure (gluedMeasure f e μ) := by
  letI : IsLocallyFiniteMeasure (gluedMeasure f e μ) := hloc
  letI : IsFiniteMeasureOnCompacts (gluedMeasure f e μ) :=
    ⟨fun _K hK ↦ hK.measure_lt_top_of_nhdsWithin fun _ _ ↦
      (gluedMeasure f e μ).finiteAt_nhdsWithin _ _⟩
  exact
    { toIsMulLeftInvariant :=
        gluedMeasure_isMulLeftInvariant f e hfe hone μ
      toIsOpenPosMeasure := hpos }

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

open MeasureTheory.TranslatedHomChart

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance placewiseHaarRealSpecialOrthogonalMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance placewiseHaarRealSpecialOrthogonalBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance placewiseHaarPadicSpecialOrthogonalMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance placewiseHaarPadicSpecialOrthogonalBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

local instance placewiseHaarRealCarrierBorelSpace :
    BorelSpace V.RealSpecialOrthogonalGroup := ⟨rfl⟩

local instance placewiseHaarPadicCarrierBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

/-! ## Real Haar measure -/

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordSpinCandidateChartGluedMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant
      V.realCliffordSpinCandidateChartGluedMeasure := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  exact gluedMeasure_isMulLeftInvariant
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe
    V.one_mem_realCliffordSpinCandidateIdentityChart_source
    V.realInvariantDifferentialGroupMeasure

theorem realCliffordSpinCandidateChartGluedMeasure_isFiniteOnCompacts :
    IsFiniteMeasureOnCompacts
      V.realCliffordSpinCandidateChartGluedMeasure := by
  letI : IsLocallyFiniteMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
  exact ⟨fun _K hK ↦ hK.measure_lt_top_of_nhdsWithin fun _ _ ↦
    V.realCliffordSpinCandidateChartGluedMeasure.finiteAt_nhdsWithin _ _⟩

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure :
    Measure.IsHaarMeasure
      V.realCliffordSpinCandidateChartGluedMeasure := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  exact gluedMeasure_isHaarMeasure
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe
    V.one_mem_realCliffordSpinCandidateIdentityChart_source
    V.realInvariantDifferentialGroupMeasure
    V.realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
    V.realCliffordSpinCandidateChartGluedMeasure_isOpenPosMeasure

/-! ## P-adic Haar measures -/

set_option backward.isDefEq.respectTransparency false in
theorem padicCliffordSpinCandidateChartGluedMeasure_isMulLeftInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulLeftInvariant
      (V.padicCliffordSpinCandidateChartGluedMeasure p) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  exact gluedMeasure_isMulLeftInvariant
    (G := V.PadicCliffordSpinCandidateGroup p)
    (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
    (V.padicInvariantDifferentialGroupMeasure p)

theorem padicCliffordSpinCandidateChartGluedMeasure_isFiniteOnCompacts
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsFiniteMeasureOnCompacts
      (V.padicCliffordSpinCandidateChartGluedMeasure p) := by
  letI : IsLocallyFiniteMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isLocallyFinite p
  exact ⟨fun _K hK ↦ hK.measure_lt_top_of_nhdsWithin fun _ _ ↦
    (V.padicCliffordSpinCandidateChartGluedMeasure p).finiteAt_nhdsWithin _ _⟩

set_option backward.isDefEq.respectTransparency false in
theorem padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  exact gluedMeasure_isHaarMeasure
    (G := V.PadicCliffordSpinCandidateGroup p)
    (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
    (V.padicInvariantDifferentialGroupMeasure p)
    (V.padicCliffordSpinCandidateChartGluedMeasure_isLocallyFinite p)
    (V.padicCliffordSpinCandidateChartGluedMeasure_isOpenPosMeasure p)

end RationalQuadraticSpaceMatrix
