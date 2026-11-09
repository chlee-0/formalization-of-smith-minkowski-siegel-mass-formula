import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalSpecialOrthogonalInvariantDifferentialPlacewiseGroupMeasure

/-!
# Placewise chart measures for the Spin candidate

The real and p-adic Spin-candidate point maps are local
homeomorphisms.  This file chooses identity-centered open partial
homeomorphism charts and pulls the invariant-differential `SO`
group measures back through their exact source/target homeomorphisms.

The resulting measures live on the chart subtypes.  Their pushforwards are
exactly the restrictions of the corresponding `SO` measures; they are locally
finite and positive on every nonempty open subset of the chart.  This is the
purely topological measure transport given by the local homeomorphism
theorem.

No claim identifies these pulled-back chart measures with the absolute-value
density of the chosen Spin top differential.  That identification requires an
analytic local coordinate map and its change-of-variables theorem.
-/

noncomputable section

open MeasureTheory
open Topology
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Borel structures on the placewise Spin carriers -/

noncomputable instance realCliffordSpinCandidateGroupMeasurableSpace_chartMeasure :
    MeasurableSpace V.RealCliffordSpinCandidateGroup := borel _

noncomputable instance realCliffordSpinCandidateGroupBorelSpace_chartMeasure :
    BorelSpace V.RealCliffordSpinCandidateGroup := ⟨rfl⟩

noncomputable instance padicCliffordSpinCandidateGroupMeasurableSpace_chartMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.PadicCliffordSpinCandidateGroup p) := borel _

noncomputable instance padicCliffordSpinCandidateGroupBorelSpace_chartMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.PadicCliffordSpinCandidateGroup p) := ⟨rfl⟩

noncomputable local instance placewiseChartRealSpecialOrthogonalMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance placewiseChartRealSpecialOrthogonalBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance placewiseChartPadicSpecialOrthogonalMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance placewiseChartPadicSpecialOrthogonalBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

/-! ## Generic transport lemmas -/

private theorem isLocallyFiniteMeasure_comap_openEmbedding
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : IsOpenEmbedding f) (μ : Measure Y)
    [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (Measure.comap f μ) := by
  refine ⟨fun x ↦ ?_⟩
  rcases μ.exists_isOpen_measure_lt_top (f x) with
    ⟨U, hfxU, hU, hμU⟩
  refine ⟨f ⁻¹' U, (hU.preimage hf.continuous).mem_nhds hfxU, ?_⟩
  rw [hf.measurableEmbedding.comap_apply]
  exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset f U)) hμU

private theorem isLocallyFiniteMeasure_map_homeomorph
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (Measure.map e μ) := by
  refine ⟨fun y ↦ ?_⟩
  rcases μ.exists_isOpen_measure_lt_top (e.symm y) with
    ⟨U, hyU, hU, hμU⟩
  refine ⟨e.symm ⁻¹' U,
    (hU.preimage e.symm.continuous).mem_nhds hyU, ?_⟩
  rw [Measure.map_apply e.measurable
    (hU.preimage e.symm.continuous).measurableSet]
  have hpreimage : e ⁻¹' (e.symm ⁻¹' U) = U := by
    ext x
    simp
  rw [hpreimage]
  exact hμU

/-! ## Identity-centered local charts -/

/-- A chosen identity-centered real chart whose underlying function is the
Spin-candidate point map. -/
noncomputable def realCliffordSpinCandidateIdentityChart :
    OpenPartialHomeomorph
      V.RealCliffordSpinCandidateGroup V.RealSpecialOrthogonalGroup :=
  Classical.choose
    (V.exists_realCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
      V.realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap)

@[simp]
theorem one_mem_realCliffordSpinCandidateIdentityChart_source :
    (1 : V.RealCliffordSpinCandidateGroup) ∈
      V.realCliffordSpinCandidateIdentityChart.source :=
  (Classical.choose_spec
    (V.exists_realCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
      V.realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap)).1

theorem realCliffordSpinCandidateIdentityChart_coe :
    (V.realCliffordSpinCandidateToSpecialOrthogonalHom :
        V.RealCliffordSpinCandidateGroup → V.RealSpecialOrthogonalGroup) =
      V.realCliffordSpinCandidateIdentityChart :=
  (Classical.choose_spec
    (V.exists_realCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
      V.realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap)).2

/-- A chosen identity-centered p-adic chart whose underlying function is the
Spin-candidate point map. -/
noncomputable def padicCliffordSpinCandidateIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (V.PadicCliffordSpinCandidateGroup p)
      (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  Classical.choose
    (V.exists_padicCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
      p (V.padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap p))

@[simp]
theorem one_mem_padicCliffordSpinCandidateIdentityChart_source
    (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : V.PadicCliffordSpinCandidateGroup p) ∈
      (V.padicCliffordSpinCandidateIdentityChart p).source :=
  (Classical.choose_spec
    (V.exists_padicCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
      p (V.padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap p))).1

theorem padicCliffordSpinCandidateIdentityChart_coe
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] :
        V.PadicCliffordSpinCandidateGroup p →
          V.specialOrthogonalMatrixGroup ℚ_[p]) =
      V.padicCliffordSpinCandidateIdentityChart p :=
  (Classical.choose_spec
    (V.exists_padicCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
      p (V.padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap p))).2

/-! ## Real chart measure -/

/-- The invariant-differential `SO(ℝ)` measure restricted, by comap, to the
target subtype of the chosen Spin chart. -/
noncomputable def realCliffordSpinCandidateIdentityChartTargetMeasure :
    Measure V.realCliffordSpinCandidateIdentityChart.target :=
  Measure.comap Subtype.val V.realInvariantDifferentialGroupMeasure

/-- The real Spin chart-source measure obtained by exact inverse transport
from the restricted `SO(ℝ)` measure. -/
noncomputable def realCliffordSpinCandidateIdentityChartSourceMeasure :
    Measure V.realCliffordSpinCandidateIdentityChart.source :=
  Measure.map
    V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm
    V.realCliffordSpinCandidateIdentityChartTargetMeasure

/-- The chosen real chart sends its source measure exactly to its target
measure. -/
theorem map_realCliffordSpinCandidateIdentityChartSourceMeasure :
    Measure.map
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
        V.realCliffordSpinCandidateIdentityChartSourceMeasure =
      V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
  rw [realCliffordSpinCandidateIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.toMeasurableEquiv

/-- Inverse transport from the real chart target is literally the chosen
source measure. -/
theorem map_realCliffordSpinCandidateIdentityChartTargetMeasure_symm :
    Measure.map
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm
        V.realCliffordSpinCandidateIdentityChartTargetMeasure =
      V.realCliffordSpinCandidateIdentityChartSourceMeasure :=
  rfl

/-- Inclusion of the chosen real target chart recovers the literal
restriction of the full invariant-differential `SO(ℝ)` measure. -/
theorem map_realCliffordSpinCandidateIdentityChartTargetMeasure_subtype :
    Measure.map Subtype.val
        V.realCliffordSpinCandidateIdentityChartTargetMeasure =
      V.realInvariantDifferentialGroupMeasure.restrict
        V.realCliffordSpinCandidateIdentityChart.target := by
  rw [realCliffordSpinCandidateIdentityChartTargetMeasure]
  exact map_comap_subtype_coe
    V.realCliffordSpinCandidateIdentityChart.open_target.measurableSet _

/-- On the chosen source subtype, the literal real Spin-to-`SO` point map
pushes the chart measure to the restriction of the canonical `SO` measure. -/
theorem map_realCliffordSpinCandidateIdentityChartSourceMeasure_pointMap :
    Measure.map
        (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
          V.realCliffordSpinCandidateToSpecialOrthogonalHom x)
        V.realCliffordSpinCandidateIdentityChartSourceMeasure =
      V.realInvariantDifferentialGroupMeasure.restrict
        V.realCliffordSpinCandidateIdentityChart.target := by
  calc
    Measure.map
        (fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
          V.realCliffordSpinCandidateToSpecialOrthogonalHom x)
        V.realCliffordSpinCandidateIdentityChartSourceMeasure =
        Measure.map Subtype.val
          (Measure.map
            V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget
            V.realCliffordSpinCandidateIdentityChartSourceMeasure) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.measurable]
      congr 1
      funext x
      change V.realCliffordSpinCandidateToSpecialOrthogonalHom x =
        V.realCliffordSpinCandidateIdentityChart x
      rw [V.realCliffordSpinCandidateIdentityChart_coe]
    _ = Measure.map Subtype.val
        V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
      rw [V.map_realCliffordSpinCandidateIdentityChartSourceMeasure]
    _ = V.realInvariantDifferentialGroupMeasure.restrict
        V.realCliffordSpinCandidateIdentityChart.target :=
      V.map_realCliffordSpinCandidateIdentityChartTargetMeasure_subtype

set_option backward.isDefEq.respectTransparency false in
/-- The restricted target measure is locally finite. -/
theorem realCliffordSpinCandidateIdentityChartTargetMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure
      V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
  letI : BorelSpace V.RealSpecialOrthogonalGroup := ⟨rfl⟩
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  letI : IsLocallyFiniteMeasure V.realInvariantDifferentialGroupMeasure :=
    by
      simpa [realInvariantDifferentialGroupMeasure] using
        (PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
          V.pairingMatrix V.form_symm V.form_det_ne_zero)
  exact isLocallyFiniteMeasure_comap_openEmbedding
    (X := V.realCliffordSpinCandidateIdentityChart.target)
    (Y := V.RealSpecialOrthogonalGroup) Subtype.val
    V.realCliffordSpinCandidateIdentityChart.open_target.isOpenEmbedding_subtypeVal
    V.realInvariantDifferentialGroupMeasure

/-- The real chart-source measure is locally finite. -/
theorem realCliffordSpinCandidateIdentityChartSourceMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure
      V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  letI : IsLocallyFiniteMeasure
      V.realCliffordSpinCandidateIdentityChartTargetMeasure :=
    V.realCliffordSpinCandidateIdentityChartTargetMeasure_isLocallyFinite
  rw [realCliffordSpinCandidateIdentityChartSourceMeasure]
  exact isLocallyFiniteMeasure_map_homeomorph
    V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm
    V.realCliffordSpinCandidateIdentityChartTargetMeasure

/-- The restricted real target measure is positive on every nonempty open
set. -/
theorem realCliffordSpinCandidateIdentityChartTargetMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure
      V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  rw [realCliffordSpinCandidateIdentityChartTargetMeasure]
  exact Measure.IsOpenPosMeasure.comap V.realInvariantDifferentialGroupMeasure
    V.realCliffordSpinCandidateIdentityChart.open_target.isOpenEmbedding_subtypeVal

/-- The real chart-source measure is positive on every nonempty open set. -/
theorem realCliffordSpinCandidateIdentityChartSourceMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure
      V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  letI : Measure.IsOpenPosMeasure
      V.realCliffordSpinCandidateIdentityChartTargetMeasure :=
    V.realCliffordSpinCandidateIdentityChartTargetMeasure_isOpenPosMeasure
  rw [realCliffordSpinCandidateIdentityChartSourceMeasure]
  exact
    V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm.continuous
      |>.isOpenPosMeasure_map
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm.surjective

/-! ## P-adic chart measures -/

/-- The invariant-differential `SO(ℚ_p)` measure restricted, by comap, to the
target subtype of the chosen Spin chart. -/
noncomputable def padicCliffordSpinCandidateIdentityChartTargetMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordSpinCandidateIdentityChart p).target :=
  Measure.comap Subtype.val (V.padicInvariantDifferentialGroupMeasure p)

/-- The p-adic Spin chart-source measure obtained by exact inverse transport
from the restricted `SO(ℚ_p)` measure. -/
noncomputable def padicCliffordSpinCandidateIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordSpinCandidateIdentityChart p).source :=
  Measure.map
    (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.symm
    (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p)

/-- The chosen p-adic chart sends its source measure exactly to its target
measure. -/
theorem map_padicCliffordSpinCandidateIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) =
      V.padicCliffordSpinCandidateIdentityChartTargetMeasure p := by
  rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.toMeasurableEquiv

/-- Inverse transport from the p-adic chart target is literally the chosen
source measure. -/
theorem map_padicCliffordSpinCandidateIdentityChartTargetMeasure_symm
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.symm
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) =
      V.padicCliffordSpinCandidateIdentityChartSourceMeasure p :=
  rfl

/-- Inclusion of the chosen p-adic target chart recovers the literal
restriction of the full invariant-differential `SO(ℚ_p)` measure. -/
theorem map_padicCliffordSpinCandidateIdentityChartTargetMeasure_subtype
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) =
      (V.padicInvariantDifferentialGroupMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).target := by
  rw [padicCliffordSpinCandidateIdentityChartTargetMeasure]
  exact map_comap_subtype_coe
    (V.padicCliffordSpinCandidateIdentityChart p).open_target.measurableSet _

/-- On the chosen source subtype, the literal p-adic Spin-to-`SO` point map
pushes the chart measure to the restriction of the canonical `SO` measure. -/
theorem map_padicCliffordSpinCandidateIdentityChartSourceMeasure_pointMap
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (fun x : (V.padicCliffordSpinCandidateIdentityChart p).source ↦
          V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x)
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) =
      (V.padicInvariantDifferentialGroupMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).target := by
  calc
    Measure.map
        (fun x : (V.padicCliffordSpinCandidateIdentityChart p).source ↦
          V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x)
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) =
        Measure.map Subtype.val
          (Measure.map
            (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget
            (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.measurable]
      congr 1
      funext x
      change V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x =
        V.padicCliffordSpinCandidateIdentityChart p x
      rw [V.padicCliffordSpinCandidateIdentityChart_coe p]
    _ = Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      rw [V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure p]
    _ = (V.padicInvariantDifferentialGroupMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).target :=
      V.map_padicCliffordSpinCandidateIdentityChartTargetMeasure_subtype p

set_option backward.isDefEq.respectTransparency false in
/-- The restricted p-adic target measure is locally finite. -/
theorem padicCliffordSpinCandidateIdentityChartTargetMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyFiniteMeasure
      (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
  letI : BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  letI : IsLocallyFiniteMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    by
      simpa [padicInvariantDifferentialGroupMeasure] using
        (PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_isLocallyFinite
          p n V.pairingMatrix V.form_symm V.form_det_ne_zero)
  exact isLocallyFiniteMeasure_comap_openEmbedding
    (X := (V.padicCliffordSpinCandidateIdentityChart p).target)
    (Y := V.specialOrthogonalMatrixGroup ℚ_[p]) Subtype.val
    (V.padicCliffordSpinCandidateIdentityChart p).open_target.isOpenEmbedding_subtypeVal
    (V.padicInvariantDifferentialGroupMeasure p)

/-- The p-adic chart-source measure is locally finite. -/
theorem padicCliffordSpinCandidateIdentityChartSourceMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyFiniteMeasure
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
  letI : IsLocallyFiniteMeasure
      (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) :=
    V.padicCliffordSpinCandidateIdentityChartTargetMeasure_isLocallyFinite p
  rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
  exact isLocallyFiniteMeasure_map_homeomorph
    (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.symm
    (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p)

/-- The restricted p-adic target measure is positive on every nonempty open
set. -/
theorem padicCliffordSpinCandidateIdentityChartTargetMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsOpenPosMeasure
      (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  rw [padicCliffordSpinCandidateIdentityChartTargetMeasure]
  exact Measure.IsOpenPosMeasure.comap
    (V.padicInvariantDifferentialGroupMeasure p)
    (V.padicCliffordSpinCandidateIdentityChart p).open_target.isOpenEmbedding_subtypeVal

/-- The p-adic chart-source measure is positive on every nonempty open set. -/
theorem padicCliffordSpinCandidateIdentityChartSourceMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsOpenPosMeasure
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
  letI : Measure.IsOpenPosMeasure
      (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) :=
    V.padicCliffordSpinCandidateIdentityChartTargetMeasure_isOpenPosMeasure p
  rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
  exact
    (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.symm.continuous
      |>.isOpenPosMeasure_map
        (V.padicCliffordSpinCandidateIdentityChart p).toHomeomorphSourceTarget.symm.surjective

end RationalQuadraticSpaceMatrix
