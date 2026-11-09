import SMSFormula.RationalCliffordGeneralSpinPlacewiseTranslatedDifferentialChart
import SMSFormula.RationalCliffordSpinCandidatePlacewiseHaar

/-!
# Placewise horizontal Haar measures on intrinsic general Spin

The translated real and p-adic `(nu, pi)` charts carry compatible source
measures.  This file glues them across a countable translated atlas and proves
that the resulting ambient intrinsic-`GSpin` measures are Haar measures.

Their scale is not chosen by Haar uniqueness: on the identity chart the glued
measure recovers the inverse transport of the literal product

`Measure.haar(K^*) x invariantDifferentialSO(K)`.

Thus these are the actual placewise horizontal differential measures needed
for the common crossed quotient.  No adelic restricted product or quotient
disintegration is constructed here.
-/

noncomputable section

open MeasureTheory
open Topology

namespace RationalQuadraticSpaceMatrix

open MeasureTheory.TranslatedHomChart

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1200000

noncomputable local instance horizontalHaarRealSchemeSOMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance horizontalHaarRealSchemeSOBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance horizontalHaarPadicSchemeSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance horizontalHaarPadicSchemeSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

noncomputable local instance horizontalHaarRealTargetSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) := borel _

noncomputable local instance horizontalHaarRealTargetSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) := ⟨rfl⟩

noncomputable local instance horizontalHaarPadicTargetSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

noncomputable local instance horizontalHaarPadicTargetSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

local instance horizontalHaarRealSchemeSOIsTopologicalGroup :
    IsTopologicalGroup (V.specialOrthogonalMatrixGroup ℝ) := by
  change IsTopologicalGroup
    (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℝ)))
  infer_instance

/-! ## Countability of the local intrinsic carriers -/

noncomputable instance realCliffordGeneralSpinGroupSecondCountableTopology_horizontal :
    SecondCountableTopology (V.CliffordGeneralSpinIntrinsicPoint ℝ) := by
  letI : SecondCountableTopology (Finset (Fin n) → ℝ) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact (V.cliffordGeneralSpinPointCoordinateMap_isEmbedding ℝ)
    |>.secondCountableTopology

noncomputable instance padicCliffordGeneralSpinGroupSecondCountableTopology_horizontal
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := by
  letI : SecondCountableTopology (Finset (Fin n) → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact (V.cliffordGeneralSpinPointCoordinateMap_isEmbedding ℚ_[p])
    |>.secondCountableTopology

/-! ## Generic local transport helpers -/

private theorem isLocallyFiniteMeasure_comap_openEmbedding
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : IsOpenEmbedding f) (mu : Measure Y)
    [IsLocallyFiniteMeasure mu] :
    IsLocallyFiniteMeasure (Measure.comap f mu) := by
  refine ⟨fun x ↦ ?_⟩
  rcases mu.exists_isOpen_measure_lt_top (f x) with
    ⟨U, hfxU, hU, hmuU⟩
  refine ⟨f ⁻¹' U, (hU.preimage hf.continuous).mem_nhds hfxU, ?_⟩
  rw [hf.measurableEmbedding.comap_apply]
  exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset f U)) hmuU

private theorem isLocallyFiniteMeasure_map_homeomorph
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (E : X ≃ₜ Y) (mu : Measure X) [IsLocallyFiniteMeasure mu] :
    IsLocallyFiniteMeasure (Measure.map E mu) := by
  refine ⟨fun y ↦ ?_⟩
  rcases mu.exists_isOpen_measure_lt_top (E.symm y) with
    ⟨U, hyU, hU, hmuU⟩
  refine ⟨E.symm ⁻¹' U,
    (hU.preimage E.symm.continuous).mem_nhds hyU, ?_⟩
  rw [Measure.map_apply E.measurable
    (hU.preimage E.symm.continuous).measurableSet]
  have hpreimage : E ⁻¹' (E.symm ⁻¹' U) = U := by
    ext x
    simp
  rw [hpreimage]
  exact hmuU

/-- The generic glued measure recovers the prescribed identity-source
measure on the literal identity chart, not merely on a propositionally equal
translate centered at `1`. -/
private theorem restrict_gluedMeasure_identitySource
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H]
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source)
    (mu : Measure H) [Measure.IsMulLeftInvariant mu] :
    (gluedMeasure f e mu).restrict e.source =
      Measure.map Subtype.val (identitySourceMeasure e mu) := by
  have hrest := restrict_gluedMeasure_source f e hfe hone mu (1 : G)
  have hsource : source e (1 : G) = e.source := by
    ext x
    simp [source]
  have hleft := map_identitySourceMeasure_sourceLeftHomeomorph
    f e (1 : G) mu
  have hfun :
      (Subtype.val : source e (1 : G) → G) ∘ sourceLeftHomeomorph e (1 : G) =
        (Subtype.val : e.source → G) := by
    funext x
    simp [sourceLeftHomeomorph]
  calc
    (gluedMeasure f e mu).restrict e.source =
        (gluedMeasure f e mu).restrict (source e (1 : G)) := by
      rw [hsource]
    _ = Measure.map Subtype.val (sourceMeasure f e (1 : G) mu) := hrest
    _ = Measure.map Subtype.val (identitySourceMeasure e mu) := by
      rw [← hleft, Measure.map_map continuous_subtype_val.measurable
        (sourceLeftHomeomorph e (1 : G)).measurable, hfun]

/-! ## Product Haar normalizations -/

theorem realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure :
    Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SFinite V.realInvariantDifferentialGroupMeasure := by
    infer_instance
  exact Measure.prod.instIsHaarMeasure
    (Measure.haar : Measure ℝˣ) V.realInvariantDifferentialGroupMeasure

theorem padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SFinite (V.padicInvariantDifferentialGroupMeasure p) := by
    infer_instance
  exact Measure.prod.instIsHaarMeasure
    (Measure.haar : Measure ℚ_[p]ˣ)
    (V.padicInvariantDifferentialGroupMeasure p)

/-! ## Identity and translated source regularity -/

theorem realCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure
      (identitySourceMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  letI : IsLocallyFiniteMeasure
      (identityTargetMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) :=
    isLocallyFiniteMeasure_comap_openEmbedding Subtype.val
      V.realCliffordGeneralSpinCentralFiberIdentityChart.open_target.isOpenEmbedding_subtypeVal
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
  rw [identitySourceMeasure]
  exact isLocallyFiniteMeasure_map_homeomorph
    V.realCliffordGeneralSpinCentralFiberIdentityChart.toHomeomorphSourceTarget.symm
    (identityTargetMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure)

theorem realCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure
      (identitySourceMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  letI : Measure.IsOpenPosMeasure
      (identityTargetMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) := by
    rw [identityTargetMeasure]
    exact Measure.IsOpenPosMeasure.comap
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
      V.realCliffordGeneralSpinCentralFiberIdentityChart.open_target.isOpenEmbedding_subtypeVal
  rw [identitySourceMeasure]
  exact
    V.realCliffordGeneralSpinCentralFiberIdentityChart.toHomeomorphSourceTarget.symm.continuous
      |>.isOpenPosMeasure_map
        V.realCliffordGeneralSpinCentralFiberIdentityChart.toHomeomorphSourceTarget.symm.surjective

theorem padicCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyFiniteMeasure
      (identitySourceMeasure
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  letI : IsLocallyFiniteMeasure
      (identityTargetMeasure
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) :=
    isLocallyFiniteMeasure_comap_openEmbedding Subtype.val
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_target.isOpenEmbedding_subtypeVal
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
  rw [identitySourceMeasure]
  exact isLocallyFiniteMeasure_map_homeomorph
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).toHomeomorphSourceTarget.symm
    (identityTargetMeasure
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p))

theorem padicCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsOpenPosMeasure
      (identitySourceMeasure
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  letI : Measure.IsOpenPosMeasure
      (identityTargetMeasure
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) := by
    rw [identityTargetMeasure]
    exact Measure.IsOpenPosMeasure.comap
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_target.isOpenEmbedding_subtypeVal
  rw [identitySourceMeasure]
  exact
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).toHomeomorphSourceTarget.symm.continuous
      |>.isOpenPosMeasure_map
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).toHomeomorphSourceTarget.symm.surjective

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isLocallyFinite
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    IsLocallyFiniteMeasure
      (V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure g) := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  letI : IsLocallyFiniteMeasure
      (identitySourceMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) :=
    V.realCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isLocallyFinite
  exact sourceMeasure_isLocallyFinite_of_identity
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart g
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isOpenPosMeasure
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    Measure.IsOpenPosMeasure
      (V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure g) := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  letI : Measure.IsOpenPosMeasure
      (identitySourceMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) :=
    V.realCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isOpenPosMeasure
  exact sourceMeasure_isOpenPosMeasure_of_identity
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart g
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

theorem padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    IsLocallyFiniteMeasure
      (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure p g) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  letI : IsLocallyFiniteMeasure
      (identitySourceMeasure
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) :=
    V.padicCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isLocallyFinite p
  exact sourceMeasure_isLocallyFinite_of_identity
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

theorem padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    Measure.IsOpenPosMeasure
      (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure p g) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  letI : Measure.IsOpenPosMeasure
      (identitySourceMeasure
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) :=
    V.padicCliffordGeneralSpinCentralFiberIdentitySourceMeasure_isOpenPosMeasure p
  exact sourceMeasure_isOpenPosMeasure_of_identity
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

/-! ## Glued ambient Haar measures -/

set_option backward.isDefEq.respectTransparency false in
/-- The real horizontal differential Haar measure on intrinsic `GSpin`. -/
noncomputable def realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :
    Measure (V.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  gluedMeasure
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

/-- The p-adic horizontal differential Haar measure on intrinsic `GSpin`. -/
noncomputable def padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  gluedMeasure (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

set_option backward.isDefEq.respectTransparency false in
theorem restrict_realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_source
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
        (V.RealCliffordGeneralSpinTranslatedDifferentialChartSource g) =
      Measure.map Subtype.val
        (V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure g) :=
  restrict_gluedMeasure_source
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure g

theorem restrict_padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_source
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (V.PadicCliffordGeneralSpinTranslatedDifferentialChartSource p g) =
      Measure.map Subtype.val
        (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure p g) :=
  restrict_gluedMeasure_source
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
    (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) g

set_option backward.isDefEq.respectTransparency false in
/-- On the literal real identity chart, the ambient glued measure recovers
the already normalized intrinsic chart measure. -/
theorem restrict_realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity :
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source =
      Measure.map Subtype.val
        V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  calc
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source =
        Measure.map Subtype.val
          (identitySourceMeasure
            V.realCliffordGeneralSpinCentralFiberIdentityChart
            V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure) := by
      exact restrict_gluedMeasure_identitySource
        (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
        (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
        V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
        V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
    _ = Measure.map Subtype.val
        V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure := by
      simpa using congrArg
        (Measure.map
          (Subtype.val :
            V.realCliffordGeneralSpinCentralFiberIdentityChart.source → _))
        V.realCliffordGeneralSpinCentralFiberIdentitySourceMeasure_eq

/-- On the literal p-adic identity chart, the ambient glued measure recovers
the already normalized intrinsic chart measure. -/
theorem restrict_padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source =
      Measure.map Subtype.val
        (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  calc
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source =
        Measure.map Subtype.val
          (identitySourceMeasure
            (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
            (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)) := by
      exact restrict_gluedMeasure_identitySource
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
        (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
    _ = Measure.map Subtype.val
        (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p) := by
      simpa using congrArg
        (Measure.map
          (Subtype.val :
            (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source → _))
        (V.padicCliffordGeneralSpinCentralFiberIdentitySourceMeasure_eq p)

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
  gluedMeasure_isLocallyFinite
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
    V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isLocallyFinite

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
  gluedMeasure_isOpenPosMeasure
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
    V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isOpenPosMeasure

theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyFiniteMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
  gluedMeasure_isLocallyFinite
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
    (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
    (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isLocallyFinite p)

theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsOpenPosMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
  gluedMeasure_isOpenPosMeasure
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
    (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
    (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_isOpenPosMeasure p)

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure :
    Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  simpa [realCliffordGeneralSpinHorizontalDifferentialHaarMeasure] using
    (gluedMeasure_isHaarMeasure
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isOpenPosMeasure)

theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  simpa [padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure] using
    (gluedMeasure_isHaarMeasure
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
    (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite p)
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isOpenPosMeasure p))

end RationalQuadraticSpaceMatrix
