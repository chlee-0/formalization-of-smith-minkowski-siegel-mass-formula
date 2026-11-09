import SMSFormula.HaarMeasureTwoSheetLocalHomeomorph
import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalCliffordGeneralSpinLocalCompactness
import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalHaar
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialUnimodular
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialUnimodular

/-!
# Placewise unimodularity of horizontal intrinsic general Spin Haar

The combined homomorphism `(nu, pi)` is a local homeomorphism at the identity
with literal two-point kernel.  Its range is therefore an open subgroup of
`K^* x SO(K)`.  The fixed product differential measure is inversion invariant,
so its restriction to that open range supplies an inversion-invariant Haar
measure.  The two-sheet local-chart theorem makes the pushforward of the
already normalized intrinsic `GSpin` Haar another Haar measure on the same
range.  Haar uniqueness and homomorphic descent then prove inversion and right
invariance of the actual real and p-adic horizontal measures at their fixed
differential scales.

No adelic product, quotient disintegration, or Haar normalization scalar is
introduced here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalUnimodularRealSchemeSOIsTopologicalGroup :
    IsTopologicalGroup (V.specialOrthogonalMatrixGroup ℝ) := by
  change IsTopologicalGroup
    (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℝ)))
  infer_instance

set_option synthInstance.maxHeartbeats 400000

noncomputable local instance placewiseHorizontalUnimodularRealSchemeSOMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance placewiseHorizontalUnimodularRealSchemeSOBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance
    placewiseHorizontalUnimodularPadicSchemeSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance placewiseHorizontalUnimodularPadicSchemeSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

noncomputable local instance placewiseHorizontalUnimodularRealTargetSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) := borel _

noncomputable local instance placewiseHorizontalUnimodularRealTargetSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) := ⟨rfl⟩

noncomputable local instance placewiseHorizontalUnimodularPadicTargetSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

noncomputable local instance placewiseHorizontalUnimodularPadicTargetSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

noncomputable local instance placewiseHorizontalUnimodularRealTargetSOLocallyCompact :
    LocallyCompactSpace (V.specialOrthogonalMatrixGroup ℝ) := by
  change LocallyCompactSpace
    (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup V.realFormMatrix)
  exact V.realSpecialOrthogonalGroupLocallyCompactSpace

noncomputable local instance placewiseHorizontalUnimodularPadicTargetSOLocallyCompact
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_locallyCompact
    p n V.pairingMatrix V.form_det_ne_zero

noncomputable local instance placewiseHorizontalUnimodularRealTargetSOSecondCountable :
    SecondCountableTopology (V.specialOrthogonalMatrixGroup ℝ) := by
  change SecondCountableTopology V.RealSpecialOrthogonalGroup
  exact V.realSpecialOrthogonalGroupSecondCountable_spinorNorm

noncomputable local instance placewiseHorizontalUnimodularPadicTargetSOSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupSecondCountable_spinorNorm p

noncomputable local instance placewiseHorizontalUnimodularRealSourceLocallyCompact :
    LocallyCompactSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  V.realCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance placewiseHorizontalUnimodularPadicSourceLocallyCompact
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  V.padicCliffordGeneralSpinGroupLocallyCompactSpace p

/-! ## Open combined images -/

/-- The actual real image of the combined central-fiber homomorphism. -/
abbrev RealCliffordGeneralSpinCentralFiberImage :=
  (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).range

/-- The actual p-adic image of the combined central-fiber homomorphism. -/
abbrev PadicCliffordGeneralSpinCentralFiberImage
    (p : ℕ) [Fact (Nat.Prime p)] :=
  (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).range

theorem isOpen_realCliffordGeneralSpinCentralFiberImage :
    IsOpen
      ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).range :
        Set (ℝˣ × V.specialOrthogonalMatrixGroup ℝ)) :=
  MeasureTheory.TranslatedHomChart.isOpen_range_of_local_chart
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source

theorem isOpen_padicCliffordGeneralSpinCentralFiberImage
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).range :
        Set (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p])) :=
  MeasureTheory.TranslatedHomChart.isOpen_range_of_local_chart
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
    (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)

noncomputable instance realCliffordGeneralSpinCentralFiberImageLocallyCompactSpace :
    LocallyCompactSpace V.RealCliffordGeneralSpinCentralFiberImage :=
  V.isOpen_realCliffordGeneralSpinCentralFiberImage.locallyCompactSpace

noncomputable instance realCliffordGeneralSpinCentralFiberImageSecondCountableTopology :
    SecondCountableTopology V.RealCliffordGeneralSpinCentralFiberImage :=
  TopologicalSpace.Subtype.secondCountableTopology _

noncomputable instance padicCliffordGeneralSpinCentralFiberImageLocallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (V.PadicCliffordGeneralSpinCentralFiberImage p) :=
  (V.isOpen_padicCliffordGeneralSpinCentralFiberImage p).locallyCompactSpace

noncomputable instance
    padicCliffordGeneralSpinCentralFiberImageSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (V.PadicCliffordGeneralSpinCentralFiberImage p) :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-! ## Inversion-invariant product and image measures -/

noncomputable instance
    realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isInvInvariant :
    Measure.IsInvInvariant
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure := by
  letI : Measure.IsInvInvariant V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isInvInvariant
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) := by infer_instance
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SFinite (Measure.haar : Measure ℝˣ) := by infer_instance
  letI : SFinite V.realInvariantDifferentialGroupMeasure := by infer_instance
  unfold realCliffordGeneralSpinHorizontalDifferentialProductMeasure
  exact Measure.isInvInvariant_prod
    (Measure.haar : Measure ℝˣ) V.realInvariantDifferentialGroupMeasure

noncomputable instance
    padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) := by
  letI : Measure.IsInvInvariant (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isInvInvariant p
  letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) := by infer_instance
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SFinite (Measure.haar : Measure ℚ_[p]ˣ) := by infer_instance
  letI : SFinite (V.padicInvariantDifferentialGroupMeasure p) := by infer_instance
  unfold padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
  exact Measure.isInvInvariant_prod
    (Measure.haar : Measure ℚ_[p]ˣ)
    (V.padicInvariantDifferentialGroupMeasure p)

/-- The fixed real product differential measure restricted to the actual
combined image. -/
def realCliffordGeneralSpinCentralFiberImageDifferentialMeasure :
    Measure V.RealCliffordGeneralSpinCentralFiberImage :=
  Measure.comap V.RealCliffordGeneralSpinCentralFiberImage.subtype
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

/-- The fixed p-adic product differential measure restricted to the actual
combined image. -/
def padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.PadicCliffordGeneralSpinCentralFiberImage p) :=
  Measure.comap (V.PadicCliffordGeneralSpinCentralFiberImage p).subtype
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

noncomputable instance
    realCliffordGeneralSpinCentralFiberImageDifferentialMeasure_isHaar :
    Measure.IsHaarMeasure
      V.realCliffordGeneralSpinCentralFiberImageDifferentialMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  unfold realCliffordGeneralSpinCentralFiberImageDifferentialMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure)
    (f := V.RealCliffordGeneralSpinCentralFiberImage.subtype)
    (mH := ContinuousMul.measurableMul)
    V.isOpen_realCliffordGeneralSpinCentralFiberImage.isOpenEmbedding_subtypeVal

set_option backward.isDefEq.respectTransparency false in
noncomputable instance
    realCliffordGeneralSpinCentralFiberImageDifferentialMeasure_isInvInvariant :
    Measure.IsInvInvariant
      V.realCliffordGeneralSpinCentralFiberImageDifferentialMeasure := by
  letI : Measure.IsInvInvariant
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isInvInvariant
  unfold realCliffordGeneralSpinCentralFiberImageDifferentialMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (G := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (muG := V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure)
    V.RealCliffordGeneralSpinCentralFiberImage rfl
    V.isOpen_realCliffordGeneralSpinCentralFiberImage.measurableSet

noncomputable instance
    padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure_isHaar
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure p
  unfold padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)
    (f := (V.PadicCliffordGeneralSpinCentralFiberImage p).subtype)
    (mH := ContinuousMul.measurableMul)
    (V.isOpen_padicCliffordGeneralSpinCentralFiberImage p).isOpenEmbedding_subtypeVal

noncomputable instance
    padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure p) := by
  letI : Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure_isInvInvariant p
  unfold padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (V.PadicCliffordGeneralSpinCentralFiberImage p) rfl
    (V.isOpen_padicCliffordGeneralSpinCentralFiberImage p).measurableSet

/-! ## Descent to the normalized intrinsic local measures -/

set_option backward.isDefEq.respectTransparency false in
noncomputable instance
    map_realCliffordGeneralSpinCentralFiberRangeRestrict_horizontalMeasure_isHaar :
    Measure.IsHaarMeasure
      (Measure.map
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).rangeRestrict
        V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  exact
    MeasureTheory.TranslatedHomChart.isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
      (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
      (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
      V.realCliffordGeneralSpinCentralFiberIdentityChart
      (V.continuous_cliffordGeneralSpinCentralFiberGroupHom ℝ)
      V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
      V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
      V.isOpen_realCliffordGeneralSpinCentralFiberImage
      (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V ℝ)
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_negOnePoint V ℝ)
      (CliffordGeneralSpinIntrinsicPoint.eq_one_or_centralFiberNegOnePoint_of_centralFiberGroupHom_eq_one
        V ℝ)
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure

noncomputable instance
    map_realCliffordGeneralSpinCentralFiberRangeRestrict_horizontalMeasure_isInvInvariant :
    Measure.IsInvInvariant
      (Measure.map
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).rangeRestrict
        V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) := by
  exact Measure.isInvInvariant_of_isHaarMeasure_of_exists
    (Measure.map
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).rangeRestrict
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)
    V.realCliffordGeneralSpinCentralFiberImageDifferentialMeasure

noncomputable instance
    realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isInvInvariant :
    Measure.IsInvInvariant
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  have hf : Continuous
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).rangeRestrict :=
    (V.continuous_cliffordGeneralSpinCentralFiberGroupHom ℝ).subtype_mk _
  exact Measure.isInvInvariant_of_map_of_isHaarMeasure
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ).rangeRestrict
    hf.measurable

noncomputable instance
    realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isMulRightInvariant :
    Measure.IsMulRightInvariant
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure

noncomputable instance
    map_padicCliffordGeneralSpinCentralFiberRangeRestrict_horizontalMeasure_isHaar
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (Measure.map
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).rangeRestrict
        (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure p
  exact
    MeasureTheory.TranslatedHomChart.isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
      (V.continuous_cliffordGeneralSpinCentralFiberGroupHom ℚ_[p])
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p)
      (V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p)
      (V.isOpen_padicCliffordGeneralSpinCentralFiberImage p)
      (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V ℚ_[p])
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_negOnePoint V ℚ_[p])
      (CliffordGeneralSpinIntrinsicPoint.eq_one_or_centralFiberNegOnePoint_of_centralFiberGroupHom_eq_one
        V ℚ_[p])
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)

noncomputable instance
    map_padicCliffordGeneralSpinCentralFiberRangeRestrict_horizontalMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (Measure.map
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).rangeRestrict
        (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)) := by
  exact Measure.isInvInvariant_of_isHaarMeasure_of_exists
    (Measure.map
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).rangeRestrict
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p))
    (V.padicCliffordGeneralSpinCentralFiberImageDifferentialMeasure p)

noncomputable instance
    padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure p
  have hf : Continuous
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).rangeRestrict :=
    (V.continuous_cliffordGeneralSpinCentralFiberGroupHom ℚ_[p]).subtype_mk _
  exact Measure.isInvInvariant_of_map_of_isHaarMeasure
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]).rangeRestrict
    hf.measurable

noncomputable instance
    padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isMulRightInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulRightInvariant
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure p
  exact Measure.isMulRightInvariant_of_isInvInvariant
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)

end RationalQuadraticSpaceMatrix
