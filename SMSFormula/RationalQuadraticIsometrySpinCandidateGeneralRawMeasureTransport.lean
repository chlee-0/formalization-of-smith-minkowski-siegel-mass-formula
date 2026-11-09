import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRawHaarTransport
import SMSFormula.RationalCliffordSpinCandidateRawNormalizationUniqueness

/-!
# Raw Spin quotient transport under an arbitrary rational isometry

Exact raw full-adelic Haar transport is descended through the already fixed
left quotients.  The measurable Weil identity is transported simultaneously
through the group and quotient equivalences, and existing fundamental-domain
uniqueness identifies the quotient measures without comparing or selecting
fundamental domains.  Fixed-matrix raw-normalization uniqueness then gives
invariance of arbitrary certified Spin Tamagawa numbers.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

/-! ## Measurable Weil quotient transport -/

private theorem leftPreperiodize_equiv_of_subgroup_map
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (Gamma : Subgroup G) (Delta : Subgroup H)
    (hmap : Gamma.map e.toMonoidHom = Delta)
    (f : H → ℝ≥0∞) (y : G) :
    leftPreperiodize Gamma (fun z => f (e z)) y =
      leftPreperiodize Delta f (e y) := by
  unfold leftPreperiodize
  let eGamma : Gamma ≃ Delta :=
    ((e.subgroupMap Gamma).trans
      (MulEquiv.subgroupCongr hmap)).toEquiv
  calc
    (∑' gamma : Gamma, f (e ((gamma : G) * y))) =
        ∑' gamma : Gamma,
          f (((eGamma gamma : Delta) : H) * e y) := by
      apply tsum_congr
      intro gamma
      rw [map_mul]
      rfl
    _ = ∑' delta : Delta, f ((delta : H) * e y) := by
      exact eGamma.tsum_eq
        (fun delta : Delta => f ((delta : H) * e y))

/-- Left preperiodization commutes with the exact full-adelic Spin and
rational-diagonal arbitrary-isometry equivalences. -/
theorem rationalIsometrySpinCandidate_leftPreperiodize_commutes
    (f : Z.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞)
    (y : W.FullAdelicCliffordSpinCandidateGroup) :
    leftPreperiodize
        W.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
        (fun z =>
          f (rationalIsometrySpinCandidateMulEquiv
            W Z e RationalAdele z)) y =
      leftPreperiodize
        Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f
        (rationalIsometrySpinCandidateMulEquiv
          W Z e RationalAdele y) := by
  exact leftPreperiodize_equiv_of_subgroup_map
    (rationalIsometrySpinCandidateMulEquiv W Z e RationalAdele)
    W.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
    Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
    (rationalIsometrySpinCandidateFullAdelic_diagonalSubgroup_map W Z e) f y

/-- Descended left periodization commutes with the full-adelic Spin group and
left-quotient arbitrary-isometry equivalences. -/
theorem rationalIsometrySpinCandidate_leftPeriodize_commutes
    (f : Z.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞)
    (C : W.FullAdelicCliffordSpinCandidateLeftQuotient) :
    leftPeriodize
        W.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
        (fun z =>
          f (rationalIsometrySpinCandidateMulEquiv
            W Z e RationalAdele z)) C =
      leftPeriodize
        Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv
          W Z e C) := by
  refine Quot.inductionOn C ?_
  intro y
  change leftPreperiodize
      W.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      (fun z =>
        f (rationalIsometrySpinCandidateMulEquiv
          W Z e RationalAdele z)) y =
    leftPreperiodize
      Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f
      (rationalIsometrySpinCandidateMulEquiv W Z e RationalAdele y)
  exact rationalIsometrySpinCandidate_leftPreperiodize_commutes W Z e f y

/-- A measurable left Weil identity transports simultaneously through the
exact full-adelic Spin group and quotient equivalences. -/
theorem isLeftMeasurableWeilQuotientMeasure_map_rationalIsometrySpinCandidate
    (D : W.CliffordSpinCandidateMeasurableWeilMeasureData) :
    IsLeftMeasurableWeilQuotientMeasure
      Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      (Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalAdele)
        D.adelicMeasure)
      (Measure.map
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
          W Z e)
        D.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    let eG :=
      (rationalIsometrySpinCandidateContinuousMulEquiv
        W Z e RationalAdele).toMeasurableEquiv
    let eX : W.FullAdelicCliffordSpinCandidateLeftQuotient ≃ᵐ
        Z.FullAdelicCliffordSpinCandidateLeftQuotient :=
      { toEquiv :=
          rationalIsometrySpinCandidateFullAdelicLeftQuotientEquiv W Z e
        measurable_toFun :=
          measurable_rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
            W Z e
        measurable_invFun :=
          measurable_rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph_symm
            W Z e }
    calc
      ∫⁻ X,
          leftPeriodize
            Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f X
          ∂Measure.map eX D.quotientMeasure =
        ∫⁻ C,
          leftPeriodize
            Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f (eX C)
          ∂D.quotientMeasure := by
            exact lintegral_map_equiv _ eX
      _ =
        ∫⁻ C,
          leftPeriodize
            W.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
            (fun z => f (eG z)) C
          ∂D.quotientMeasure := by
            apply lintegral_congr
            intro C
            exact (rationalIsometrySpinCandidate_leftPeriodize_commutes
              W Z e f C).symm
      _ = ∫⁻ y, f (eG y) ∂D.adelicMeasure :=
        D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq _
          (hf.comp eG.measurable)
      _ = ∫⁻ z, f z ∂Measure.map eG D.adelicMeasure := by
        exact (lintegral_map_equiv f eG).symm

/-- The canonical raw quotient measure transports exactly when the source
scale is divided by the independently forced inverse-volume correction. -/
theorem map_rationalIsometryFullAdelicSpinCandidateRawDifferentialQuotientMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (finiteScale : ℝ≥0) :
    Measure.map
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
          W Z e)
        (W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
          (finiteScale /
            e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)).quotientMeasure =
      (Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale).quotientMeasure := by
  let DW :=
    W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
      (finiteScale /
        e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)
  let DZ :=
    Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
      finiteScale
  have hWeil :=
    isLeftMeasurableWeilQuotientMeasure_map_rationalIsometrySpinCandidate
      W Z e DW
  have hAdelic : Measure.map
      (rationalIsometrySpinCandidateContinuousMulEquiv
        W Z e RationalAdele)
      DW.adelicMeasure = DZ.adelicMeasure := by
    dsimp only [DW, DZ]
    rw [W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_adelicMeasure,
      Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_adelicMeasure]
    exact
      map_rationalIsometryFullAdelicSpinCandidateRawDifferentialGroupMeasure
        W Z e hS hW hZ finiteScale
  rw [hAdelic] at hWeil
  let DT : Z.CliffordSpinCandidateMeasurableWeilMeasureData :=
    { adelicMeasure := DZ.adelicMeasure
      quotientMeasure := Measure.map
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
          W Z e)
        DW.quotientMeasure
      isMeasurableWeilQuotientMeasure := hWeil }
  calc
    Measure.map
        (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
          W Z e)
        DW.quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        Z.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
        DZ.adelicMeasure
        Z.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain :=
      DT.quotientMeasure_eq_fundamentalDomain
    _ = DZ.quotientMeasure :=
      DZ.quotientMeasure_eq_fundamentalDomain.symm

/-- The canonical raw Spin quotient volumes agree under an arbitrary
rational isometry. -/
theorem fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_of_rationalIsometry
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (finiteScale : ℝ≥0) :
    (W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
      (finiteScale /
        e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)).quotientVolumeENNReal =
      (Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale).quotientVolumeENNReal := by
  have hmap :=
    map_rationalIsometryFullAdelicSpinCandidateRawDifferentialQuotientMeasure
      W Z e hS hW hZ finiteScale
  have hmass := congrArg (fun μ : Measure
      Z.FullAdelicCliffordSpinCandidateLeftQuotient => μ Set.univ) hmap
  change (Measure.map
      (rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph W Z e)
      (W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        (finiteScale /
          e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)).quotientMeasure)
        Set.univ =
    (Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
      finiteScale).quotientMeasure Set.univ at hmass
  rw [Measure.map_apply
      (measurable_rationalIsometrySpinCandidateFullAdelicLeftQuotientHomeomorph
        W Z e)
      MeasurableSet.univ] at hmass
  simpa [CliffordSpinCandidateMeasurableWeilMeasureData.quotientVolumeENNReal]
    using hmass

/-! ## Certified raw-data invariance -/

/-- The raw Spin Tamagawa number is invariant under an arbitrary supplied
rational quadratic isometry.  Arbitrary certified data are first replaced by
the canonical differential data on their own fixed matrices; the middle
equality is exact quotient-volume transport. -/
theorem spinTamagawaNumberENNReal_eq_of_rationalIsometry_of_horizontalIntegralTailSupport
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (DW : W.CliffordSpinCandidateRawOnoTamagawaData)
    (DZ : Z.CliffordSpinCandidateRawOnoTamagawaData) :
    DW.spinTamagawaNumberENNReal = DZ.spinTamagawaNumberENNReal := by
  let sourceCertificate :=
    e.transport_target_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_toSource
      hS DZ.spinRaw.volumeProductCertificate
  let DSource : W.CliffordSpinCandidateRawOnoTamagawaData :=
    { specialOrthogonalData := DW.specialOrthogonalData
      specialOrthogonalFiniteScale := DW.specialOrthogonalFiniteScale
      spinFiniteScale := DZ.spinFiniteScale /
        e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S
      spinData :=
        W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
          (DZ.spinFiniteScale /
            e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)
      specialOrthogonalRaw := DW.specialOrthogonalRaw
      spinRaw :=
        W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
          (DZ.spinFiniteScale /
            e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)
          sourceCertificate }
  let DTarget : Z.CliffordSpinCandidateRawOnoTamagawaData :=
    { specialOrthogonalData := DZ.specialOrthogonalData
      specialOrthogonalFiniteScale := DZ.specialOrthogonalFiniteScale
      spinFiniteScale := DZ.spinFiniteScale
      spinData :=
        Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
          DZ.spinFiniteScale
      specialOrthogonalRaw := DZ.specialOrthogonalRaw
      spinRaw :=
        Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
          DZ.spinFiniteScale DZ.spinRaw.volumeProductCertificate }
  calc
    DW.spinTamagawaNumberENNReal = DSource.spinTamagawaNumberENNReal :=
      DW.spinTamagawaNumberENNReal_eq DSource
    _ = (W.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        (DZ.spinFiniteScale /
          e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)).quotientVolumeENNReal := rfl
    _ = (Z.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        DZ.spinFiniteScale).quotientVolumeENNReal :=
      fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_of_rationalIsometry
        W Z e hS hW hZ DZ.spinFiniteScale
    _ = DTarget.spinTamagawaNumberENNReal := rfl
    _ = DZ.spinTamagawaNumberENNReal :=
      DTarget.spinTamagawaNumberENNReal_eq DZ

end RationalQuadraticSpaceMatrix

end
