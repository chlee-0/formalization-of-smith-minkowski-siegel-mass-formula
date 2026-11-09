import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarComparison
import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientMeasure

/-!
# Horizontal general-Spin quotient measure under a complement presentation

The exact full-adelic presentation homeomorphism maps the rational diagonal
subgroup onto the ambient rational diagonal subgroup.  Consequently the left
Weil identity transports simultaneously on the group and its existing left
quotient.  Combining this with the already fixed horizontal Haar comparison
forces the same scalar on the horizontal quotient measure.

The comparison scalar is not asserted to be one.  No fundamental domain is
transported or compared, and no quotient representative, complement lattice,
new measure, or chart is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

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

/-- Left preperiodization commutes with the full-adelic general-Spin
presentation equivalence and the exact rational-diagonal identification. -/
theorem blockToAmbientGeneralSpin_leftPreperiodize_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (y : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup) :
    leftPreperiodize
        (P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        (fun z =>
          f (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z)) y =
      leftPreperiodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx y) := by
  exact leftPreperiodize_equiv_of_subgroup_map
    (P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx)
    (P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    (P.blockToAmbientGeneralSpinFullAdelic_diagonalSubgroup_map hx) f y

/-- Descended left periodization commutes with the full-adelic general-Spin
group and quotient presentation equivalences. -/
theorem blockToAmbientGeneralSpin_leftPeriodize_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (C : (P.blockSpace hx).FullAdelicCliffordGeneralSpinLeftQuotient) :
    leftPeriodize
        (P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        (fun z =>
          f (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z)) C =
      leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv hx C) := by
  refine Quot.inductionOn C ?_
  intro y
  change leftPreperiodize
      (P.blockSpace hx).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      (fun z =>
        f (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z)) y =
    leftPreperiodize
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx y)
  exact P.blockToAmbientGeneralSpin_leftPreperiodize_commutes hx f y

/-- A measurable left Weil identity transports simultaneously through the
exact full-adelic general-Spin group and quotient presentation equivalences. -/
theorem isLeftMeasurableWeilQuotientMeasure_map_blockToAmbientGeneralSpin
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (D : (P.blockSpace hx).CliffordGeneralSpinMeasurableWeilMeasureData) :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        D.adelicMeasure)
      (Measure.map
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
        D.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    let eG :=
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        |>.toMeasurableEquiv
    let eX :
        (P.blockSpace hx).FullAdelicCliffordGeneralSpinLeftQuotient ≃ᵐ
          V.FullAdelicCliffordGeneralSpinLeftQuotient :=
      { toEquiv :=
          P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv hx
        measurable_toFun :=
          P.measurable_blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx
        measurable_invFun :=
          P.measurable_blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph_symm hx }
    calc
      ∫⁻ X,
          leftPeriodize
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f X
          ∂Measure.map eX D.quotientMeasure =
        ∫⁻ C,
          leftPeriodize
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f (eX C)
          ∂D.quotientMeasure := by
            exact lintegral_map_equiv _ eX
      _ =
        ∫⁻ C,
          leftPeriodize
            (P.blockSpace hx
              ).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
            (fun z => f (eG z)) C
          ∂D.quotientMeasure := by
            apply lintegral_congr
            intro C
            exact (P.blockToAmbientGeneralSpin_leftPeriodize_commutes
              hx f C).symm
      _ = ∫⁻ y, f (eG y) ∂D.adelicMeasure :=
        D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq _
          (hf.comp eG.measurable)
      _ = ∫⁻ z, f z ∂Measure.map eG D.adelicMeasure := by
        exact (lintegral_map_equiv f eG).symm

/-- The fixed horizontal general-Spin quotient measure transports by exactly
the same positive finite scalar as the fixed horizontal group Haar measure. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalQuotientMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
        (P.blockSpace hx
          ).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure =
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx •
        V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure := by
  let DB :=
    (P.blockSpace hx
      ).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
  let DA :=
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.smul
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx)
  have hWeil :=
    P.isLeftMeasurableWeilQuotientMeasure_map_blockToAmbientGeneralSpin hx DB
  have hAdelic :
      Measure.map
          (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
          DB.adelicMeasure =
        DA.adelicMeasure := by
    dsimp only [DB, DA,
      CliffordGeneralSpinMeasurableWeilMeasureData.smul]
    exact
      P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_smul hx
  rw [hAdelic] at hWeil
  let DT : V.CliffordGeneralSpinMeasurableWeilMeasureData :=
    { adelicMeasure := DA.adelicMeasure
      quotientMeasure := Measure.map
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
        DB.quotientMeasure
      isMeasurableWeilQuotientMeasure := hWeil }
  calc
    Measure.map
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
        DB.quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        DA.adelicMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :=
      DT.quotientMeasure_eq_fundamentalDomain V
    _ = DA.quotientMeasure :=
      (DA.quotientMeasure_eq_fundamentalDomain V).symm
    _ =
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx •
        V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure := rfl

/-- The total horizontal quotient volumes carry the same presentation scalar.
This is a direct corollary of the exact quotient-measure pushforward. -/
theorem block_fullAdelicCliffordGeneralSpinHorizontalQuotientVolume_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx
      ).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientVolumeENNReal =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientVolumeENNReal := by
  have hmap :=
    P.map_blockToAmbientFullAdelicGeneralSpinHorizontalQuotientMeasure_eq_smul hx
  have hmass := congrArg
    (fun μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient =>
      μ Set.univ) hmap
  change (Measure.map
      (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
      (P.blockSpace hx
        ).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure)
      Set.univ = _ at hmass
  rw [Measure.map_apply
      (P.measurable_blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
      MeasurableSet.univ] at hmass
  simpa [CliffordGeneralSpinMeasurableWeilMeasureData.quotientVolumeENNReal,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply] using hmass

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
