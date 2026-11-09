import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarComparison

/-!
# Placewise factorization of the presentation Haar scalar

The real and finite-adelic presentation maps carry the repository's fixed
horizontal Haar measures to positive scalar multiples of the corresponding
ambient measures.  The full-adelic presentation pushforward is then the
product of those two scalar multiples under the fixed real--finite
splitting.

No local scalar is evaluated in this file.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance presentationFiniteMeasurableSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance presentationFiniteBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The native real specialization of the presentation group equivalence. -/
abbrev blockToAmbientRealGeneralSpinContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).RealCliffordGeneralSpinGroup ≃ₜ*
      V.RealCliffordGeneralSpinGroup :=
  P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℝ

/-- The native finite-adelic specialization of the presentation group
equivalence. -/
abbrev blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup ≃ₜ*
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  P.blockToAmbientGeneralSpinContinuousMulEquiv hx RationalFiniteAdele

theorem map_blockToAmbientRealGeneralSpinHorizontalMeasure_isHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)) := by
  letI : Measure.IsHaarMeasure
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) :=
    (P.blockSpace hx)
      |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  exact
    (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx).toMulEquiv
      |>.isHaarMeasure_map
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx).continuous
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx).symm.continuous

theorem map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_isHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)) := by
  letI : Measure.IsHaarMeasure
      ((P.blockSpace hx)
        |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) :=
    (P.blockSpace hx)
      |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact
    (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).toMulEquiv
      |>.isHaarMeasure_map
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).continuous
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm.continuous

/-- The positive scalar comparing the real presentation pushforward with the
fixed ambient real differential Haar measure. -/
noncomputable def blockToAmbientRealGeneralSpinHorizontalHaarScalar
    (P : V.AnisotropicComplementPresentation x m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℝ≥0 := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)) :=
    P.map_blockToAmbientRealGeneralSpinHorizontalMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  exact Measure.haarScalarFactor
    (Measure.map
      (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure))
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure

/-- The positive scalar comparing the finite-adelic presentation pushforward
with the fixed ambient finite-adelic horizontal Haar measure. -/
noncomputable def blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar
    (P : V.AnisotropicComplementPresentation x m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℝ≥0 := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.haarScalarFactor
    (Measure.map
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure))
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure

theorem blockToAmbientRealGeneralSpinHorizontalHaarScalar_pos
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    0 < P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)) :=
    P.map_blockToAmbientRealGeneralSpinHorizontalMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  unfold blockToAmbientRealGeneralSpinHorizontalHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar_pos
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    0 < P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  unfold blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem map_blockToAmbientRealGeneralSpinHorizontalMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) =
      P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx •
        V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)) :=
    P.map_blockToAmbientRealGeneralSpinHorizontalMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  exact Measure.isMulLeftInvariant_eq_smul _ _

theorem map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx •
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.isMulLeftInvariant_eq_smul _ _

/-- The product of the real and finite presentation maps. -/
abbrev blockToAmbientRealFiniteGeneralSpinContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    ((P.blockSpace hx).RealCliffordGeneralSpinGroup ×
        (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup) ≃ₜ*
      (V.RealCliffordGeneralSpinGroup ×
        V.FiniteAdelicCliffordGeneralSpinGroup) :=
  PositiveDefiniteIntegralLattice.prodContinuousMulEquiv
    (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
    (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)

/-- Presentation transport commutes literally with the fixed real--finite
splitting of full-adelic intrinsic general Spin. -/
theorem blockToAmbientFullAdelicGeneralSpin_realFinite_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z) =
      P.blockToAmbientRealFiniteGeneralSpinContinuousMulEquiv hx
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv z) := by
  apply Prod.ext
  · change CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinRealAlgHom
          (P.blockToAmbientGeneralSpinIntrinsicPoint RationalAdele hx z) =
      P.blockToAmbientGeneralSpinIntrinsicPoint ℝ hx
        (CliffordGeneralSpinIntrinsicPoint.map (P.blockSpace hx)
          fullAdelicCliffordGeneralSpinRealAlgHom z)
    exact (P.blockToAmbientGeneralSpinIntrinsicPoint_naturality hx
      fullAdelicCliffordGeneralSpinRealAlgHom z).symm
  · change CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinFiniteAlgHom
          (P.blockToAmbientGeneralSpinIntrinsicPoint RationalAdele hx z) =
      P.blockToAmbientGeneralSpinIntrinsicPoint RationalFiniteAdele hx
        (CliffordGeneralSpinIntrinsicPoint.map (P.blockSpace hx)
          fullAdelicCliffordGeneralSpinFiniteAlgHom z)
    exact (P.blockToAmbientGeneralSpinIntrinsicPoint_naturality hx
      fullAdelicCliffordGeneralSpinFiniteAlgHom z).symm

/-- On the fixed real--finite product measure, the presentation pushforward
has exactly the product of the two placewise comparison scalars. -/
theorem map_blockToAmbientRealFiniteGeneralSpinHorizontalMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientRealFiniteGeneralSpinContinuousMulEquiv hx)
        (((P.blockSpace hx)
            |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure).prod
          ((P.blockSpace hx)
            |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)) =
      (P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
          P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx) •
        (V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.prod
          V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  letI : IsLocallyFiniteMeasure
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) :=
    (P.blockSpace hx)
      |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite
  letI : SigmaFinite
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) :=
    sigmaFinite_of_locallyFinite
  letI : SFinite
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) := by
    infer_instance
  have hrealMeasurable : Measurable
      (fun z => P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx z) :=
    (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx).continuous.measurable
  have hfiniteMeasurable : Measurable
      (fun z => P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx z) :=
    (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).continuous.measurable
  change Measure.map
      (Prod.map
        (fun z => P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx z)
        (fun z => P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx z))
      (((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure).prod
        ((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)) = _
  rw [← Measure.map_prod_map _ _ hrealMeasurable hfiniteMeasurable,
    P.map_blockToAmbientRealGeneralSpinHorizontalMeasure_eq_smul hx,
    P.map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_eq_smul hx]
  change
    (((P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx : ℝ≥0) : ℝ≥0∞) •
        V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure).prod
      (((P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0) : ℝ≥0∞) •
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      (((P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
        P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0) :
          ℝ≥0∞) •
        (V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.prod
          V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure))
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rfl

/-- The full-adelic presentation pushforward has exactly the product of the
real and finite comparison scalars.  This is an identity at the repository's
fixed real--finite product normalization, before either local scalar is
evaluated. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalMeasure_eq_placewise_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      (P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
          P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx) •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  apply
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph
      |>.measurableEmbedding.map_injective
  have hfullMeasurable : Measurable
      (fun z => P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z) :=
    (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).continuous.measurable
  have hsplitMeasurable : Measurable
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph :=
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph.measurable
  have htargetSplit :
      Measure.map
          V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph
          V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure =
        V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.prod
          V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
    exact V.map_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_realFinite
  rw [Measure.map_smul, htargetSplit]
  rw [Measure.map_map hsplitMeasurable hfullMeasurable]
  have hcommutes :
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph ∘
          (fun z => P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z) =
        (fun z => P.blockToAmbientRealFiniteGeneralSpinContinuousMulEquiv hx z) ∘
          (P.blockSpace hx).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph := by
    funext z
    exact P.blockToAmbientFullAdelicGeneralSpin_realFinite_commutes hx z
  rw [hcommutes]
  have hproductMeasurable : Measurable
      (fun z => P.blockToAmbientRealFiniteGeneralSpinContinuousMulEquiv hx z) :=
    (P.blockToAmbientRealFiniteGeneralSpinContinuousMulEquiv hx).continuous.measurable
  have hblockSplitMeasurable : Measurable
      (P.blockSpace hx).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph :=
    (P.blockSpace hx).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph.measurable
  rw [← Measure.map_map hproductMeasurable hblockSplitMeasurable]
  have hsourceSplit :
      Measure.map
          (P.blockSpace hx).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph
          ((P.blockSpace hx)
            |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
        ((P.blockSpace hx)
            |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure).prod
          ((P.blockSpace hx)
            |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
    exact (P.blockSpace hx)
      |>.map_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_realFinite
  rw [hsourceSplit]
  exact P.map_blockToAmbientRealFiniteGeneralSpinHorizontalMeasure_eq_smul hx

/-- The full-adelic Haar comparison scalar factors as the
product of the real and finite presentation-change scalars. -/
theorem blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_eq_mul_placewise
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx =
      P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
        P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx := by
  letI : Measure.IsHaarMeasure
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure)) :=
    P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_isHaarMeasure hx
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  change Measure.haarScalarFactor
      (Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure))
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure = _
  simp only [
    P.map_blockToAmbientFullAdelicGeneralSpinHorizontalMeasure_eq_placewise_smul hx,
    Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul,
    mul_one]

/-- Literal full-adelic normalization is exactly the one remaining
placewise product calculation. -/
theorem blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_eq_one_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx = 1 ↔
      P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
        P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx = 1 := by
  rw [P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_eq_mul_placewise hx]

/-- The placewise product formula, once established for the fixed
differential normalizations, closes the full-adelic Haar square literally. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalMeasure_eq_of_placewise_mul_eq_one
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hplacewise :
      P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
        P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx = 1) :
    Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [P.map_blockToAmbientFullAdelicGeneralSpinHorizontalMeasure_eq_placewise_smul hx,
    hplacewise, one_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
