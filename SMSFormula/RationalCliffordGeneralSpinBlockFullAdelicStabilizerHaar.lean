import SMSFormula.RationalCliffordGeneralSpinBlockFiniteAdelicStabilizerHaar
import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicHaar

/-!
# Full-adelic Haar on the intrinsic GSpin complement stabilizer

The certified full-adelic complement stabilizer is split through the existing
real--finite equivalence and the already normalized real and finite stabilizer
homeomorphisms.  Their product measure is transported back to the literal
full-adelic stabilizer.  This measure is exactly the pushforward of the
lower-rank horizontal full-adelic Haar, with no new scale.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance blockFullAdelicInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance blockFullAdelicFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance blockFullAdelicT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance blockFullAdelicSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) :
    SecondCountableTopology W.FullAdelicCliffordGeneralSpinGroup :=
  W.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph
    |>.secondCountableTopology

noncomputable local instance blockFullAdelicSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) :
    LocallyCompactSpace W.FullAdelicCliffordGeneralSpinGroup :=
  W.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance blockFullAdelicSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace W.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance blockFullAdelicSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace W.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance blockRealSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace W.RealCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance blockRealSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace W.RealCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance blockFiniteSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance blockFiniteSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

abbrev FullAdelicNonisotropicLastComplementGeneralSpinStabilizer
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :=
  W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha RationalAdele

/-- The actual full-adelic lower GSpin carrier is homeomorphic to the literal
fixed-last-vector stabilizer in the block extension. -/
noncomputable def fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicCliffordGeneralSpinGroup ≃ₜ*
      W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha :=
  W.nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    a ha RationalAdele

theorem fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv_toMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha).toMulEquiv =
        W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
          a ha RationalAdele := by
  exact
    W.nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv_toMulEquiv
      a ha RationalAdele

noncomputable local instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerSecondCountableTopology
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  borel _

noncomputable instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  ⟨rfl⟩

noncomputable local instance
    realNonisotropicLastComplementGeneralSpinStabilizerSecondCountableTopology
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha ℝ)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable local instance
    finiteNonisotropicLastComplementGeneralSpinStabilizerSecondCountableTopology
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalFiniteAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

/-- The literal full-adelic stabilizer splits into the already normalized real
and finite-adelic stabilizers. -/
noncomputable def fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRealFiniteContinuousMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ≃ₜ*
      W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha ×
        W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha :=
  (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha).symm.trans
    (W.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.trans
      (PositiveDefiniteIntegralLattice.prodContinuousMulEquiv
        (W.realNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
          a ha)
        (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
          a ha)))

/-- The literal real--finite product of the already normalized stabilizer
measures. -/
noncomputable def realFiniteNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure
      (W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha ×
        W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha).prod
    (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
      a ha)

/-- The full-adelic stabilizer measure assembled from its established real and
restricted finite factors. -/
noncomputable def fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure (W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  Measure.map
    (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRealFiniteContinuousMulEquiv
      a ha).symm.toHomeomorph
    (W.realFiniteNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
      a ha)

/-- Splitting the assembled full-adelic stabilizer measure recovers exactly
the established real stabilizer Haar times the restricted finite stabilizer
Haar. -/
theorem map_fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_realFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure.map
        (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRealFiniteContinuousMulEquiv
          a ha).toHomeomorph
        (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) =
      (W.realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha).prod
        (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) := by
  let E :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRealFiniteContinuousMulEquiv
      a ha
  rw [fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure,
    Measure.map_map E.continuous.measurable E.symm.continuous.measurable]
  have hcomp :
      (⇑E.toHomeomorph ∘ ⇑E.symm.toHomeomorph) = id := by
    funext x
    exact E.apply_symm_apply x
  rw [hcomp, Measure.map_id]
  rfl

/-- The real--finite assembly is exactly the direct pushforward of the
established lower-rank horizontal full-adelic Haar through the certified block
embedding. -/
theorem fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_eq_map_horizontal
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha =
      Measure.map
        (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
          a ha RationalAdele)
        W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  let Efull :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha
  let Esplit :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRealFiniteContinuousMulEquiv
      a ha
  let Elower := W.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
  let Eprod := PositiveDefiniteIntegralLattice.prodContinuousMulEquiv
    (W.realNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha)
    (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha)
  apply Esplit.toHomeomorph.measurableEmbedding.map_injective
  rw [W.map_fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_realFinite
    a ha]
  have hEfull :
      (⇑(W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
        a ha RationalAdele) : W.FullAdelicCliffordGeneralSpinGroup →
          W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) =
        ⇑Efull.toHomeomorph := by
    funext x
    exact congrArg (fun e : W.FullAdelicCliffordGeneralSpinGroup ≃*
        W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha => e x)
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv_toMulEquiv
        a ha).symm
  rw [hEfull]
  rw [Measure.map_map Esplit.continuous.measurable Efull.continuous.measurable]
  have hcomp :
      (⇑Esplit.toHomeomorph ∘ ⇑Efull.toHomeomorph) =
        (⇑Eprod.toHomeomorph ∘ ⇑Elower.toHomeomorph) := by
    funext x
    change Eprod (Elower (Efull.symm (Efull x))) = Eprod (Elower x)
    rw [Efull.symm_apply_apply]
  rw [hcomp]
  rw [← Measure.map_map Eprod.continuous.measurable Elower.continuous.measurable]
  rw [W.map_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_realFinite]
  letI : IsLocallyFiniteMeasure
      W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isLocallyFinite
  letI : SigmaFinite
      W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SFinite
      W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
    infer_instance
  letI : IsLocallyFiniteMeasure
      W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isLocallyFinite
  letI : SigmaFinite
      W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SFinite
      W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
    infer_instance
  rw [show Measure.map Eprod.toHomeomorph
      (W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.prod
        W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
        (Measure.map
          (W.realNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
            a ha).toHomeomorph
          W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure).prod
        (Measure.map
          (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
            a ha).toHomeomorph
          W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) by
    exact (Measure.map_prod_map
      W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
      W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
      (W.realNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
        a ha).continuous.measurable
      (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
        a ha).continuous.measurable).symm]
  rfl

noncomputable instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure.IsHaarMeasure
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  letI : Measure.IsHaarMeasure
      W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  let Efull :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha
  rw [W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_eq_map_horizontal
    a ha]
  exact Efull.toMulEquiv.isHaarMeasure_map
    W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    Efull.continuous Efull.symm.continuous

noncomputable instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isLocallyFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsLocallyFiniteMeasure
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  infer_instance

noncomputable instance
    fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isSigmaFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SigmaFinite
      (W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) :=
  sigmaFinite_of_locallyFinite

/-- Integration against full-adelic stabilizer Haar is literally lower-rank
horizontal full-adelic integration through the certified block map. -/
theorem lintegral_fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z
        ∂(W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) =
      ∫⁻ x, f
          (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
            a ha RationalAdele x)
        ∂W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_eq_map_horizontal
    a ha]
  exact lintegral_map hf
    (W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha RationalAdele).measurable

end RationalQuadraticSpaceMatrix
