import SMSFormula.RationalCliffordGeneralSpinBlockStabilizerHaar
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicHaarRegularity
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicLocalCompactness

/-!
# Finite-adelic Haar on the intrinsic GSpin complement stabilizer

The exact complement block homeomorphism is specialized to the existing
intrinsic finite-adelic GSpin carrier.  Its local evaluations commute with the
placewise block maps, so the carrier keeps its restricted-product structure.
The coherent horizontal finite-adelic Haar measure is then pushed to the
fixed-last-vector stabilizer with no new scale.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

local instance blockFiniteAdelicT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance blockFiniteAdelicPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance blockFiniteAdelicSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) :
    LocallyCompactSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  W.finiteAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance blockFiniteAdelicSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance blockFiniteAdelicSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The actual finite-adelic lower GSpin carrier is homeomorphic to the
literal fixed-last-vector stabilizer in the block extension. -/
noncomputable def finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FiniteAdelicCliffordGeneralSpinGroup ≃ₜ*
      W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalFiniteAdele :=
  W.nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    a ha RationalFiniteAdele

theorem finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv_toMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha).toMulEquiv =
        W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
          a ha RationalFiniteAdele := by
  rfl

abbrev FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :=
  W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalFiniteAdele

noncomputable local instance
    finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerSecondCountableTopology
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalFiniteAdele)
    |>.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

noncomputable instance
    finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  borel _

noncomputable instance
    finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  ⟨rfl⟩

/-- Finite-adelic block embedding commutes with evaluation at every
height-one place. -/
theorem finiteAdelicNonisotropicLastComplementGeneralSpinStabilizer_component
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : W.FiniteAdelicCliffordGeneralSpinGroup) :
    (W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHeightOneComponentHom
        v
        (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
          a ha RationalFiniteAdele x).1 =
      W.nonisotropicLastComplementGeneralSpinPoint a ha
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (W.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x) := by
  exact W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) x

/-- The coherent horizontal finite-adelic Haar transported to the exact
GSpin complement stabilizer. -/
noncomputable def finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure
      (W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  Measure.map
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha RationalFiniteAdele)
    W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure

noncomputable instance
    finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure.IsHaarMeasure
      (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  letI : Measure.IsHaarMeasure
      W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  let e :=
    W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha
  change Measure.IsHaarMeasure
    (Measure.map e.toMulEquiv
      W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure)
  exact e.toMulEquiv.isHaarMeasure_map
    W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
    e.continuous e.symm.continuous

noncomputable instance
    finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isLocallyFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsLocallyFiniteMeasure
      (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) := by
  infer_instance

noncomputable instance
    finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isSigmaFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SigmaFinite
      (W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
        a ha) :=
  sigmaFinite_of_locallyFinite

/-- Integration against finite-adelic stabilizer Haar is literally integration
against the lower-rank coherent horizontal Haar through the block map. -/
theorem lintegral_finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : W.FiniteAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z
        ∂(W.finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
          a ha) =
      ∫⁻ x, f
          (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
            a ha RationalFiniteAdele x)
        ∂W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  have hmeas : Measurable
      (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
        a ha RationalFiniteAdele) :=
    W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha RationalFiniteAdele |>.measurable
  rw [finiteAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure,
    lintegral_map hf hmeas]

end RationalQuadraticSpaceMatrix
