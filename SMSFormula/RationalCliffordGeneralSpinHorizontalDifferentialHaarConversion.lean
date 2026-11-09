import SMSFormula.RationalCliffordGeneralSpinHorizontalCentralExtensionCylinder
import SMSFormula.RationalIdeleDifferentialMathlibHaarComparison

/-!
# Differential Haar conversion on horizontal central-extension cylinders

The exceptional scalar coordinates in the established horizontal `GSpin`
cylinders use Mathlib's selected local multiplicative Haar measures.  The
ambient central fiber instead uses the compact-normalized differential idele
Haar.  This file carries the already isolated finite local conversion through
the exceptional scalar/Spin product, the real/finite central-extension base,
and its good-tail kernel.

The baseline-relative horizontal block weight and the finite Haar conversion
multiply.  No theorem cancels them, identifies either factor with one, or
forms an Euler product.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

local instance horizontalDifferentialHaarConversionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalDifferentialHaarConversionUnitMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance horizontalDifferentialHaarConversionUnitBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance horizontalDifferentialHaarConversionUnitSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalDifferentialHaarConversionPadicSOMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (V.specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalDifferentialHaarConversionPadicSOBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-! ## Exceptional scalar/Spin products -/

/-- The exceptional scalar/Spin chart measure with compact-normalized
differential Haar on every scalar square branch. -/
def cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource S) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1).prod
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)

set_option backward.isDefEq.respectTransparency false in
instance cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure_sigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure S) := by
  let base := fun v : {v // v ∈ S} ↦
    (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1).prod
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
  letI (v : {v // v ∈ S}) : SigmaFinite (base v) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (rationalPadicIdeleDifferentialHaarMeasure v.1) :=
      Measure.IsHaarMeasure.sigmaFinite
        (rationalPadicIdeleDifferentialHaarMeasure v.1)
    letI : SigmaFinite
        (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure,
        map_comap_subtype_coe squareChart.open_source.measurableSet]
      infer_instance
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
      exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    infer_instance
  unfold cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The exceptional scalar/Spin chart measure is the differential measure
scaled by exactly the finite product of local Mathlib-to-differential Haar
conversion scalars. -/
theorem cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure_eq_smul_differential
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure S =
      rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar S •
        V.cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure S := by
  let lhs := fun v : {v // v ∈ S} ↦
    (padicUnitSquareIdentityChartAmbientSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
  let rhs := fun v : {v // v ∈ S} ↦
    (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1).prod
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
  letI (v : {v // v ∈ S}) : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI (v : {v // v ∈ S}) : SigmaFinite (rhs v) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (rationalPadicIdeleDifferentialHaarMeasure v.1) :=
      Measure.IsHaarMeasure.sigmaFinite
        (rationalPadicIdeleDifferentialHaarMeasure v.1)
    letI : SigmaFinite
        (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure,
        map_comap_subtype_coe squareChart.open_source.measurableSet]
      infer_instance
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
      exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    infer_instance
  have hlocal (v : {v // v ∈ S}) :
      lhs v = rationalPadicMathlibHaarToDifferentialScalar v.1 • rhs v := by
    unfold lhs rhs
    rw [padicUnitSquareIdentityChartAmbientSourceMeasure_eq_smul_differential]
    change
      (((rationalPadicMathlibHaarToDifferentialScalar v.1 : ℝ≥0∞) •
          padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1).prod
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1)) =
      (rationalPadicMathlibHaarToDifferentialScalar v.1 : ℝ≥0∞) • rhs v
    exact Measure.prod_smul_left
      (ν := V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
      (μ := padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1)
      (rationalPadicMathlibHaarToDifferentialScalar v.1 : ℝ≥0∞)
  letI (v : {v // v ∈ S}) : SigmaFinite (lhs v) := by
    rw [hlocal]
    infer_instance
  change Measure.pi lhs =
    (∏ v : {v // v ∈ S}, rationalPadicMathlibHaarToDifferentialScalar v.1) •
      Measure.pi rhs
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi _ s]
  simp_rw [hlocal, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.coe_finset_prod, Finset.prod_mul_distrib]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

local instance horizontalDifferentialCylinderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalDifferentialCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance horizontalDifferentialCylinderRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalDifferentialCylinderRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalDifferentialCylinderPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalDifferentialCylinderPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalDifferentialCylinderRealSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalDifferentialCylinderRealSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalDifferentialCylinderPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalDifferentialCylinderPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalDifferentialCylinderHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalDifferentialCylinderHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalDifferentialCylinderFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalDifferentialCylinderFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-! ## Central-extension cylinder scale -/

/-- The central-extension base with differential Haar on its exceptional
scalar coordinates. -/
def cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (L.CliffordGeneralSpinHorizontalCentralExtensionCylinderBase S) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  (RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
      V.realCliffordSpinCandidateIdentityChartSourceMeasure).prod
    ((V.cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prod
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)))

/-- The finite exceptional Mathlib-to-differential conversion used by the
central-extension cylinder. -/
def cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  RationalQuadraticSpaceMatrix.rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar
    (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)

theorem cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar_ne_zero
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar S ≠ 0 := by
  unfold cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar
  exact_mod_cast
    RationalQuadraticSpaceMatrix.rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar_ne_zero
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)

theorem cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar S ≠ ⊤ := by
  simp [cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar]

/-- The central-extension base differs from the differential base by exactly
the finite exceptional Haar conversion. -/
theorem cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure_eq_smul_differential
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S =
      L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar S •
        L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let muR :=
    RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
      V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let muE :=
    V.cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure
      (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
  let muSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
    (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
  let c : ℝ≥0∞ :=
    RationalQuadraticSpaceMatrix.rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar
      (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
  letI : SigmaFinite muE := by
    unfold muE
    infer_instance
  letI : SigmaFinite muSO := IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite (muE.prod muSO) := by infer_instance
  change muR.prod
      ((V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
          (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prod muSO) =
    c • muR.prod (muE.prod muSO)
  rw [show V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
      (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) = c • muE by
    exact V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure_eq_smul_differential
      (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)]
  change muR.prod ((c • muE).prod muSO) = c • muR.prod (muE.prod muSO)
  rw [Measure.prod_smul_left, Measure.prod_smul_right]

/-- The complete finite cylinder coefficient is the product of the existing
baseline-relative block weight and the exceptional Haar conversion. -/
def cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) *
    L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar S

theorem cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_zero
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S ≠ 0 := by
  exact mul_ne_zero
    (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_zero
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S))
    (L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar_ne_zero S)

theorem cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_top
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S))
    (L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar_ne_top S)

/-- The weighted base exposes both finite coefficients, with no cancellation
between the block normalization and the Haar conversion. -/
theorem cliffordGeneralSpinHorizontalCentralExtensionWeightedBaseMeasure_eq_smul_differential
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) •
        L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S =
      L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S •
        L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S := by
  rw [L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure_eq_smul_differential]
  let w :=
    L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)
  let c := L.cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar S
  let μ := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S
  change w • c • μ = (w * c) • μ
  exact smul_smul w c μ

/-- Passing through the normalized good-tail central fiber preserves the
complete explicit differential cylinder scale. -/
theorem cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure_eq_smul_differential
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight
            (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) •
          L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S) =
      L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S •
        (L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
          L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S) := by
  let κ := L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S
  let c := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S
  let μ := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S
  have hbase := congrArg (fun ν => κ ∘ₘ ν)
    (L.cliffordGeneralSpinHorizontalCentralExtensionWeightedBaseMeasure_eq_smul_differential S)
  calc
    _ = κ ∘ₘ (c • μ) := hbase
    _ = _ := Measure.comp_smul c

end PositiveDefiniteIntegralLattice
