import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberScale

/-!
# Differential central-extension cylinders on full adelic general Spin

The completed central-extension cylinder has two finite normalizations: the
baseline-relative horizontal block weight and the finite exceptional
Mathlib-to-differential Haar conversion.  This file transports the genuinely
differential version of that cylinder to the intrinsic full-adelic `GSpin`
carrier.

The resulting full-adelic measure is not identified here with the restriction
of the ambient differential central-fiber bind.  What is proved is the exact
comparison with the already certified coherent horizontal cylinder: the latter
is the explicit positive finite cylinder scale times the differential
full-adelic cylinder.  No coordinate injectivity, quotient comparison, Euler
product, or scalar-one assertion is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalDifferentialFullAdelicDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalDifferentialFullAdelicPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance horizontalDifferentialFullAdelicRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalDifferentialFullAdelicRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalDifferentialFullAdelicPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalDifferentialFullAdelicPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalDifferentialFullAdelicPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalDifferentialFullAdelicRealGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  borel _

noncomputable local instance horizontalDifferentialFullAdelicRealGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  ⟨rfl⟩

noncomputable local instance horizontalDifferentialFullAdelicPadicGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  borel _

noncomputable local instance horizontalDifferentialFullAdelicPadicGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  ⟨rfl⟩

local instance horizontalDifferentialFullAdelicIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalDifferentialFullAdelicIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalDifferentialFullAdelicTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalDifferentialFullAdelicTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalDifferentialFullAdelicFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalDifferentialFullAdelicFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-! ## Direct full-adelic transport -/

/-- The carrier-independent differential central-extension cylinder transported
through the exact reconstructed full-adelic point. -/
noncomputable def
    cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  Measure.map
    (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
      E)
    (L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
      L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S)

/-- Reconstructing the weighted established central-extension cylinder gives
the literal coherent full-adelic identity-chart cylinder.  This removes the
auxiliary global `(nu, pi)` coordinate from the comparison. -/
theorem
    map_cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure_reconstructed
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    Measure.map
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
          E)
        (L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
          (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight E •
            L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S)) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
        E := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let reconstruct :=
    V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  let split := V.cliffordGeneralSpinHorizontalRealFiniteChartSplit E
  let parameterToAmbient :=
    V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient E
  have hreconstruct : Measurable reconstruct :=
    V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have hsplit : Measurable split :=
    (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E).measurable
  have hdyadic : RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈
      E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    exact Finset.mem_union_left _
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces_dyadic S)
  rw [L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure
    S]
  rw [← V.map_cliffordGeneralSpinHorizontalRealFiniteChartSplit_of_dyadic E hdyadic]
  rw [Measure.map_map hreconstruct hsplit]
  have hcomp : reconstruct ∘ split = parameterToAmbient := by
    funext x
    exact V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_split E x
  rw [hcomp]
  exact V.map_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient E

/-- The coherent horizontal cylinder is exactly the named finite scale times
the differential full-adelic central-extension cylinder. -/
theorem
    cliffordGeneralSpinHorizontalDifferentialCylinderScale_smul_fullAdelicCylinderMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S •
        L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
        E := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let reconstruct :=
    V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  let κ := L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S
  let μ := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S
  let c := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S
  have hweighted :=
    L.map_cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure_reconstructed
      S
  have hconvert :=
    L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure_eq_smul_differential
      S
  change c • Measure.map reconstruct (κ ∘ₘ μ) = _
  rw [← Measure.map_smul]
  rw [← hconvert]
  exact hweighted

/-! ## Calibration against fixed horizontal Haar -/

/-- On the certified identity-chart carrier, fixed horizontal Haar is exactly
the explicit cylinder scale times the differential full-adelic cylinder. -/
theorem
    cliffordGeneralSpinHorizontalDifferentialCylinderScale_smul_fullAdelicCylinderMeasure_eq_haar_restrict
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S •
        L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S =
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
          E) := by
  dsimp only
  rw [L.cliffordGeneralSpinHorizontalDifferentialCylinderScale_smul_fullAdelicCylinderMeasure
    S]
  exact
    (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)).symm

/-- Equivalently, the differential full-adelic cylinder is the inverse named
scale times fixed horizontal Haar restricted to the same literal carrier. -/
theorem
    cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure_eq_inv_scale_smul_haar_restrict
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S =
      (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S)⁻¹ •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
            E) := by
  dsimp only
  let c := L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S
  let μ :=
    L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S
  let ν :=
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
      (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S))
  have h := congrArg (fun ρ : Measure _ => c⁻¹ • ρ)
    (L.cliffordGeneralSpinHorizontalDifferentialCylinderScale_smul_fullAdelicCylinderMeasure_eq_haar_restrict
      S)
  change c⁻¹ • c • μ = c⁻¹ • ν at h
  rw [smul_smul, ENNReal.inv_mul_cancel
      (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_zero S)
      (L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_top S),
    one_smul] at h
  exact h

end PositiveDefiniteIntegralLattice
