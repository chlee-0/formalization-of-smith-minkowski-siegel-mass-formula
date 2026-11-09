import SMSFormula.RationalCliffordGeneralSpinHorizontalExceptionalChartTransition
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicMeasure

/-!
# Horizontal identity-chart cylinders on genuine finite-adelic blocks

The direct exceptional/tail identity-chart transition is transported first to
the restricted-family principal blocks and then through the fixed-block
homeomorphisms to genuine intrinsic finite-adelic `GSpin` blocks.  The global
block weights cancel the finite transition volume exactly.

The final endpoints push the genuine cylinders into the common finite-adelic
carrier.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

local instance horizontalIdentityChartGenuineBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIdentityChartGenuineBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalIdentityChartGenuineBlockPadicGSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance horizontalIdentityChartGenuineBlockPadicGSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

local instance horizontalIdentityChartGenuineBlockIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalIdentityChartGenuineBlockIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalIdentityChartGenuineBlockExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalIdentityChartGenuineBlockExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalIdentityChartGenuineBlockTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalIdentityChartGenuineBlockTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalIdentityChartGenuineBlockFiniteGroupMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalIdentityChartGenuineBlockFiniteGroupBorelSpace :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalIdentityChartGenuineBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Restricted-family block cylinders -/

/-- The exceptional identity-chart source cylinder transported to the actual
restricted-family principal block. -/
def cliffordGeneralSpinHorizontalIdentityChartRestrictedPrincipalBlockMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S)
    (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S)

/-- The block-weighted identity-chart cylinder at `S`. -/
def cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :=
  V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
    V.cliffordGeneralSpinHorizontalIdentityChartRestrictedPrincipalBlockMeasure S

/-! ## Genuine block cylinders -/

/-- The coherent identity-chart cylinder transported to the genuine
finite-adelic block. -/
def cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm
    (V.cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure S)

theorem
    cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure_eq_comap
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure S =
      (V.cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure S).comap
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S) := by
  let e := V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
  let μ :=
    V.cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure S
  change Measure.map e.symm μ = μ.comap e
  calc
    Measure.map e.symm μ = (Measure.map e (Measure.map e.symm μ)).comap e := by
      rw [e.measurableEmbedding.comap_map]
    _ = μ.comap e := by
      exact congrArg (fun ν : Measure _ ↦ ν.comap e)
        (MeasurableEquiv.map_map_symm e.toMeasurableEquiv)

/-! ## Common finite-adelic carrier -/

/-- The coherent identity-chart cylinder pushed into the common intrinsic
finite-adelic carrier. -/
def cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure V.FiniteAdelicCliffordGeneralSpinGroup :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S)
    (V.cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure S)

/-! ## Attachment of the real identity chart -/

/-- The literal restriction of the fixed real horizontal Haar measure to its
central-fiber identity chart. -/
def realCliffordGeneralSpinHorizontalIdentityChartAmbientMeasure :
    Measure V.RealCliffordGeneralSpinGroup :=
  V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
    V.realCliffordGeneralSpinCentralFiberIdentityChart.source

/-- The real identity chart times a coherent finite-adelic identity-chart
cylinder on the common real--finite carrier. -/
def cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :=
  V.realCliffordGeneralSpinHorizontalIdentityChartAmbientMeasure.prod
    (V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S)

end RationalQuadraticSpaceMatrix
