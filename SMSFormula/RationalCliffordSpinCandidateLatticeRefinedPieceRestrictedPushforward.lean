import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteSpinClassHorizontalConcrete
import Mathlib.Probability.ProductMeasure
import SMSFormula.RationalCliffordSpinCandidateLatticeGoodIntegralPointMapPushforward
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit
import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSpinorRange
import SMSFormula.RationalCliffordSpinCandidateAlmostEverywhereIntegralLifting
import SMSFormula.RationalSquareClassFiniteLocalizationSurjectivity
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FieldSimp
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteAdelicStabilizerCarrier
import SMSFormula.SpecialOrthogonalFiniteAdelicDifferentialSelectorMass
import SMSFormula.AdelicLeftCosets
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSOSurjectivity
import SMSFormula.RationalCliffordGeneralSpinAdelicProduct
import SMSFormula.RationalCliffordGeneralSpinVerticalEquivalence
import SMSFormula.RationalCliffordGeneralSpinAdelicSpecialOrthogonalQuotient
import SMSFormula.RationalCliffordSpinCandidateLatticeProperDomainSelectorSourceMap
import SMSFormula.SpecialOrthogonalFullAdelicProperPieceDifferentialMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import SMSFormula.RationalCliffordGeneralSpinVerticalSpecialOrthogonalProjection
import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalCliffordSpinCandidateAdelicLeftQuotientTopology
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued
import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicRestrictedFamilyCarrier
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicRestrictedFamilyGroup
import SMSFormula.RationalSpecialOrthogonalAdelicSpinorNormDiagonal
import SMSFormula.RationalSpecialOrthogonalTamagawa
import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup
import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaData
import SMSFormula.RationalCliffordSpinCandidateCanonicalRightQuotient
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductPrecursor
import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction
import SMSFormula.RationalCliffordSpinCandidatePlacewiseFiniteSheetHaar
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockCylinderMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDifferentialScale
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicGenuineBlockCoherence
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicGenuinePrincipalBlockCarrier
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDirectedMeasure
import SMSFormula.RationalCliffordSpinCandidateAdelicProduct
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialMeasure

/-!
# Restricted point-map measures of refined real--finite Spin pieces

Put the exact transported Spin fundamental-domain restriction into the
real--finite product point-map pushforward.  Every refined ambient Spin mass
is then the value of this literal restricted pushforward on the corresponding
proper-selector target.

For comparison, also record the already evaluated pushforward before the
fundamental-domain restriction.  This separates the remaining finite-sheet
calculation from the completed local two-sheet calculation without comparing
the singular limiting quotient measures.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance restrictedPushforwardRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance restrictedPushforwardRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance restrictedPushforwardFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance restrictedPushforwardFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance restrictedPushforwardRealSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealSpecialOrthogonalGroup :=
  borel _

local instance restrictedPushforwardRealSOBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance restrictedPushforwardFiniteSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance restrictedPushforwardFiniteSOBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance restrictedPushforwardRealSOMatrixMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  borel _

local instance restrictedPushforwardRealSOMatrixBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  ⟨rfl⟩

local instance restrictedPushforwardFiniteSOMatrixMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup RationalFiniteAdele) :=
  borel _

local instance restrictedPushforwardFiniteSOMatrixBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup RationalFiniteAdele) :=
  ⟨rfl⟩

/-- The raw real--finite Spin product measure used by the exact lattice datum. -/
noncomputable def cliffordSpinCandidateRealFiniteRawMeasure
    (L : PositiveDefiniteIntegralLattice n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData) :
    Measure (L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup ×
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup) :=
  L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateChartGluedMeasure.prod
    (L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
      D.spinFiniteScale)

end PositiveDefiniteIntegralLattice

end
