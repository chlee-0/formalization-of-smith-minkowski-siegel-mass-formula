import SMSFormula.RationalCliffordGeneralSpinHorizontalFullCentralOrbitChart
import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberBind
import SMSFormula.RationalIdeleDifferentialSquareChartRestriction

/-!
# Restricting ambient differential central fibers to the horizontal chart

The exact full-adelic central-orbit/chart intersection gives a measure
identity here.  Differential idele Haar restricts along an ambient central
orbit to the full square chart, and the same formula is then
recorded for the descended `SO`-indexed central fiber.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalAmbientFiberRestrictionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalAmbientFiberRestrictionFullGSpinMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup := borel _

local instance horizontalAmbientFiberRestrictionFullGSpinBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup := ⟨rfl⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-- The literal full central orbit is measurable. -/
theorem measurable_cliffordGeneralSpinHorizontalFullCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    Measurable
      (V.cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g) := by
  exact
    (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_id).mul continuous_const |>.measurable

/-- Restricting a literal differential central orbit to the certified
`GSpin` identity carrier is exactly restriction of differential idele Haar to
the full square chart. -/
theorem fullAdelicDifferentialCentralFiberKernel_restrict_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (hsReal : sReal ∈ V.realCliffordSpinCandidateIdentityChart.source)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    (V.fullAdelicDifferentialCentralFiberKernel
        (V.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
          S sReal sFinite g)).restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) =
      Measure.map
        (V.cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g)
        (rationalIdeleDifferentialHaarMeasure.restrict
          (rationalIdeleDifferentialFullSquareChartCarrier
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))) := by
  rw [V.fullAdelicDifferentialCentralFiberKernel_apply]
  change
    (Measure.map
        (V.cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g)
        rationalIdeleDifferentialHaarMeasure).restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) = _
  rw [Measure.restrict_map
    (V.measurable_cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g)
    (V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S)]
  rw [V.preimage_cliffordGeneralSpinHorizontalFullCentralOrbit_identityChart
    S sReal hsReal sFinite g]

/-- After inserting the exact differential square-chart restriction, the
restricted central fiber is the pushforward of the bare square-chart
measure. -/
theorem fullAdelicDifferentialCentralFiberKernel_restrict_identityChart_eq_map_squareChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (hsReal : sReal ∈ V.realCliffordSpinCandidateIdentityChart.source)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    (V.fullAdelicDifferentialCentralFiberKernel
        (V.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
          S sReal sFinite g)).restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) =
      Measure.map
        (V.cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g ∘
          rationalIdeleDifferentialFullSquareChartToAmbient
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
        (rationalIdeleDifferentialFullSquareChartSourceMeasure
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
  rw [V.fullAdelicDifferentialCentralFiberKernel_restrict_identityChart
    S sReal hsReal sFinite g]
  rw [rationalIdeleDifferentialHaarMeasure_restrict_squareChart]
  rw [Measure.map_map
    (V.measurable_cliffordGeneralSpinHorizontalFullCentralOrbit
      S sReal sFinite g)
    ((measurableEmbedding_rationalIdeleDifferentialFullSquareChartToAmbient
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).measurable)]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalDescendedFiberRestrictionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalDescendedFiberRestrictionFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalDescendedFiberRestrictionFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The descended `SO`-indexed ambient central fiber has the same exact
restriction formula when evaluated at the projection of the certified chart
origin. -/
theorem fullAdelicDifferentialCentralFiberKernelAtSO_restrict_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup)
    (hsReal : sReal ∈
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source)
    (sFinite :
      L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalExceptionalSOChartSource
        (S ∪ L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S) :
    (L.fullAdelicDifferentialCentralFiberKernelAtSO
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
          (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
            S sReal sFinite g))).restrict
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
          S) =
      Measure.map
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullCentralOrbit
          S sReal sFinite g ∘
            RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
              (S ∪
                L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure
          (S ∪
            L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
  rw [L.fullAdelicDifferentialCentralFiberKernelAtSO_comp_projection]
  exact
    L.rationalQuadraticSpaceMatrix.fullAdelicDifferentialCentralFiberKernel_restrict_identityChart_eq_map_squareChart
      S sReal hsReal sFinite g

end PositiveDefiniteIntegralLattice
