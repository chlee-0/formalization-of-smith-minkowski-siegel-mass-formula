import SMSFormula.RationalCliffordGeneralSpinHorizontalRealFiniteChartParameter
import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicHaar

/-!
# Horizontal full-adelic chart parameters

The coherent real--finite horizontal identity-chart cylinders are transported
through the intrinsic full-adelic `GSpin` equivalence.  The joint local
scalar/Spin parameter map therefore lands on the full-adelic carrier,
and splitting the transported measure back into real and finite coordinates
recovers the real--finite cylinder exactly.

The final construction records the full-adelic `GSpin` point together with
its scalar/Spin chart coordinates in one coupling measure.  Its two marginals
are the transported ambient cylinder and the normalized split
measure.  When the dyadic place lies in the finite exceptional set, the second
marginal has scalar one by the certified real/dyadic cancellation.

No quotient comparison, global Weil disintegration, or Tamagawa-volume
identity is asserted here.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalFullAdelicChartParameterDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalFullAdelicChartParameterFiniteMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFullAdelicChartParameterFiniteBorelSpace :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalFullAdelicChartParameterFullMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFullAdelicChartParameterFullBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-! ## Transport to the intrinsic full-adelic carrier -/

/-- The coherent real--finite identity-chart cylinder transported to the
intrinsic full-adelic `GSpin` carrier. -/
def cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure V.FullAdelicCliffordGeneralSpinGroup :=
  Measure.map
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
    (V.cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure S)

/-- Splitting the transported full-adelic cylinder recovers the coherent
real--finite cylinder exactly. -/
theorem map_cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure_realFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (V.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure S := by
  unfold cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
  exact MeasurableEquiv.map_map_symm
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toMeasurableEquiv

/-- Joint central multiplication followed by assembly into the intrinsic
full-adelic `GSpin` carrier. -/
def cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S →
      V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm ∘
    V.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S

private theorem measurable_cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable
      (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S) := by
  unfold cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
  exact
    ((V.continuous_cliffordGeneralSpinCentralSpinMultiplication ℝ).measurable.comp
      continuous_subtype_val.measurable).prodMap
      (V.measurable_cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient S)

theorem measurable_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S) := by
  exact
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.measurable.comp
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S)

/-- The full-adelic parameter map pushes the literal parameter measure to the
transported coherent cylinder, without a conversion scalar. -/
theorem map_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure S := by
  unfold cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
    cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
  rw [← Measure.map_map]
  rw [V.map_cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S]
  · exact V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.measurable
  · exact V.measurable_cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S

/-! ## A coupling retaining the scalar/Spin coordinates -/

/-- The ambient full-adelic point together with the literal real--finite
scalar/Spin chart coordinates that produce it. -/
abbrev CliffordGeneralSpinHorizontalFullAdelicChartCouplingTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.FullAdelicCliffordGeneralSpinGroup ×
    V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S

/-- The graph map retaining both the full-adelic point and its unsimplified
scalar/Spin chart parameters. -/
def cliffordGeneralSpinHorizontalFullAdelicChartCoupling
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S →
      V.CliffordGeneralSpinHorizontalFullAdelicChartCouplingTarget S :=
  fun x ↦
    (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S x,
      V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S x)

theorem measurable_cliffordGeneralSpinHorizontalFullAdelicChartCoupling
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFullAdelicChartCoupling S) := by
  have hsplit :
      Measurable (V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S) := by
    unfold cliffordGeneralSpinHorizontalRealFiniteChartSplit
    exact
      (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℝ).source
          V.realCliffordSpinCandidateIdentityChart.source).measurable.prodMap
        ((V.measurable_cliffordGeneralSpinHorizontalExceptionalChartSplit
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prodMap measurable_id)
  exact
    (V.measurable_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S).prodMk
      hsplit

/-- The full coupling measure on the ambient point and its chart
coordinates. -/
def cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalFullAdelicChartCouplingTarget S) :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalFullAdelicChartCoupling S)
    (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S)

/-- The ambient marginal of the coupling is exactly the transported
full-adelic identity-chart cylinder. -/
theorem map_fst_cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map Prod.fst
        (V.cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure S := by
  unfold cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure
  rw [Measure.map_map measurable_fst
    (V.measurable_cliffordGeneralSpinHorizontalFullAdelicChartCoupling S)]
  change Measure.map
      (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S)
      (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) = _
  exact V.map_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S

/-- When the dyadic place lies in the finite exceptional set, the scalar/Spin
marginal of the full-adelic coupling has coefficient one: the real factor `2`
and dyadic factor `2⁻¹` cancel on this finite carrier. -/
theorem map_snd_cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure_of_dyadic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hdyadic : rationalIdeleDyadicPlace ∈
      S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    Measure.map Prod.snd
        (V.cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure S) =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
        V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S := by
  unfold cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure
  rw [Measure.map_map measurable_snd
    (V.measurable_cliffordGeneralSpinHorizontalFullAdelicChartCoupling S)]
  change Measure.map
      (V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S)
      (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) = _
  exact V.map_cliffordGeneralSpinHorizontalRealFiniteChartSplit_of_dyadic S hdyadic

end RationalQuadraticSpaceMatrix
