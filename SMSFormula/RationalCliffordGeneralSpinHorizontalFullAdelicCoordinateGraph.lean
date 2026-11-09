import SMSFormula.RationalCliffordGeneralSpinHorizontalFullAdelicChartParameter

/-!
# The full-adelic horizontal coordinate graph

The full-adelic chart coupling is upgraded from two separate marginals to an
exact graph identity.  First, the intrinsic full-adelic `(nu, pi)` map is
shown to commute literally with the established real--finite equivalences.
Next, the scalar/Spin split is packaged as a genuine homeomorphism, so its
coordinates reconstruct the original parameter and hence the corresponding
full-adelic `GSpin` point without a measurable choice.

The final measure theorem maps the coupling by the global `(nu, pi)`
coordinate and proves that it is the graph pushforward of the already
normalized scalar/Spin split measure.  Under dyadic retention its coefficient
is one.  This is the carrier-level graph needed for the subsequent ambient
Weil disintegration; no quotient or global disintegration is asserted here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3000000

local instance horizontalFullAdelicCoordinateGraphPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalFullAdelicCoordinateGraphDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalFullAdelicCoordinateGraphRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalFullAdelicCoordinateGraphRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalFullAdelicCoordinateGraphRealSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalFullAdelicCoordinateGraphRealSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalFullAdelicCoordinateGraphRealGSpinMeasurableSpace :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := borel _

noncomputable local instance horizontalFullAdelicCoordinateGraphRealGSpinBorelSpace :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := ⟨rfl⟩

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicGSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance horizontalFullAdelicCoordinateGraphPadicGSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

local instance horizontalFullAdelicCoordinateGraphIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalFullAdelicCoordinateGraphIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalFullAdelicCoordinateGraphTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalFullAdelicCoordinateGraphTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalFullAdelicCoordinateGraphFiniteMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFullAdelicCoordinateGraphFiniteBorelSpace :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalFullAdelicCoordinateGraphFullMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFullAdelicCoordinateGraphFullBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-! ## Global and real--finite `(nu, pi)` coordinates -/

/-- The literal global horizontal coordinate map `(nu, pi)` on full-adelic
intrinsic `GSpin`. -/
def cliffordGeneralSpinHorizontalFullAdelicCoordinate :
    V.FullAdelicCliffordGeneralSpinGroup →
      RationalAdeleˣ × V.FullAdelicSpecialOrthogonalGroup :=
  fun g ↦
    (V.fullAdelicCliffordGeneralSpinSimilitudeHom g,
      V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom g)

/-- The corresponding pair of real and finite horizontal coordinates. -/
def cliffordGeneralSpinHorizontalRealFiniteCoordinate :
    (V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) →
      (ℝˣ × RationalFiniteAdeleˣ) ×
        (V.RealSpecialOrthogonalGroup ×
          V.FiniteAdelicSpecialOrthogonalGroup) :=
  fun g ↦
    ((V.realCliffordGeneralSpinSimilitudeHom g.1,
        V.finiteAdelicCliffordGeneralSpinSimilitudeHom g.2),
      (V.realCliffordGeneralSpinToSpecialOrthogonalHom g.1,
        V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom g.2))

/-- The global `(nu, pi)` map commutes literally with both real--finite
equivalences. -/
theorem cliffordGeneralSpinHorizontalFullAdelicCoordinate_realFinite
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    (rationalAdeleUnitsRealFiniteContinuousEquiv
        (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate g).1,
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate g).2) =
      V.cliffordGeneralSpinHorizontalRealFiniteCoordinate
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g) := by
  unfold cliffordGeneralSpinHorizontalFullAdelicCoordinate
    cliffordGeneralSpinHorizontalRealFiniteCoordinate
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_similitude,
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_toSO]

/-- On the chart parameter source, the global coordinates are exactly the
real and finite coordinates of the constructed ambient point. -/
theorem cliffordGeneralSpinHorizontalFullAdelicChartParameter_coordinate_realFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S) :
    (rationalAdeleUnitsRealFiniteContinuousEquiv
        (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate
          (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S x)).1,
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate
          (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S x)).2) =
      V.cliffordGeneralSpinHorizontalRealFiniteCoordinate
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S x) := by
  rw [V.cliffordGeneralSpinHorizontalFullAdelicCoordinate_realFinite]
  unfold cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
  change V.cliffordGeneralSpinHorizontalRealFiniteCoordinate
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
          (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient S x))) = _
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]

/-! ## Reconstruction from the scalar/Spin split -/

/-- The complete real--finite scalar/Spin split is a homeomorphism.  The good
tail is unchanged literally. -/
def cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S ≃ₜ
      V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S :=
  (Homeomorph.Set.prod
      (Rat.unitSquareIdentityChart ℝ).source
      V.realCliffordSpinCandidateIdentityChart.source).prodCongr
    ((V.cliffordGeneralSpinHorizontalExceptionalChartSplitHomeomorph
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prodCongr
        (Homeomorph.refl _))

@[simp]
theorem cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S) :
    V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S x =
      V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S x :=
  rfl

/-- Reconstruct a full-adelic `GSpin` point from its scalar/Spin
coordinates by the inverse chart split and the certified ambient assembly. -/
def cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S →
      V.FullAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S ∘
    (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).symm

theorem measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S) := by
  exact
    (V.measurable_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S).comp
      (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).symm.measurable

/-- Splitting and reconstructing returns the exact full-adelic point produced
by the original parameter. -/
theorem cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_split
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S) :
    V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S
        (V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S x) =
      V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S x := by
  unfold cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
  rw [← V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph_apply S x,
    show
      (V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S ∘
          ⇑(V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).symm)
          (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S x) =
        V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S
          ((V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).symm
            (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S x)) from rfl,
    (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).symm_apply_apply]

/-! ## Exact graph pushforward -/

/-- Global `(nu, pi)` together with the scalar/Spin coordinates. -/
def cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalFullAdelicChartCouplingTarget S →
      (RationalAdeleˣ × V.FullAdelicSpecialOrthogonalGroup) ×
        V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S :=
  fun z ↦ (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate z.1, z.2)

/-- The same graph parametrized solely by the split coordinates. -/
def cliffordGeneralSpinHorizontalSplitCoordinateGraph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S →
      (RationalAdeleˣ × V.FullAdelicSpecialOrthogonalGroup) ×
        V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource S :=
  fun y ↦
    (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate
      (V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S y), y)

theorem measurable_cliffordGeneralSpinHorizontalFullAdelicCoordinate :
    Measurable V.cliffordGeneralSpinHorizontalFullAdelicCoordinate := by
  exact
    V.continuous_fullAdelicCliffordGeneralSpinSimilitudeHom.measurable.prodMk
      V.continuous_fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom.measurable

theorem measurable_cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph S) := by
  exact
    (V.measurable_cliffordGeneralSpinHorizontalFullAdelicCoordinate.comp
      measurable_fst).prodMk measurable_snd

theorem measurable_cliffordGeneralSpinHorizontalSplitCoordinateGraph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalSplitCoordinateGraph S) := by
  exact
    (V.measurable_cliffordGeneralSpinHorizontalFullAdelicCoordinate.comp
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S)).prodMk
        measurable_id

/-- Pointwise, the coupling lies on the graph reconstructed from its
scalar/Spin coordinate. -/
theorem cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.CliffordGeneralSpinHorizontalRealFiniteChartParameterSource S) :
    V.cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph S
        (V.cliffordGeneralSpinHorizontalFullAdelicChartCoupling S x) =
      V.cliffordGeneralSpinHorizontalSplitCoordinateGraph S
        (V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S x) := by
  apply Prod.ext
  · exact congrArg V.cliffordGeneralSpinHorizontalFullAdelicCoordinate
      (V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_split S x).symm
  · rfl

/-- After dyadic retention, applying global `(nu, pi)` to the ambient marginal
of the coupling gives exactly the graph pushforward of the scalar-one split
measure.  No coefficient remains outside the established block weight. -/
theorem map_cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph_of_dyadic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hdyadic : rationalIdeleDyadicPlace ∈
      S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph S)
        (V.cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure S) =
      Measure.map
        (V.cliffordGeneralSpinHorizontalSplitCoordinateGraph S)
        (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
          V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S) := by
  let coupling := V.cliffordGeneralSpinHorizontalFullAdelicChartCoupling S
  let fullGraph :=
    V.cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph S
  let split := V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S
  let splitGraph := V.cliffordGeneralSpinHorizontalSplitCoordinateGraph S
  have hcoupling : Measurable coupling :=
    V.measurable_cliffordGeneralSpinHorizontalFullAdelicChartCoupling S
  have hfullGraph : Measurable fullGraph :=
    V.measurable_cliffordGeneralSpinHorizontalFullAdelicCouplingCoordinateGraph S
  have hsplit : Measurable split := by
    exact (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).measurable
  have hsplitGraph : Measurable splitGraph :=
    V.measurable_cliffordGeneralSpinHorizontalSplitCoordinateGraph S
  unfold cliffordGeneralSpinHorizontalFullAdelicChartCouplingMeasure
  calc
    Measure.map fullGraph
        (Measure.map coupling
          (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S)) =
      Measure.map (fullGraph ∘ coupling)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) := by
          rw [Measure.map_map hfullGraph hcoupling]
    _ = Measure.map (splitGraph ∘ split)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) := by
      congr 1
    _ = Measure.map splitGraph
        (Measure.map split
          (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S)) := by
      rw [Measure.map_map hsplitGraph hsplit]
    _ = Measure.map splitGraph
        (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
          V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S) := by
      rw [V.map_cliffordGeneralSpinHorizontalRealFiniteChartSplit_of_dyadic S hdyadic]

/-- When the dyadic place lies in `S` or among the integral bad places, the global
`(nu, pi)` image of the coherent full-adelic cylinder is the pushforward of the
scalar-one split measure by the reconstructed global coordinate map.  Unlike the
preceding graph identity, this theorem has no coupling coordinate on either side;
it is stated directly in ambient coordinates, in the form used by the subsequent
specialized Weil disintegration. -/
theorem map_cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure_coordinate_of_dyadic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hdyadic : rationalIdeleDyadicPlace ∈
      S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    Measure.map
        V.cliffordGeneralSpinHorizontalFullAdelicCoordinate
        (V.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure S) =
      Measure.map
        (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate ∘
          V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S)
        (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
          V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S) := by
  let parameterToAmbient :=
    V.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S
  let split := V.cliffordGeneralSpinHorizontalRealFiniteChartSplit S
  let reconstructedCoordinate :=
    V.cliffordGeneralSpinHorizontalFullAdelicCoordinate ∘
      V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S
  have hparameterToAmbient : Measurable parameterToAmbient :=
    V.measurable_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S
  have hcoordinate :
      Measurable V.cliffordGeneralSpinHorizontalFullAdelicCoordinate :=
    V.measurable_cliffordGeneralSpinHorizontalFullAdelicCoordinate
  have hsplit : Measurable split :=
    (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph S).measurable
  have hreconstructedCoordinate : Measurable reconstructedCoordinate :=
    hcoordinate.comp
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic S)
  rw [← V.map_cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient S,
    Measure.map_map hcoordinate hparameterToAmbient]
  calc
    Measure.map
        (V.cliffordGeneralSpinHorizontalFullAdelicCoordinate ∘ parameterToAmbient)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) =
      Measure.map (reconstructedCoordinate ∘ split)
        (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S) := by
      congr 1
    _ = Measure.map reconstructedCoordinate
        (Measure.map split
          (V.cliffordGeneralSpinHorizontalRealFiniteChartParameterMeasure S)) := by
      rw [Measure.map_map hreconstructedCoordinate hsplit]
    _ = Measure.map reconstructedCoordinate
        (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
          V.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure S) := by
      rw [V.map_cliffordGeneralSpinHorizontalRealFiniteChartSplit_of_dyadic S hdyadic]

end RationalQuadraticSpaceMatrix
