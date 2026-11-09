import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberCylinderReassociation

/-!
# Support of the ambient differential central fibers on a horizontal cylinder

The projection of the certified full-adelic `GSpin` identity carrier lies in
the matching literal `SO` chart carrier.  Since every ambient central fiber is
supported on one exact `SO` fiber, a base point outside that `SO` chart gives
the `GSpin` carrier zero mass.  This removes the complementary base before the
weighted chart bind is evaluated.

No measurable section, Cartesian central-extension presentation, new chart,
or normalization scalar is introduced.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

local instance horizontalAmbientCentralFiberSupportPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalAmbientCentralFiberSupportDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalAmbientCentralFiberSupportFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberSupportFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberSupportFullSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberSupportFullSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

noncomputable local instance horizontalAmbientCentralFiberSupportPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalAmbientCentralFiberSupportPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalAmbientCentralFiberSupportRealSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealSpecialOrthogonalGroup :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalAmbientCentralFiberSupportRealSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealSpecialOrthogonalGroup :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalAmbientCentralFiberSupportHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalAmbientCentralFiberSupportHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalAmbientCentralFiberSupportHeightOneSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalAmbientCentralFiberSupportFiniteSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberSupportFiniteSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberSupportExceptionalSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAmbientCentralFiberSupportExceptionalSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalExceptionalProduct B) :=
  Pi.borelSpace

local instance horizontalAmbientCentralFiberSupportIntegralSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ B}) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalAmbientCentralFiberSupportIntegralSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ B}) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance horizontalAmbientCentralFiberSupportIntegralSOTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAmbientCentralFiberSupportIntegralSOTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail B) :=
  Pi.borelSpace

local instance horizontalAmbientCentralFiberSupportLocalSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalAmbientCentralFiberSupportLocalSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor B v) :=
  Subtype.borelSpace _

local instance horizontalAmbientCentralFiberSupportMixedSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAmbientCentralFiberSupportMixedSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock B) :=
  Pi.borelSpace

local instance horizontalAmbientCentralFiberSupportGenuineSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock B) :=
  borel _

local instance horizontalAmbientCentralFiberSupportGenuineSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock B) :=
  ⟨rfl⟩

/-! ## Projection of the certified `GSpin` carrier -/

/-- Every point of the certified full-adelic `GSpin` identity carrier projects
into the matching literal full `SO` chart carrier. -/
theorem
    fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_mem_fullSOChartCarrier_of_mem_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup}
    (hg : g ∈
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
        S) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom g ∈
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartCarrier
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  let V := L.rationalQuadraticSpaceMatrix
  let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  rcases hg with ⟨z, hz, rfl⟩
  rcases hz.2 with ⟨x, hx, hxz⟩
  let realTarget : V.realCliffordSpinCandidateIdentityChart.target :=
    ⟨V.realCliffordGeneralSpinToSpecialOrthogonalHom z.1, by
      have h := V.realCliffordGeneralSpinCentralFiberIdentityChart.map_source hz.1
      exact h.2⟩
  let sReal : V.realCliffordSpinCandidateIdentityChart.source :=
    V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.symm realTarget
  have hsReal :
      V.realCliffordSpinCandidateToSpecialOrthogonalHom sReal =
        V.realCliffordGeneralSpinToSpecialOrthogonalHom z.1 := by
    have h :=
      V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.apply_symm_apply
        realTarget
    simpa only [V.realCliffordSpinCandidateIdentityChart_coe] using
      congrArg Subtype.val h
  let sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource B :=
    fun v ↦
      (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).toHomeomorphSourceTarget.symm
        ⟨V.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 (x.1 v), by
          have h :=
            (V.padicCliffordGeneralSpinCentralFiberIdentityChart
              (Rat.HeightOneSpectrum.primesEquiv v.1).1).map_source
                (hx.1 v (Set.mem_univ v))
          exact h.2⟩
  have hsFinite (v : {v // v ∈ B}) :
      V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (sFinite v) =
        V.padicCliffordGeneralSpinToSpecialOrthogonalHom
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 (x.1 v) := by
    have h :=
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).toHomeomorphSourceTarget.apply_symm_apply
          ⟨V.padicCliffordGeneralSpinToSpecialOrthogonalHom
              (Rat.HeightOneSpectrum.primesEquiv v.1).1 (x.1 v), by
            have hm :=
              (V.padicCliffordGeneralSpinCentralFiberIdentityChart
                (Rat.HeightOneSpectrum.primesEquiv v.1).1).map_source
                  (hx.1 v (Set.mem_univ v))
            exact hm.2⟩
    simpa only [V.padicCliffordSpinCandidateIdentityChart_coe] using
      congrArg Subtype.val h
  let tFinite : V.FiniteAdelicSpecialOrthogonalIntegralTail B :=
    fun v ↦
      V.padicCliffordGeneralSpinHorizontalIntegralToSO S
        ⟨v.1, v.2⟩
        (x.2 ⟨v.1, v.2⟩)
  let source : V.CliffordGeneralSpinHorizontalFullSOChartSource B :=
    (sReal, sFinite, tFinite)
  refine ⟨source, ?_⟩
  apply V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.injective
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_toSO]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartToAmbient
  simp only [Function.comp_apply]
  rw [V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply,
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]
  apply Prod.ext
  · exact hsReal
  · change
      V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient B source.2 =
        V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom z.2
    apply V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom_injective
    funext v
    change
      V.finiteAdelicSpecialOrthogonalHeightOneComponent
          (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient B source.2) v =
        V.finiteAdelicSpecialOrthogonalHeightOneComponent
          (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom z.2) v
    rw [L.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient_component B source.2 v]
    have hnatur := DFunLike.congr_fun
      (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality
        V (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v))
      z.2
    change
      V.specialOrthogonalMatrixGroupMap
          (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
          (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom z.2) =
        V.padicCliffordGeneralSpinToSpecialOrthogonalHom
          (Rat.HeightOneSpectrum.primesEquiv v).1
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z.2)
      at hnatur
    rw [show
      V.finiteAdelicSpecialOrthogonalHeightOneComponent
          (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom z.2) v =
        V.padicCliffordGeneralSpinToSpecialOrthogonalHom
          (Rat.HeightOneSpectrum.primesEquiv v).1
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z.2) by
      exact hnatur]
    have hcomponent := congrArg
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v) hxz
    rw [← hcomponent]
    rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient
      S x v]
    by_cases hv : v ∈ B
    · have hv' : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := hv
      rw [dif_pos hv, dif_pos hv']
      exact hsFinite ⟨v, hv⟩
    · have hv' : v ∉ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := hv
      rw [dif_neg hv, dif_neg hv']
      rfl

/-! ## Complementary-fiber vanishing -/

/-- A descended central fiber indexed outside the matching full `SO` chart
gives the certified `GSpin` identity carrier zero mass. -/
theorem
    fullAdelicDifferentialCentralFiberKernelAtSO_apply_identityChart_eq_zero_of_not_mem_fullSOChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hh : h ∉
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartCarrier
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.fullAdelicDifferentialCentralFiberKernelAtSO h
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
          S) = 0 := by
  let V := L.rationalQuadraticSpaceMatrix
  let x := L.fullAdelicDifferentialCentralFiberLift h
  let orbit := fun a : RationalAdeleˣ ↦
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele a * x
  have horbit : Measurable orbit :=
    (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_id).mul continuous_const |>.measurable
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S
  have hC : MeasurableSet C :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S
  rw [L.fullAdelicDifferentialCentralFiberKernelAtSO_apply]
  unfold fullAdelicDifferentialCentralFiberMeasureAtSO
  rw [V.fullAdelicDifferentialCentralFiberKernel_apply]
  rw [Measure.map_apply horbit hC]
  have hpreimage : orbit ⁻¹' C = ∅ := by
    ext a
    constructor
    · intro ha
      exfalso
      apply hh
      have horbitSO :=
        L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_mem_fullSOChartCarrier_of_mem_identityChart
          S ha
      have hprojection :
          V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom (orbit a) = h := by
        have hscalar :
            RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V RationalAdele a ∈
              (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                V RationalAdele).ker := by
          rw [← RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
          exact ⟨a, rfl⟩
        change
          V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V RationalAdele a) = 1 at hscalar
        unfold orbit
        rw [map_mul, hscalar, L.fullAdelicDifferentialCentralFiberLift_spec]
        simp
      rwa [hprojection] at horbitSO
    · intro ha
      simp at ha
  rw [hpreimage]
  simp

/-- Pointwise outside the matching `SO` chart, the already measurable
restricted ambient kernel is the zero measure. -/
theorem
    fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply_eq_zero_of_not_mem_fullSOChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hh : h ∉
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartCarrier
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart S h = 0 := by
  rw [L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply,
    Measure.restrict_eq_zero]
  exact
    L.fullAdelicDifferentialCentralFiberKernelAtSO_apply_identityChart_eq_zero_of_not_mem_fullSOChart
      S h hh

/-! ## Removing the complementary base -/

/-- The already defined full `SO` chart carrier is measurable.  This merely
exports the measurable-embedding argument used inside its Haar-restriction
theorem. -/
theorem measurableSet_cliffordGeneralSpinHorizontalFullSOChartCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartCarrier B) := by
  let V := L.rationalQuadraticSpaceMatrix
  let realMap := fun x : V.realCliffordSpinCandidateIdentityChart.source ↦
    V.realCliffordSpinCandidateToSpecialOrthogonalHom x
  let finiteMap := V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient B
  have hreal : MeasurableEmbedding realMap := by
    have h := V.realCliffordSpinCandidateIdentityChart.open_target
      |>.isOpenEmbedding_subtypeVal.comp
        V.realCliffordSpinCandidateIdentityChart.toHomeomorphSourceTarget.isOpenEmbedding
    simpa only [realMap, V.realCliffordSpinCandidateIdentityChart_coe] using
      h.measurableEmbedding
  have hfinite : MeasurableEmbedding finiteMap := by
    exact
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding B).comp
        ((V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph B).symm.measurableEmbedding.comp
          ((V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph B).measurableEmbedding.comp
            ((V.measurableEmbedding_cliffordGeneralSpinHorizontalExceptionalSOChartToProduct B).prodMap
              MeasurableEmbedding.id)))
  have hfull : MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B) :=
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.measurableEmbedding.comp
      (hreal.prodMap hfinite)
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartCarrier
  rw [← Set.image_univ]
  exact hfull.measurableSet_image.mpr MeasurableSet.univ

/-- The restricted ambient fiber kernel bound over the complement of the full
`SO` chart is the zero measure. -/
theorem
    fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_restrict_compl_fullSOChart_eq_zero
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart S ∘ₘ
        (V.fullAdelicInvariantDifferentialGroupMeasure.restrict
          (V.cliffordGeneralSpinHorizontalFullSOChartCarrier B)ᶜ) = 0 := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let D := V.cliffordGeneralSpinHorizontalFullSOChartCarrier B
  let κ := L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart S
  let μ := V.fullAdelicInvariantDifferentialGroupMeasure
  have hD : MeasurableSet D :=
    L.measurableSet_cliffordGeneralSpinHorizontalFullSOChartCarrier B
  change κ ∘ₘ μ.restrict Dᶜ = 0
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA κ.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [MeasureTheory.ae_restrict_mem hD.compl] with h hh
  have hzero :=
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply_eq_zero_of_not_mem_fullSOChart
      S h hh
  rw [hzero]
  simp

/-- Restricting the normalized ambient central-fiber bind to the certified
`GSpin` carrier gives exactly the absolute finite `SO` block weight times
the calibrated differential full-adelic cylinder. -/
theorem
    fullAdelicInvariantDifferentialCentralFiberBoundMeasure_restrict_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure.restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      V.finiteAdelicSpecialOrthogonalBlockWeight B •
        L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  let D := V.cliffordGeneralSpinHorizontalFullSOChartCarrier B
  let κ := L.fullAdelicDifferentialCentralFiberKernelAtSO
  let η := L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E
  let μ := V.fullAdelicInvariantDifferentialGroupMeasure
  have hC : MeasurableSet C :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hD : MeasurableSet D :=
    L.measurableSet_cliffordGeneralSpinHorizontalFullSOChartCarrier B
  have hrestrict : (κ ∘ₘ μ).restrict C = η ∘ₘ μ := by
    apply Measure.ext
    intro A hA
    rw [Measure.restrict_apply hA,
      Measure.bind_apply (hA.inter hC) κ.aemeasurable,
      Measure.bind_apply hA η.aemeasurable]
    apply lintegral_congr
    intro h
    rw [L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply,
      Measure.restrict_apply hA]
  have hcompl : η ∘ₘ μ.restrict Dᶜ = 0 :=
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_restrict_compl_fullSOChart_eq_zero
      E
  unfold fullAdelicInvariantDifferentialCentralFiberBoundMeasure
  change (κ ∘ₘ μ).restrict C = _
  rw [hrestrict]
  calc
    η ∘ₘ μ = η ∘ₘ (μ.restrict D + μ.restrict Dᶜ) := by
      rw [Measure.restrict_add_restrict_compl hD]
    _ = η ∘ₘ μ.restrict D + η ∘ₘ μ.restrict Dᶜ := by
      rw [Measure.comp_add]
    _ = η ∘ₘ μ.restrict D := by rw [hcompl, add_zero]
    _ = V.finiteAdelicSpecialOrthogonalBlockWeight B •
        ((ProbabilityTheory.Kernel.comap η
            (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
            (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)) ∘ₘ
          V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B) := by
      exact
        L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_restrict_fullSOChart
          S
    _ = V.finiteAdelicSpecialOrthogonalBlockWeight B •
        L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S := by
      rw [L.comap_fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_fullSOChartSourceMeasure
        S]

end PositiveDefiniteIntegralLattice
