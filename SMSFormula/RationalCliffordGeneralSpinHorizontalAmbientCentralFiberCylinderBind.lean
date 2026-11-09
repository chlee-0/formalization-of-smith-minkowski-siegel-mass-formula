import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberRestriction
import SMSFormula.RationalCliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelic

/-!
# Binding restricted ambient central fibers over the horizontal SO chart

This file connects the pointwise descended ambient-fiber restriction with the
existing absolute-weighted differential `SO` chart.  The first compatibility
identifies the full `SO` chart point with the projection of the canonical
full-adelic `GSpin` orbit origin used by the fiber theorem.
-/

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalAmbientFiberCylinderBindDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalAmbientFiberCylinderBindPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance horizontalAmbientFiberCylinderBindHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalAmbientFiberCylinderBindHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalAmbientFiberCylinderBindHeightOneSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalAmbientFiberCylinderBindIntegralSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance horizontalAmbientFiberCylinderBindIntegralSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalAmbientFiberCylinderBindIntegralSOTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAmbientFiberCylinderBindIntegralSOTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-- Height-one evaluation of the literal finite `SO` chart assembly recovers
the displayed exceptional or integral-tail source coordinate. -/
theorem cliffordGeneralSpinHorizontalFiniteSOChartToAmbient_component
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFiniteSOChartSource B)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalHeightOneComponent
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
          B x) v =
      if hv : v ∈ B then
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (x.1 ⟨v, hv⟩)
      else
        (x.2 ⟨v, hv⟩).1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let y :=
    (V.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct B x.1, x.2)
  let m := V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph B y
  let a := (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph B).symm m
  have hgenuine :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv_apply_component
      B a v
  have hmixed :
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph B a = m :=
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph B).apply_symm_apply m
  change V.finiteAdelicSpecialOrthogonalHeightOneComponent a.1 v = _
  by_cases hv : v ∈ B
  · have hexception :=
      V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_apply_mem
        B y v hv
    calc
      _ = (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph B a v).1 :=
        hgenuine.symm
      _ = (m v).1 := congrArg (fun z => (z v).1) hmixed
      _ = y.1 ⟨v, hv⟩ := hexception
      _ = _ := by
        rw [dif_pos hv]
        dsimp [y,
          RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalSOChartToProduct]
  · have htail :=
      V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_apply_notMem
        B y v hv
    calc
      _ = (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph B a v).1 :=
        hgenuine.symm
      _ = (m v).1 := congrArg (fun z => (z v).1) hmixed
      _ = (y.2 ⟨v, hv⟩).1 := htail
      _ = _ := by simp [y, hv]

/-- Canonical `GSpin` origin above a full `SO` chart source point.  The only
choice is the existing definition-only lift of the normalized integral good
tail. -/
noncomputable def cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  V.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
    E x.1 x.2.1
      (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
          (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
          (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
        x.2.2)

/-- The canonical `GSpin` origin projects to the full `SO` chart map. -/
theorem fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_fullSOChartGSpinOrigin
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartToAmbient
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) x := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  apply V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.injective
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_toSO]
  unfold cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartToAmbient
  simp only [Function.comp_apply]
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply,
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply]
  change
    (V.realCliffordGeneralSpinToSpecialOrthogonalHom
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ x.1),
      V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) =
      (V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1,
        V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
          (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) (x.2.1, x.2.2))
  apply Prod.ext
  · rfl
  · apply V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom_injective
    funext v
    by_cases hv : v ∈ E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    · change
        V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) v =
          V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
              (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) (x.2.1, x.2.2)) v
      have hnatur := DFunLike.congr_fun
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality
          V (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v))
        (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)
      change
        V.specialOrthogonalMatrixGroupMap
            (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
            (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) =
          V.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v).1
            (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g))
          at hnatur
      rw [show
        V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) v =
          V.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v).1
            (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) by
          exact hnatur]
      have hcomponent :=
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient
          E
          ((fun w ↦ V.cliffordSpinCandidateToCliffordGeneralSpinHom
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv w.1).1] (x.2.1 w)), g) v
      rw [show
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
            (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g) =
          V.cliffordSpinCandidateToCliffordGeneralSpinHom
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (x.2.1 ⟨v, hv⟩) by
          simpa [RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
            hv] using hcomponent]
      rw [L.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient_component
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) (x.2.1, x.2.2) v]
      simp only [dif_pos hv]
      rfl
    · change
        V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) v =
          V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (V.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient
              (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) (x.2.1, x.2.2)) v
      let vg : V.CliffordGeneralSpinHorizontalIntegralPlace E := ⟨v, hv⟩
      have hnatur := DFunLike.congr_fun
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality
          V (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v))
        (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)
      change
        V.specialOrthogonalMatrixGroupMap
            (RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v)
            (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) =
          V.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v).1
            (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g))
          at hnatur
      rw [show
        V.finiteAdelicSpecialOrthogonalHeightOneComponent
            (V.finiteAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) v =
          V.padicCliffordGeneralSpinToSpecialOrthogonalHom
            (Rat.HeightOneSpectrum.primesEquiv v).1
            (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
              (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g)) by
          exact hnatur]
      have hcomponent :=
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient
          E
          ((fun w ↦ V.cliffordSpinCandidateToCliffordGeneralSpinHom
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv w.1).1] (x.2.1 w)), g) v
      rw [show
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
            (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g) =
          (g vg).1 by
          simpa [RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin,
            hv, vg] using hcomponent]
      rw [L.cliffordGeneralSpinHorizontalFiniteSOChartToAmbient_component
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) (x.2.1, x.2.2) v]
      simp only [dif_neg hv]
      have htail := congrFun
        (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift_spec E
          (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
            (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
          (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
            (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2) vg
      exact congrArg Subtype.val htail

/-- The descended ambient central fiber restricted above a full `SO` chart
point is the bare differential square-chart orbit through the canonical
`GSpin` origin. -/
theorem fullAdelicDifferentialCentralFiberKernelAtSO_restrict_fullSOChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
    (L.fullAdelicDifferentialCentralFiberKernelAtSO
        (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B x)).restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      Measure.map
        (V.cliffordGeneralSpinHorizontalFullCentralOrbit E x.1 x.2.1 g ∘
          RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B)
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B) := by
  dsimp only
  rw [← L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_fullSOChartGSpinOrigin S x]
  exact L.fullAdelicDifferentialCentralFiberKernelAtSO_restrict_identityChart
    (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)
    x.1 x.1.2 x.2.1
    (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2)

/-! ## The restricted ambient kernel on the literal SO chart -/

/-- Restrict every descended ambient differential central fiber to the
certified full-adelic `GSpin` identity carrier. -/
noncomputable def fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.Kernel
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  L.fullAdelicDifferentialCentralFiberKernelAtSO.restrict
    (L.rationalQuadraticSpaceMatrix.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
      S)

@[simp]
theorem fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart S h =
      (L.fullAdelicDifferentialCentralFiberKernelAtSO h).restrict
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
          S) := by
  exact ProbabilityTheory.Kernel.restrict_apply _ _ _

/-- Pulling the restricted ambient kernel back to the bare full `SO` chart
source gives pointwise the exact differential square-chart orbit measure.
The definition-only good-tail lift disappears from the base through the
already descended kernel. -/
theorem comap_fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
    (ProbabilityTheory.Kernel.comap
        (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
        (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
        (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)) x =
      Measure.map
        (V.cliffordGeneralSpinHorizontalFullCentralOrbit E x.1 x.2.1 g ∘
          RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B)
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B) := by
  dsimp only
  rw [ProbabilityTheory.Kernel.comap_apply,
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply]
  exact L.fullAdelicDifferentialCentralFiberKernelAtSO_restrict_fullSOChart S x

/-- Binding the restricted ambient kernel over the mapped bare `SO` chart is
exactly binding its pullback over the literal chart source.  This is the
measure-theoretic base-change needed before the remaining scalar/Spin source
reassociation; it introduces no coefficient. -/
theorem
    fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_map_fullSOChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E ∘ₘ
        Measure.map
          (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
          (V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B) =
      (ProbabilityTheory.Kernel.comap
          (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
          (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
          (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)) ∘ₘ
        V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B := by
  dsimp only
  rw [← Measure.deterministic_comp_eq_map
      (L.rationalQuadraticSpaceMatrix.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)),
    Measure.comp_assoc,
    ProbabilityTheory.Kernel.comp_deterministic_eq_comap]

/-- Binding over the ambient differential `SO` chart restriction retains
exactly its absolute finite block weight.  All fiber geometry is on the bare
chart source; no other normalization appears. -/
theorem
    fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_restrict_fullSOChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E ∘ₘ
        (V.fullAdelicInvariantDifferentialGroupMeasure.restrict
          (V.cliffordGeneralSpinHorizontalFullSOChartCarrier B)) =
      V.finiteAdelicSpecialOrthogonalBlockWeight B •
        ((ProbabilityTheory.Kernel.comap
            (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
            (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
            (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)) ∘ₘ
          V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B) := by
  dsimp only
  rw [L.rationalQuadraticSpaceMatrix.fullAdelicInvariantDifferentialGroupMeasure_restrict_horizontalSOChart,
    Measure.bind_smul,
    L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_map_fullSOChart]

end PositiveDefiniteIntegralLattice
