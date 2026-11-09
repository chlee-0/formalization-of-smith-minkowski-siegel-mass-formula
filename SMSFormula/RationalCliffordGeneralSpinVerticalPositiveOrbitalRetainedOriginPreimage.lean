import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRealFiniteRestriction
import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberCylinderBind

/-!
# Component preimages of the retained central-orbit origin

The canonical retained `GSpin` origin splits into its embedded real
Spin point and finite central-orbit origin.  Consequently its real--finite
Spin-orbit preimage of the identity carrier is a Cartesian product of explicit
real and finite preimages.  The raw product measure and the descended orbital
kernel therefore evaluate as the product of those two component masses.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance retainedOriginPreimageDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedOriginPreimageRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedOriginPreimageRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedOriginPreimageFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedOriginPreimageFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedOriginPreimageRealGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  borel _

local instance retainedOriginPreimageRealGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedOriginPreimageFiniteGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedOriginPreimageFiniteGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The canonical retained full `GSpin` origin has the real--finite
components used in its definition. -/
theorem fullSOChartGSpinOrigin_realFinite
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x) =
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ x.1,
        V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g) := by
  dsimp only
  unfold cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
  exact L.rationalQuadraticSpaceMatrix
    |>.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply _

/-- Real Spin points whose translation of the retained real origin remains in
the real identity carrier. -/
def cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Set L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  {y | L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ y *
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ x.1 ∈
        L.rationalQuadraticSpaceMatrix.realCliffordGeneralSpinCentralFiberIdentityChart.source}

/-- Finite Spin points whose translation of the retained finite origin remains
in the finite identity carrier. -/
def cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Set L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  {y | V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y *
      V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g ∈
        V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier E}

/-- The retained-origin orbit preimage splits into the real and finite
component preimages. -/
theorem preimage_cliffordSpinCandidateRealFiniteOrbitAt_fullSOChartGSpinOrigin
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    V.cliffordSpinCandidateRealFiniteOrbitAt
        (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x) ⁻¹'
        V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) =
      L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
        L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x := by
  dsimp only
  unfold RationalQuadraticSpaceMatrix.cliffordSpinCandidateRealFiniteOrbitAt
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
    cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage
    cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage
  dsimp only
  rw [show
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x) = _ by
      exact L.fullSOChartGSpinOrigin_realFinite S x]
  rfl

theorem measurableSet_cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    MeasurableSet
      (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x) := by
  exact
    L.rationalQuadraticSpaceMatrix.realCliffordGeneralSpinCentralFiberIdentityChart
      |>.open_source.measurableSet.preimage
        ((L.rationalQuadraticSpaceMatrix
          |>.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom ℝ).mul
            continuous_const).measurable

theorem measurableSet_cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    MeasurableSet
      (L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  exact
    (V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier E).preimage
      ((V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
        RationalFiniteAdele).mul continuous_const).measurable

/-- Raw real--finite Spin mass of the retained-origin carrier preimage is the
product of its explicit component masses. -/
theorem cliffordSpinCandidateRealFiniteRawMeasure_spinOrbit_fullSOChartGSpinOrigin
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.cliffordSpinCandidateRealFiniteRawMeasure D
        (L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateRealFiniteOrbitAt
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x) ⁻¹'
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
            (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) =
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateChartGluedMeasure
          (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
          D.spinFiniteScale
          (L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x) := by
  let V := L.rationalQuadraticSpaceMatrix
  letI : SigmaFinite V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isSigmaFinite
  letI : SFinite V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
    infer_instance
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        D.spinFiniteScale) := by
    unfold
      RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    infer_instance
  rw [L.preimage_cliffordSpinCandidateRealFiniteOrbitAt_fullSOChartGSpinOrigin S x]
  unfold cliffordSpinCandidateRealFiniteRawMeasure
  exact Measure.prod_prod
    (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x)
    (L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x)

/-- The descended orbital-kernel mass at the retained origin is the same
product of explicit real and finite raw Spin masses. -/
theorem positiveSpinOrbitalKernel_fullSOChartGSpinOrigin_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      V.realCliffordSpinCandidateChartGluedMeasure
          (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x) *
        V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
          D.spinFiniteScale
          (L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x) := by
  dsimp only
  rw [L.positiveSpinOrbitalKernel_projection_apply_identityChart_eq_realFinite]
  exact L.cliffordSpinCandidateRealFiniteRawMeasure_spinOrbit_fullSOChartGSpinOrigin D S x

end PositiveDefiniteIntegralLattice

end
