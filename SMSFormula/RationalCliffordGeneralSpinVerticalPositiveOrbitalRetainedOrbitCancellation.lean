import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedCylinderSource

/-!
# Cancellation on the retained vertical Spin orbit source

The translated real and finite Spin sources were chosen by right translating
the retained horizontal origin.  This file records the resulting pointwise
cancellation after those sources act on that origin.  At the real place and
at every retained exceptional finite place the Spin chart coordinate is
recovered.  Outside the retained finite set, the normalized Spin tail acts on
the good `GSpin` tail lift.

These are componentwise identities only.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedOrbitCancellationDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedOrbitCancellationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedOrbitCancellationRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedOrbitCancellationRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedOrbitCancellationFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedOrbitCancellationFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedOrbitCancellationRealGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  borel _

local instance retainedOrbitCancellationRealGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedOrbitCancellationFiniteGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedOrbitCancellationFiniteGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedOrbitCancellationExceptionalSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedOrbitCancellationExceptionalBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance retainedOrbitCancellationIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedOrbitCancellationIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedOrbitCancellationTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedOrbitCancellationTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

/-- The paired translated Spin source acting on the retained full `GSpin`
origin. -/
def retainedRealFiniteSpinSourceOrbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) →
      V.RealCliffordGeneralSpinGroup × V.FiniteAdelicCliffordGeneralSpinGroup := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact fun u =>
    V.cliffordSpinCandidateRealFiniteOrbitAt
      (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x)
      (L.retainedRealSpinSourceToOrbitPreimage S x u.1,
        L.retainedSpinBlockSourceToOrbitPreimage S x u.2)

theorem measurable_retainedRealFiniteSpinSourceOrbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Measurable (L.retainedRealFiniteSpinSourceOrbit S x) := by
  let V := L.rationalQuadraticSpaceMatrix
  exact
    (V.continuous_cliffordSpinCandidateRealFiniteOrbitAt
      (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x)).measurable.comp
        (((L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x).measurable.comp
          measurable_fst).prodMk
        ((L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x).measurable.comp
          measurable_snd))

/-- The retained real translation cancels the real Spin coordinate of the
horizontal origin. -/
theorem retainedRealFiniteSpinSourceOrbit_fst
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)) :
    (L.retainedRealFiniteSpinSourceOrbit S x u).1 =
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ u.1.1 := by
  let V := L.rationalQuadraticSpaceMatrix
  unfold retainedRealFiniteSpinSourceOrbit
    RationalQuadraticSpaceMatrix.cliffordSpinCandidateRealFiniteOrbitAt
  rw [L.fullSOChartGSpinOrigin_realFinite S x]
  simp [retainedRealSpinSourceToOrbitPreimage, map_mul, map_inv]

/-- At a retained exceptional finite place, the translated Spin source and
the retained horizontal origin cancel to the displayed exceptional Spin chart
coordinate. -/
theorem finiteAdelicCliffordGeneralSpinHeightOneComponent_retainedOrbit_mem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (L.retainedRealFiniteSpinSourceOrbit S x u).2 =
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (u.2.1 ⟨v, by
          rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
          exact hv⟩) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  have hB : v ∈ B := hv
  have hvA : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B := by
    rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
    exact hv
  have horigin := L.fullSOChartGSpinOrigin_realFinite S x
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele
          (L.retainedSpinBlockSourceToOrbitPreimage S x u.2) *
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x)).2) = _
  rw [horigin]
  unfold retainedSpinBlockSourceToOrbitPreimage
  rw [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul,
    V.finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom,
    map_mul, map_inv,
    L.retainedSpinBlockSourceToAmbient_component_mem B u.2 v hvA,
    L.retainedFiniteSpinTranslation_component_mem S x v hv]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
  rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
  rw [dif_pos hB, map_mul, map_inv, mul_assoc]
  let t : V.PadicCliffordGeneralSpinGroup
      (Rat.HeightOneSpectrum.primesEquiv v).1 :=
    V.cliffordSpinCandidateToCliffordGeneralSpinHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (x.2.1 ⟨v, hv⟩)
  have ht : t⁻¹ * t = 1 := inv_mul_cancel t
  change
    V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (u.2.1 ⟨v, hvA⟩) *
          (t⁻¹ * t) =
      V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (u.2.1 ⟨v, hvA⟩)
  rw [ht, mul_one]

/-- Outside the retained finite set, the translated source has trivial
translation component, so its normalized integral Spin tail acts on the
good `GSpin` tail lift. -/
theorem finiteAdelicCliffordGeneralSpinHeightOneComponent_retainedOrbit_notMem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (L.retainedRealFiniteSpinSourceOrbit S x u).2 =
      V.cliffordSpinCandidateToCliffordGeneralSpinHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (u.2.2 ⟨v, by
            rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
            exact hv⟩).1 *
        (g ⟨v, hv⟩).1 := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  have hB : v ∉ B := hv
  have hvA : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B := by
    rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
    exact hv
  have horigin := L.fullSOChartGSpinOrigin_realFinite S x
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele
          (L.retainedSpinBlockSourceToOrbitPreimage S x u.2) *
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x)).2) = _
  rw [horigin]
  unfold retainedSpinBlockSourceToOrbitPreimage
  rw [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul,
    V.finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom,
    map_mul, map_inv,
    L.retainedSpinBlockSourceToAmbient_component_notMem B u.2 v hvA,
    L.retainedFiniteSpinTranslation_component_notMem S x v hv]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
  rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
  rw [dif_neg hB]
  simp only [inv_one, mul_one]
  change
    V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (u.2.2 ⟨v, hvA⟩).1 *
          (g ⟨v, hB⟩).1 =
      V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (u.2.2 ⟨v, hvA⟩).1 *
          (g ⟨v, hB⟩).1
  rfl

end PositiveDefiniteIntegralLattice
