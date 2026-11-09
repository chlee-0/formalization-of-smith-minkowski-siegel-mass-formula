import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFixedSquarePreimage

/-!
# Substitute the retained source into the orbital kernel on the retained base

Each point in the retained positive-idèle base disintegration is the positive
similitude of the horizontal origin multiplied by its displayed full
differential square scalar.  The representative-free restricted orbital
kernel may therefore be computed at that scaled origin.  Fixed-square
preimage invariance then identifies its raw orbit pushforward with the
retained-cylinder source pushforward.

This is a pointwise measure identity.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedBaseKernelSubstitutionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseKernelSubstitutionRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedBaseKernelSubstitutionRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedBaseKernelSubstitutionFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedBaseKernelSubstitutionFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedBaseKernelSubstitutionRealGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  borel _

local instance retainedBaseKernelSubstitutionRealGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedBaseKernelSubstitutionFiniteGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedBaseKernelSubstitutionFiniteGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedBaseKernelSubstitutionFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedBaseKernelSubstitutionFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- At every literal point of the retained base disintegration, the
identity-carrier-restricted descended orbital kernel is exactly the retained
raw source pushed through the literal fixed-square cylinder orbit. -/
theorem positiveSpinOrbitalKernelRestrictIdentityChart_retainedBasePoint
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      (Rat.unitSquareIdentityChart ℝ).source ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B)
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B)
    (a : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q
    let root : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B :=
      (z.1, z.2, a)
    let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
      (L.retainedSpinBlockSourceToOrbitPreimage S x)
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
    let base :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToPositive B
        ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget
            B z.2,
            fun v => (a v) ^ 2 *
              V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g v)))
    L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S base =
      Measure.map
        (fun u => L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x (root, u))
        source := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q
  let root : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B :=
    (z.1, z.2, a)
  let scalar := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
    B root
  let origin := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
  let scaled :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele scalar * origin
  let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
    (L.retainedSpinBlockSourceToOrbitPreimage S x)
  let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
  let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
  let base :=
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToPositive B
      ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget
          B z.2,
          fun v => (a v) ^ 2 *
            V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g v)))
  have hsim : L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr scaled = base := by
    apply Subtype.ext
    change V.fullAdelicCliffordGeneralSpinSimilitudeHom scaled = (base : RationalAdeleˣ)
    unfold scaled
    rw [map_mul]
    change scalar ^ 2 * V.fullAdelicCliffordGeneralSpinSimilitudeHom origin = _
    exact (L.rationalIdeleDifferential_retainedBasePoint_eq_square_mul_originSimilitude
      S z q a).symm
  let carrier := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hcarrier : MeasurableSet carrier :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  rw [L.positiveSpinOrbitalKernelRestrictIdentityChart_apply]
  rw [L.positiveSpinOrbitalKernel_restrict_of_similitude_eq
    hr D base scaled hsim carrier hcarrier]
  exact L.map_spinOrbit_spinData_restrict_fixedSquare_fullSOChartOrigin_preimage
    D S x root

/-- Nonnegative-integral form of the retained-base pointwise substitution. -/
theorem lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBasePoint
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      (Rat.unitSquareIdentityChart ℝ).source ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B)
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B)
    (a : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q
    let root : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B :=
      (z.1, z.2, a)
    let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
      (L.retainedSpinBlockSourceToOrbitPreimage S x)
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
    let base :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToPositive B
        ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget
            B z.2,
            fun v => (a v) ^ 2 *
              V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g v)))
    (∫⁻ w, f w ∂L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S base) =
      ∫⁻ u, f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x (root, u))
        ∂source := by
  dsimp only
  rw [L.positiveSpinOrbitalKernelRestrictIdentityChart_retainedBasePoint hr D S z q a]
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q
  let root : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B :=
    (z.1, z.2, a)
  let literal := fun u =>
    L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x (root, u)
  have hliteral : Measurable literal := by
    unfold literal cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit
    let c := RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B root)
    have hleft : Measurable (fun w : V.FullAdelicCliffordGeneralSpinGroup => c * w) :=
      (continuous_const.mul continuous_id).measurable
    simpa only [Prod.fst, Prod.snd] using
      hleft.comp
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.continuous.measurable.comp
          (L.measurable_retainedRealFiniteSpinSourceOrbit S x))
  exact lintegral_map hf hliteral

/-- Disintegrating the retained positive-idèle base and then integrating the
restricted orbital kernel gives the fixed-square retained-cylinder
source in the exact `real/exceptional, SO-tail, scalar-tail, Spin-source`
order.  All changes of variables here have coefficient one. -/
theorem lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBase_disintegration
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μRE :=
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B)
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let μScalar :=
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
    let x := L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S
    let j := fun q => Prod.map (L.retainedRealSpinSourceToOrbitPreimage S (x q))
      (L.retainedSpinBlockSourceToOrbitPreimage S (x q))
    let C := fun q => L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S (x q) ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S (x q)
    let source := fun q =>
      ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict (C q)).comap (j q)
    (∫⁻ b, ∫⁻ w, f w
        ∂L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S b
      ∂(RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
        (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B))) =
      ∫⁻ z, ∫⁻ q, ∫⁻ a, ∫⁻ u,
        f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S (x q)
          ((z.1, z.2, a), u))
        ∂source q ∂μScalar ∂μSO ∂μRE := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let κ := L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S
  let carrier := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hcarrier : MeasurableSet carrier :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hk : Measurable (fun b => ∫⁻ w, f w ∂κ b) := by
    have hraw := L.measurable_lintegral_positiveSpinOrbitalKernel hr D
      (hf.indicator hcarrier)
    have heq : (fun b => ∫⁻ w, f w ∂κ b) =
        fun b => ∫⁻ w, carrier.indicator f w ∂L.positiveSpinOrbitalKernel hr D b := by
      funext b
      rw [L.positiveSpinOrbitalKernelRestrictIdentityChart_apply]
      exact (lintegral_indicator hcarrier f).symm
    rw [heq]
    exact hraw
  rw [← L.lintegral_positiveRationalIdele_retainedBase_disintegration S
    (fun b => ∫⁻ w, f w ∂κ b) hk]
  apply lintegral_congr
  intro z
  apply lintegral_congr
  intro q
  apply lintegral_congr
  intro a
  exact L.lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBasePoint
    hr D S z q a f hf

end PositiveDefiniteIntegralLattice

end
