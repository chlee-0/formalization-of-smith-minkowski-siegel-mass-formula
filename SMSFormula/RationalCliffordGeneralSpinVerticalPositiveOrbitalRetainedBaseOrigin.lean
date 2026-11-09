import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseCarrier
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedRawCylinderSubstitution

/-!
# Canonical retained origin over the positive-idèle base

The retained base disintegration leaves only the normalized integral `SO`
tail as an origin coordinate.  This file inserts that coordinate into the
full `SO` chart, using the identity points of the real and exceptional Spin
charts.  It then identifies the similitude of the resulting canonical `GSpin`
origin componentwise.

No section of the good-tail similitude map is chosen: the only tail lift is
the central-fiber lift used throughout the horizontal cylinder construction.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedBaseOriginDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedBaseOriginPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The existing full `SO` chart point whose real and exceptional Spin
coordinates are the identity and whose good coordinate is the displayed
normalized `SO` tail point. -/
def cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.CliffordGeneralSpinHorizontalFullSOChartSource B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact (⟨1, V.one_mem_realCliffordSpinCandidateIdentityChart_source⟩,
    (fun v ↦ ⟨1, V.one_mem_padicCliffordSpinCandidateIdentityChart_source
      (Rat.HeightOneSpectrum.primesEquiv v.1).1⟩), q)

@[simp]
theorem cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin_fst
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
    ((L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q).1 :
      L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup) = 1 := by
  rfl

@[simp]
theorem cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin_exceptional
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B)
    (v : {v // v ∈
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    ((L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q).2.1 v :
      L.rationalQuadraticSpaceMatrix.PadicCliffordSpinCandidateGroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) = 1 := by
  rfl

@[simp]
theorem cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin_tail
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B) :
    (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q).2.2 = q := by
  rfl

/-- Height-one evaluation of the finite idèle square-source assembly is the
displayed exceptional coordinate on the retained set and the displayed
integral-tail coordinate elsewhere. -/
theorem rationalFiniteIdeleDifferentialSquareChartToAmbient_component
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalQuadraticSpaceMatrix.RationalFiniteIdeleDifferentialSquareChartSource S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
        (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient S z) =
      if hv : v ∈ S then z.1 ⟨v, hv⟩ else z.2 ⟨v, hv⟩ := by
  classical
  unfold RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToProduct
  change
    RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock
          S (Prod.map (fun x v ↦ ↑(x v)) id z)).1 = _
  rw [RationalQuadraticSpaceMatrix.exceptionalTailToGenuinePrincipalBlock_component]
  by_cases hv : v ∈ S <;>
    simp [RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailLocalUnit, hv]

/-- The target version of the same component formula. -/
theorem rationalFiniteIdeleDifferentialSquareTargetToAmbient_component
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalQuadraticSpaceMatrix.RationalFiniteIdeleDifferentialSquareTargetSource S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
        (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareTargetToAmbient S z) =
      if hv : v ∈ S then z.1 ⟨v, hv⟩ else z.2 ⟨v, hv⟩ := by
  classical
  unfold RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareTargetToAmbient
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareTargetToProduct
  change
    RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock
          S (Prod.map (fun x v ↦ ↑(x v)) id z)).1 = _
  rw [RationalQuadraticSpaceMatrix.exceptionalTailToGenuinePrincipalBlock_component]
  by_cases hv : v ∈ S <;>
    simp [RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailLocalUnit, hv]

/-- Similitude of the finite part of the canonical origin: exceptional Spin
identity coordinates contribute one, while the good part is the literal
similitude of the already fixed central-fiber lift. -/
theorem finiteAdelicCliffordGeneralSpinSimilitude_fullSOChartBaseOrigin_component
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (q : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicSpecialOrthogonalIntegralTail B)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
    RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S
            (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q))).2.similitude =
      if hv : v ∈ E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then 1 else
        V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E ⟨v, hv⟩ (g ⟨v, hv⟩) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
  rw [L.fullSOChartGSpinOrigin_realFinite S
    (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)]
  rw [← V.finiteAdelicCliffordGeneralSpinHeightOneComponent_similitude]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
  rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
  by_cases hv : v ∈
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  · rw [dif_pos hv, dif_pos hv]
    exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (1 : V.PadicCliffordSpinCandidateGroup
        (Rat.HeightOneSpectrum.primesEquiv v).1)
  · rw [dif_neg hv, dif_neg hv]
    rfl

/-- The idèle displayed by the retained-base disintegration is the
square of the full differential root times the similitude of the canonical
retained origin. -/
theorem rationalIdeleDifferential_retainedBasePoint_eq_square_mul_originSimilitude
    (L : PositiveDefiniteIntegralLattice (r + 2))
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
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToAmbient B
        ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget
            B z.2,
            fun v => (a v) ^ 2 *
              V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g v))) =
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
          B (z.1, z.2, a)) ^ 2 *
        V.fullAdelicCliffordGeneralSpinSimilitudeHom
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S
            (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
    B (z.1, z.2, a)
  let origin := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S
    (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)
  apply RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.injective
  rw [map_mul, map_pow]
  unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToAmbient
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
  simp only [Function.comp_apply]
  rw [RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply,
    RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply]
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_similitude]
  rw [L.fullSOChartGSpinOrigin_realFinite S
    (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)]
  apply Prod.ext
  · change
      (((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1 : ℝˣ)) =
        (z.1 : ℝˣ) ^ 2 *
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ
            (1 : V.RealCliffordSpinCandidateGroup)).similitude
    rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude, mul_one]
    change Rat.unitSquareIdentityChart ℝ (z.1 : ℝˣ) = (z.1 : ℝˣ) ^ 2
    exact Rat.unitSquareIdentityChart_apply ℝ (z.1 : ℝˣ)
  · let rootFinite :=
      RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient B
        (z.2, a)
    simp only [Prod.map_apply, Prod.snd_mul]
    rw [show ((((z.1 : ℝˣ), rootFinite) : ℝˣ × RationalFiniteAdeleˣ) ^ 2).2 =
      rootFinite ^ 2 by rfl]
    apply Units.ext
    ext v
    apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
    have hcomponent (u : RationalFiniteAdeleˣ) :
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv
            ((u : RationalFiniteAdele) v) =
          ((RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v u :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
      rfl
    rw [hcomponent, hcomponent]
    have horigin :=
      L.finiteAdelicCliffordGeneralSpinSimilitude_fullSOChartBaseOrigin_component S q v
    rw [map_mul, map_pow]
    rw [show rootFinite =
      RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient B
        (z.2, a) by rfl]
    rw [rationalFiniteIdeleDifferentialSquareChartToAmbient_component B (z.2, a) v]
    rw [rationalFiniteIdeleDifferentialSquareTargetToAmbient_component B
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget B z.2,
        fun v => (a v) ^ 2 *
          V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v
            (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
              (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
                (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
              (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
                (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q v)) v]
    dsimp only at horigin
    rw [L.fullSOChartGSpinOrigin_realFinite S
      (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)] at horigin
    change
      RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
          (V.finiteAdelicCliffordGeneralSpinSimilitudeHom
            (V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E
              (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q).2.1
              (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
                (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
                  (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
                (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
                  (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
                (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q).2.2))) =
        if hv : v ∈ B then 1 else
          V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E ⟨v, hv⟩
            (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
              (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
                (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
              (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
                (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
              q ⟨v, hv⟩) at horigin
    rw [horigin]
    by_cases hv : v ∈ B
    · rw [dif_pos hv, dif_pos hv, dif_pos hv, mul_one]
      unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget
      simpa only using congrArg
        (fun u : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ =>
          (u : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
        (Rat.unitSquareIdentityChart_apply
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (z.2 ⟨v, hv⟩ : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ))
    · rw [dif_neg hv, dif_neg hv, dif_neg hv]
      rfl

/-- The positive similitude of every literal retained Spin cylinder over the
canonical `SO`-tail origin is the corresponding point in the retained base
disintegration.  The Spin-source coordinate is invisible because its
similitude is one. -/
theorem fullAdelicCliffordGeneralSpinPositiveSimilitude_retainedCylinderLiteralOrbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
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
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) q
    L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
        (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S
          (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)
          ((z.1, z.2, a), u)) =
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToPositive B
        ((Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget z.1,
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartToTarget
            B z.2,
            fun v => (a v) ^ 2 *
              V.padicCliffordGeneralSpinHorizontalIntegralSimilitude E v (g v))) := by
  dsimp only
  apply Subtype.ext
  change
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
        (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S
          (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q)
          ((z.1, z.2, a), u)) =
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToAmbient
        _ _
  rw [L.fullAdelicCliffordGeneralSpinSimilitude_retainedCylinderLiteralOrbit S
    (L.cliffordGeneralSpinVerticalRetainedBaseSOChartOrigin S q) ((z.1, z.2, a), u)]
  exact (L.rationalIdeleDifferential_retainedBasePoint_eq_square_mul_originSimilitude
    S z q a).symm

end PositiveDefiniteIntegralLattice

end
