import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedOrbitalSourceSubstitution

/-!
# Fixed-square invariance of the retained Spin orbit preimage

The retained-base disintegration fixes a differential square root before the
raw Spin orbit is evaluated.  This file proves componentwise that multiplying
the canonical retained origin by that scalar does not change which Spin points
land in the identity carrier.

The finite good tail is the compact integral subgroup: scalar
multiplication and cancellation are performed inside that subgroup.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance retainedFixedSquarePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedFixedSquareDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

/-- Membership in the existing finite identity carrier is exactly its local
exceptional chart condition together with integrality at every good place. -/
theorem mem_cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier_iff_components
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (h : V.FiniteAdelicCliffordGeneralSpinGroup) :
    h ∈ V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S ↔
      (∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 h ∈
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).source) ∧
      (∀ v : V.CliffordGeneralSpinHorizontalIntegralPlace S,
        V.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 h)) := by
  constructor
  · rintro ⟨x, hx, hxh⟩
    constructor
    · intro v
      have hc := congrArg
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1) hxh
      rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
        at hc
      rw [dif_pos v.2] at hc
      rw [← hc]
      exact hx.1 v (Set.mem_univ v)
    · intro v
      have hc := congrArg
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1) hxh
      rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
        at hc
      rw [dif_neg v.2] at hc
      rw [← hc]
      exact (x.2 v).2
  · rintro ⟨hExceptional, hTail⟩
    let xExceptional : V.CliffordGeneralSpinHorizontalExceptionalProduct S :=
      fun v => V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 h
    let xTail : V.CliffordGeneralSpinHorizontalIntegralTail S :=
      fun v => ⟨V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 h, hTail v⟩
    let x : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S :=
      (xExceptional, xTail)
    refine ⟨x, ⟨?_, Set.mem_univ x.2⟩, ?_⟩
    · intro v _hv
      exact hExceptional v
    · apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
      funext v
      change
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
            (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S x) =
          V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v h
      rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
      by_cases hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      · rw [dif_pos hv]
      · rw [dif_neg hv]

/-- Multiplying the finite central-orbit origin by a fixed scalar
from the retained square source does not change its Spin-orbit intersection
with the finite identity carrier. -/
theorem cliffordSpinCandidate_fixedSquare_finiteOrbitOrigin_mem_identityCarrier_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (z : RationalFiniteIdeleDifferentialSquareChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (y : V.FiniteAdelicCliffordSpinCandidateGroup) :
    let a := rationalFiniteIdeleDifferentialSquareChartToAmbient
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) z
    V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y *
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalFiniteAdele a *
            V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S s g) ∈
        V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S ↔
      V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y *
          V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S s g ∈
        V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S := by
  dsimp only
  rw [V.mem_cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier_iff_components S]
  rw [V.cliffordSpinCandidate_finiteOrbitOrigin_mem_identityCarrier_iff S s g y]
  constructor
  · rintro ⟨hExceptional, hTail⟩
    constructor
    · intro v
      have h := hExceptional v
      unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin at h
      simp only [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1).map_mul,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
        at h
      rw [dif_pos v.2] at h
      have ha : finiteAdelicUnitHeightOneComponentHom v.1
          (rationalFiniteIdeleDifferentialSquareChartToAmbient
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) z) = z.1 v := by
        rw [finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [rationalIdeleDifferentialExceptionalTailLocalUnit, v.2]
      rw [ha] at h
      rw [← mul_assoc, ← V.scalarGroupHom_mul_comm, mul_assoc, ← map_mul] at h
      exact (V.scalar_mul_spin_mem_padicCentralFiberIdentityChart_iff
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 (z.1 v) (z.1 v).2
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v)).mp h
    · intro v
      have h := hTail v
      unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin at h
      simp only [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1).map_mul,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
        at h
      rw [dif_neg v.2] at h
      have ha : finiteAdelicUnitHeightOneComponentHom v.1
          (rationalFiniteIdeleDifferentialSquareChartToAmbient
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) z) =
          (z.2 ⟨v.1, v.2⟩).1 := by
        rw [finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [rationalIdeleDifferentialExceptionalTailLocalUnit, v.2]
      rw [ha] at h
      let H := V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v
      have hright :
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (z.2 ⟨v.1, v.2⟩).1 *
              (g v).1 ∈ H :=
        H.mul_mem (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
          (z.2 ⟨v.1, v.2⟩)).2 (g v).2
      have hembed := (H.mul_mem_cancel_right hright).mp h
      exact
        (V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
          v.1 (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)).mp hembed
  · rintro ⟨hExceptional, hTail⟩
    constructor
    · intro v
      unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
      simp only [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1).map_mul,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
      rw [dif_pos v.2]
      have ha : finiteAdelicUnitHeightOneComponentHom v.1
          (rationalFiniteIdeleDifferentialSquareChartToAmbient
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) z) = z.1 v := by
        rw [finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [rationalIdeleDifferentialExceptionalTailLocalUnit, v.2]
      rw [ha, ← mul_assoc, ← V.scalarGroupHom_mul_comm, mul_assoc, ← map_mul]
      exact (V.scalar_mul_spin_mem_padicCentralFiberIdentityChart_iff
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 (z.1 v) (z.1 v).2
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y * s v)).mpr
          (hExceptional v)
    · intro v
      unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
      simp only [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1).map_mul,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_cliffordSpinCandidateToCliffordGeneralSpinHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
      rw [dif_neg v.2]
      have ha : finiteAdelicUnitHeightOneComponentHom v.1
          (rationalFiniteIdeleDifferentialSquareChartToAmbient
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) z) =
          (z.2 ⟨v.1, v.2⟩).1 := by
        rw [finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [rationalIdeleDifferentialExceptionalTailLocalUnit, v.2]
      rw [ha]
      let H := V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v
      exact H.mul_mem
        ((V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
          v.1 (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y)).mpr
            (hTail v))
        (H.mul_mem (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
          (z.2 ⟨v.1, v.2⟩)).2 (g v).2)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance retainedFixedSquareIntegralPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedFixedSquareIntegralDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedFixedSquareRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedFixedSquareRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedFixedSquareFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedFixedSquareFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-- A fixed scalar from the full differential square source does not change
the real--finite Spin preimage of the identity carrier at a retained
horizontal origin. -/
theorem preimage_cliffordSpinCandidateRealFiniteOrbitAt_fixedSquare_fullSOChartOrigin
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B z
    let origin := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    V.cliffordSpinCandidateRealFiniteOrbitAt
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele root * origin) ⁻¹'
        V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier E =
      L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
        L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B z
  let origin := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  ext y
  change
    V.cliffordSpinCandidateRealFiniteOrbitAt
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele root * origin) y ∈
        V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier E ↔ _
  unfold RationalQuadraticSpaceMatrix.cliffordSpinCandidateRealFiniteOrbitAt
  rw [show V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
      (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele root * origin) =
        ((RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V ℝ z.1) *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ x.1,
          (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalFiniteAdele
              (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
                B z.2)) *
            V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g) by
      rw [map_mul, V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_scalarGroupHom]
      simp only [root,
        RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient,
        Function.comp_apply]
      rw [RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply]
      rw [L.fullSOChartGSpinOrigin_realFinite S x]
      rfl]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr
  · change
      V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ y.1 *
            (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V ℝ z.1 *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ x.1) ∈
          V.realCliffordGeneralSpinCentralFiberIdentityChart.source ↔
        y.1 ∈ L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x
    rw [← mul_assoc, ← V.scalarGroupHom_mul_comm, mul_assoc, ← map_mul]
    rw [V.scalar_mul_spin_mem_realCentralFiberIdentityChart_iff
      z.1 z.1.2 (y.1 * x.1)]
    rw [L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage_eq_preimage_mul S x]
    rfl
  · change
      V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y.2 *
            (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V RationalFiniteAdele
                (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
                  B z.2) *
              V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g) ∈
          V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier E ↔
        y.2 ∈ L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    change _ ↔
      V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y.2 *
          V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin E x.2.1 g ∈
        V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier E
    exact V.cliffordSpinCandidate_fixedSquare_finiteOrbitOrigin_mem_identityCarrier_iff
      E x.2.1 g z.2 y.2

/-- Raw adelic Spin Haar restricted to the fixed-square orbit preimage is the
same inverse real--finite pushforward as at the unscaled retained origin. -/
theorem spinData_adelicMeasure_restrict_fixedSquare_fullSOChartOrigin_preimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
    let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B z
    let g := RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele root * L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
      V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    D.spinData.adelicMeasure.restrict
        (orbit ⁻¹' V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
  let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B z
  let g := RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
    V RationalAdele root * L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
  let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
  rw [V.preimage_fullAdelicCliffordSpinCandidateOrbit_identityChart E g]
  rw [L.preimage_cliffordSpinCandidateRealFiniteOrbitAt_fixedSquare_fullSOChartOrigin S x z]
  exact L.spinData_adelicMeasure_restrict_realFinite_preimage D C

/-- Pushing the fixed-square raw restriction through its Spin orbit
is exactly the retained source pushed through the retained cylinder map. -/
theorem map_spinOrbit_spinData_restrict_fixedSquare_fullSOChartOrigin_preimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource B) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B z
    let g := RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele root * L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
      V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
    let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
      (L.retainedSpinBlockSourceToOrbitPreimage S x)
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
    Measure.map orbit
        (D.spinData.adelicMeasure.restrict
          (orbit ⁻¹' V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E)) =
      Measure.map
        (fun u => L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x (z, u))
        source := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
  let root := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B z
  let g := RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
    V RationalAdele root * L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
  let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
    (L.retainedSpinBlockSourceToOrbitPreimage S x)
  let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
  let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
  have horbit : Measurable orbit :=
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele).mul
      continuous_const |>.measurable
  have heSymm : Measurable e.symm := e.symm.continuous.measurable
  have hj : Measurable j :=
    ((L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x).prodMap
      (L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x)).measurable
  rw [L.spinData_adelicMeasure_restrict_fixedSquare_fullSOChartOrigin_preimage D S x z]
  have hsource : Measure.map j source =
      (L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C :=
    L.map_comap_cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage
      D S x
  change Measure.map orbit
      (Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C)) = _
  calc
    Measure.map orbit
        (Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C)) =
        Measure.map orbit (Measure.map e.symm (Measure.map j source)) := by rw [hsource]
    _ = Measure.map orbit (Measure.map (e.symm ∘ j) source) := by
      congr 1
      exact Measure.map_map heSymm hj
    _ = Measure.map (orbit ∘ e.symm ∘ j) source := by
      exact Measure.map_map horbit (heSymm.comp hj)
    _ = Measure.map
        (fun u => L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x (z, u))
        source := by
      congr 1
      funext u
      change orbit (e.symm (j u)) =
        L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x (z, u)
      unfold cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit
      rw [L.fullAdelicCliffordGeneralSpinRealFinite_symm_retainedSpinSourceOrbit S x u]
      unfold orbit g
      rw [← mul_assoc, ← V.scalarGroupHom_mul_comm, mul_assoc]
      rfl

end PositiveDefiniteIntegralLattice

end
