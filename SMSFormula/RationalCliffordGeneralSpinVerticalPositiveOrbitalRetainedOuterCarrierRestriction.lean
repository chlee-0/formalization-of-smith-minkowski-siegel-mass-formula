import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseOrigin
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalCarrierRestriction

/-!
# Restrict the retained Spin orbital integral to its positive-idèle base carrier

Every point of the certified full-adelic identity carrier has similitude in
the retained positive-idèle base carrier.  This is proved on the real--finite
source: the real and exceptional central-fiber identity charts give the
square targets, while the horizontal integral tail gives the normalized
integral idèle tail.

Consequently a descended Spin orbital measure assigns the identity carrier
zero mass when its positive similitude parameter lies outside the retained
base carrier.
-/

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance retainedOuterCarrierPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

/-- Membership in the real central-fiber identity chart forces the
similitude into the existing real square target. -/
theorem realCliffordGeneralSpinSimilitude_mem_unitSquareTarget_of_mem_identityChart
    (g : V.RealCliffordGeneralSpinGroup)
    (hg : g ∈ V.realCliffordGeneralSpinCentralFiberIdentityChart.source) :
    V.realCliffordGeneralSpinSimilitudeHom g ∈
      (Rat.unitSquareIdentityChart ℝ).target := by
  have h := V.realCliffordGeneralSpinCentralFiberIdentityChart.map_source hg
  exact h.1

/-- Membership in a p-adic central-fiber identity chart forces the
similitude into the corresponding p-adic square target. -/
theorem padicCliffordGeneralSpinSimilitude_mem_unitSquareTarget_of_mem_identityChart
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.PadicCliffordGeneralSpinGroup p)
    (hg : g ∈ (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source) :
    g.similitude ∈ (Rat.unitSquareIdentityChart ℚ_[p]).target := by
  have h := (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).map_source hg
  exact h.1

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance retainedOuterCarrierDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedOuterCarrierPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

/-- The positive similitude of every point in the certified identity carrier
belongs to the retained positive-idèle base carrier. -/
theorem fullAdelicCliffordGeneralSpinPositiveSimilitude_mem_retainedBaseCarrier_of_mem_identityChart
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup}
    (hg : g ∈ (L.rationalQuadraticSpaceMatrix
      |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S))) :
    L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g ∈
      RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  rcases hg with ⟨z, hz, rfl⟩
  rcases hz.2 with ⟨x, hx, hxz⟩
  let realTarget : (Rat.unitSquareIdentityChart ℝ).target :=
    ⟨V.realCliffordGeneralSpinSimilitudeHom z.1,
      V.realCliffordGeneralSpinSimilitude_mem_unitSquareTarget_of_mem_identityChart
        z.1 hz.1⟩
  let exceptionalTarget :
      (v : {v // v ∈ B}) →
        (Rat.unitSquareIdentityChart
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).target :=
    fun v =>
      ⟨(x.1 v).similitude,
        V.padicCliffordGeneralSpinSimilitude_mem_unitSquareTarget_of_mem_identityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 (x.1 v)
          (hx.1 v (Set.mem_univ v))⟩
  let tailTarget : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B :=
    fun v => ⟨(x.2 v).1.similitude, (x.2 v).2.2.2.1⟩
  let target :
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialRetainedBaseTargetSource B :=
    (realTarget, (exceptionalTarget, tailTarget))
  have hsim :
      V.fullAdelicCliffordGeneralSpinSimilitudeHom
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm z) =
        RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToAmbient
          B target := by
    apply RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.injective
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_similitude]
    unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseTargetToAmbient
    simp only [Function.comp_apply]
    rw [RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply]
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · apply Units.ext
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
      change
        ((RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
          (V.finiteAdelicCliffordGeneralSpinSimilitudeHom z.2) :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
          ((RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
            (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareTargetToAmbient
              B (exceptionalTarget, tailTarget)) :
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
      rw [rationalFiniteIdeleDifferentialSquareTargetToAmbient_component
        B (exceptionalTarget, tailTarget) v]
      have hfinite := congrArg V.finiteAdelicCliffordGeneralSpinSimilitudeHom hxz
      rw [← hfinite]
      change
        (((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient E x)).similitude :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) = _
      rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient E x v]
      by_cases hv : v ∈ B
      · rw [dif_pos hv, dif_pos hv]
      · rw [dif_neg hv, dif_neg hv]
  change
    V.fullAdelicCliffordGeneralSpinSimilitudeHom
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm z) ∈
        RationalQuadraticSpaceMatrix.rationalIdeleDifferentialRetainedBaseCarrier B
  rw [hsim]
  exact Set.mem_range_self target

/-- Outside the retained positive-idèle base carrier, the descended Spin
orbital measure gives the certified identity carrier zero mass. -/
theorem positiveSpinOrbitalKernel_identityChart_eq_zero_of_not_mem_retainedBaseCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup)
    (ha : a ∉
      RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.positiveSpinOrbitalKernel hr D a
        (L.rationalQuadraticSpaceMatrix
          |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
            (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) = 0 := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let g := L.positiveIdeleGeneralSpinLift hr a
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hg : L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g = a :=
    L.positiveIdeleGeneralSpinLift_similitude hr a
  have hpreimage : orbit ⁻¹' C = ∅ := by
    ext y
    constructor
    · intro hy
      exfalso
      have horbitSim :
          L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr (orbit y) = a := by
        apply Subtype.ext
        change V.fullAdelicCliffordGeneralSpinSimilitudeHom
            (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) =
              (a : RationalAdeleˣ)
        rw [map_mul]
        unfold RationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom
        change
          ((V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele y).similitude) *
              V.fullAdelicCliffordGeneralSpinSimilitudeHom g = (a : RationalAdeleˣ)
        rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude, one_mul]
        exact congrArg Subtype.val hg
      have hbase :=
        L.fullAdelicCliffordGeneralSpinPositiveSimilitude_mem_retainedBaseCarrier_of_mem_identityChart
          hr S hy
      rw [horbitSim] at hbase
      exact ha hbase
    · simp
  rw [L.positiveSpinOrbitalKernel_apply_of_similitude_eq hr D a g hg C
    (V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E)]
  rw [show orbit ⁻¹' C = ∅ from hpreimage]
  simp

/-- The descended orbital kernel restricted to the certified identity carrier. -/
noncomputable def positiveSpinOrbitalKernelRestrictIdentityChart
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.Kernel
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  (L.positiveSpinOrbitalKernel hr D).restrict
    (L.rationalQuadraticSpaceMatrix
      |>.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S))

@[simp]
theorem positiveSpinOrbitalKernelRestrictIdentityChart_apply
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) :
    L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S a =
      (L.positiveSpinOrbitalKernel hr D a).restrict
        (L.rationalQuadraticSpaceMatrix
          |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
            (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) := by
  exact ProbabilityTheory.Kernel.restrict_apply _ _ _

/-- Pointwise outside the retained positive-idèle base, the identity-carrier
restricted orbital kernel is the zero measure. -/
theorem positiveSpinOrbitalKernelRestrictIdentityChart_apply_eq_zero_of_not_mem_retainedBaseCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup)
    (ha : a ∉
      RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S a = 0 := by
  rw [L.positiveSpinOrbitalKernelRestrictIdentityChart_apply,
    Measure.restrict_eq_zero]
  exact
    L.positiveSpinOrbitalKernel_identityChart_eq_zero_of_not_mem_retainedBaseCarrier
      hr D S a ha

/-- Binding the identity-carrier-restricted orbital kernel over the complement
of the retained positive-idèle base gives the zero measure. -/
theorem positiveSpinOrbitalKernelRestrictIdentityChart_comp_restrict_compl_retainedBaseCarrier_eq_zero
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S ∘ₘ
        (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
          (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier
            B)ᶜ) = 0 := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let C := RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B
  let κ := L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S
  let μ := RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure
  have hC : MeasurableSet C :=
    RationalQuadraticSpaceMatrix.measurableSet_positiveRationalIdeleDifferentialRetainedBaseCarrier B
  change κ ∘ₘ μ.restrict Cᶜ = 0
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA κ.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [MeasureTheory.ae_restrict_mem hC.compl] with a ha
  have hzero :=
    L.positiveSpinOrbitalKernelRestrictIdentityChart_apply_eq_zero_of_not_mem_retainedBaseCarrier
      hr D S a ha
  rw [hzero]
  simp

/-- The full positive-idèle orbital bind restricted to the identity carrier
is exactly the restricted orbital kernel bound over the retained base.  This
is the outer carrier restriction needed for the retained-cylinder
substitution. -/
theorem positiveSpinOrbitalKernel_comp_positiveHaar_restrict_identityChart_eq_comp_restrict_retainedBaseCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    ((L.positiveSpinOrbitalKernel hr D ∘ₘ
        RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure).restrict
      (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E)) =
      L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S ∘ₘ
        (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure.restrict
          (RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier
            B)) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  let A := RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B
  let κ := L.positiveSpinOrbitalKernel hr D
  let η := L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S
  let μ := RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure
  have hC : MeasurableSet C :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hA : MeasurableSet A :=
    RationalQuadraticSpaceMatrix.measurableSet_positiveRationalIdeleDifferentialRetainedBaseCarrier B
  have hrestrict : (κ ∘ₘ μ).restrict C = η ∘ₘ μ := by
    apply Measure.ext
    intro T hT
    rw [Measure.restrict_apply hT,
      Measure.bind_apply (hT.inter hC) κ.aemeasurable,
      Measure.bind_apply hT η.aemeasurable]
    apply lintegral_congr
    intro a
    rw [L.positiveSpinOrbitalKernelRestrictIdentityChart_apply,
      Measure.restrict_apply hT]
  have hcompl : η ∘ₘ μ.restrict Aᶜ = 0 :=
    L.positiveSpinOrbitalKernelRestrictIdentityChart_comp_restrict_compl_retainedBaseCarrier_eq_zero
      hr D S
  change (κ ∘ₘ μ).restrict C = η ∘ₘ μ.restrict A
  rw [hrestrict]
  calc
    η ∘ₘ μ = η ∘ₘ (μ.restrict A + μ.restrict Aᶜ) := by
      rw [Measure.restrict_add_restrict_compl hA]
    _ = η ∘ₘ μ.restrict A + η ∘ₘ μ.restrict Aᶜ := by
      rw [Measure.comp_add]
    _ = η ∘ₘ μ.restrict A := by rw [hcompl, add_zero]

end PositiveDefiniteIntegralLattice

end
