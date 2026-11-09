import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedOrbitCancellation
import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberCylinderReassociation

/-!
# Reassociation map for the retained vertical cylinder

The normalized vertical-cylinder measure is supported on the retained
exceptional Spin identity carrier, but its ambient source type is the full
admissible exceptional product.  Before forming the scalar--Spin split map we
therefore totalize the identity-chart coordinate: on the carrier it
is the source point, and off the carrier it is the identity point of
the same chart.

Using that totalization, this file defines the complete square--Spin split
map.  Its good finite component is the differential scalar, followed by the
normalized integral Spin-tail action, followed by the fixed good
`GSpin` lift.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance retainedCylinderMapDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedCylinderMapPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedCylinderMapExceptionalSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedCylinderMapExceptionalBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance retainedCylinderMapIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedCylinderMapIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedCylinderMapTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedCylinderMapTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

/-- The underlying value of the totalized existing p-adic Spin identity
chart. -/
def retainedExceptionalSpinIdentityChartValue
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B →
      (v : {v // v ∈ B}) → V.HeightOnePadicCliffordSpinCandidateGroup v.1 := by
  classical
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact fun u v =>
    let va : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} :=
      ⟨v.1, by
        rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        exact v.2⟩
    if h : u va ∈
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source then
      u va
    else
      1

/-- Totalized version of the p-adic Spin identity charts.  The fallback
is the identity point of that same chart and is irrelevant on the retained
source measure. -/
def retainedExceptionalSpinIdentityChartTotal
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B →
      V.CliffordGeneralSpinHorizontalExceptionalSOChartSource B := by
  classical
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact fun u v => ⟨L.retainedExceptionalSpinIdentityChartValue S u v, by
    dsimp only [retainedExceptionalSpinIdentityChartValue]
    split
    · assumption
    · exact V.one_mem_padicCliffordSpinCandidateIdentityChart_source
        (Rat.HeightOneSpectrum.primesEquiv v.1).1⟩

theorem measurable_retainedExceptionalSpinIdentityChartValue
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.retainedExceptionalSpinIdentityChartValue S) := by
  classical
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  unfold retainedExceptionalSpinIdentityChartValue
  apply measurable_pi_lambda
  intro v
  let va : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} :=
    ⟨v.1, by
      rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
      exact v.2⟩
  have hEval : Measurable
      (fun u : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B => u va) :=
    measurable_pi_apply va
  have hmem : MeasurableSet
      {u : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B |
        u va ∈ (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source} :=
    (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_source.measurableSet.preimage hEval
  simpa only [Set.piecewise] using hEval.piecewise hmem
    (measurable_const : Measurable
      (fun _ : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B =>
        (1 : V.HeightOnePadicCliffordSpinCandidateGroup v.1)))

theorem measurable_retainedExceptionalSpinIdentityChartTotal
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.retainedExceptionalSpinIdentityChartTotal S) := by
  classical
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  unfold retainedExceptionalSpinIdentityChartTotal
  apply measurable_pi_lambda
  intro v
  apply Measurable.subtype_mk
  exact (measurable_pi_apply v).comp
    (L.measurable_retainedExceptionalSpinIdentityChartValue S)

/-- On the retained exceptional carrier, totalization recovers the literal
Spin source coordinate. -/
theorem retainedExceptionalSpinIdentityChartTotal_apply_of_mem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B)
    (hu : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      u ∈ V.retainedSpinExceptionalIdentityCarrier B)
    (v : {v // v ∈
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    (L.retainedExceptionalSpinIdentityChartTotal S u v).1 =
      u ⟨v.1, by
        rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        exact v.2⟩ := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let va : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} :=
    ⟨v.1, by
      rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
      exact v.2⟩
  have hva : u va ∈
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source :=
    hu va (Set.mem_univ va)
  unfold retainedExceptionalSpinIdentityChartTotal
  change L.retainedExceptionalSpinIdentityChartValue S u v = u va
  unfold retainedExceptionalSpinIdentityChartValue
  dsimp only
  rw [dif_pos]
  simpa using hva

/-- An integral Spin-tail coordinate embedded in the horizontal integral
`GSpin` subgroup at the corresponding good place. -/
def retainedIntegralSpinTailAction
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSubgroup
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) v := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let va : V.CliffordSpinCandidateAdmissibleIntegralPlace B :=
    ⟨v.1, by
      rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
      exact v.2⟩
  have huIntegral : V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 (u va).1 :=
    (u va).2 va.2
  exact ⟨
    V.cliffordSpinCandidateToCliffordGeneralSpinHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (u va).1,
    (V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
      v.1 (u va).1).mpr huIntegral⟩

theorem measurable_retainedIntegralSpinTailAction
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :
    Measurable (fun u => L.retainedIntegralSpinTailAction S u v) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let va : V.CliffordSpinCandidateAdmissibleIntegralPlace B :=
    ⟨v.1, by
      rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
      exact v.2⟩
  apply Measurable.subtype_mk
  exact (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).measurable.comp
    ((V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
      B va).measurable.comp (measurable_pi_apply va))

@[simp]
theorem retainedIntegralSpinTailAction_coe
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :
    (L.retainedIntegralSpinTailAction S u v).1 =
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
        (u ⟨v.1, by
          rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
          exact v.2⟩).1 := by
  rfl

/-- The complete retained square--Spin source mapped into the
scalar/Spin split source. -/
def cliffordGeneralSpinVerticalRetainedCylinderToSplit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.CliffordGeneralSpinVerticalRetainedCylinderSource S →
      L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  exact fun z =>
    ((z.1.1, z.2.1),
      (fun v => (z.1.2.1 v,
        L.retainedExceptionalSpinIdentityChartTotal S z.2.2.1 v),
      fun v =>
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v
            (z.1.2.2 ⟨v.1, v.2⟩) *
          L.retainedIntegralSpinTailAction S z.2.2.2 v * g v))

theorem measurable_cliffordGeneralSpinVerticalRetainedCylinderToSplit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Measurable (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  unfold cliffordGeneralSpinVerticalRetainedCylinderToSplit
  exact
    (((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_pi_lambda _ fun v =>
      ((measurable_pi_apply v).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_pi_apply v).comp
        ((L.measurable_retainedExceptionalSpinIdentityChartTotal S).comp
          (measurable_fst.comp (measurable_snd.comp measurable_snd))))).prodMk
    (measurable_pi_lambda _ fun v =>
      Measurable.subtype_mk
        (((continuous_subtype_val.measurable.comp
          ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
            ((measurable_pi_apply v).comp
              (measurable_snd.comp (measurable_snd.comp measurable_fst))))).mul
          (continuous_subtype_val.measurable.comp
            ((L.measurable_retainedIntegralSpinTailAction S v).comp
              (measurable_snd.comp (measurable_snd.comp measurable_snd))))).mul_const
                (g v).1))))

theorem cliffordGeneralSpinVerticalRetainedCylinderToSplit_real
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : L.CliffordGeneralSpinVerticalRetainedCylinderSource S) :
    (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z).1 =
      (z.1.1, z.2.1) := by
  rfl

theorem cliffordGeneralSpinVerticalRetainedCylinderToSplit_exceptional_of_mem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : L.CliffordGeneralSpinVerticalRetainedCylinderSource S)
    (hz : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      z.2.2.1 ∈ V.retainedSpinExceptionalIdentityCarrier B)
    (v : {v // v ∈
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    ((L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z).2.1 v).1 = z.1.2.1 v ∧
    (((L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z).2.1 v).2).1 =
      z.2.2.1 ⟨v.1, by
        rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        exact v.2⟩ := by
  constructor
  · rfl
  · exact L.retainedExceptionalSpinIdentityChartTotal_apply_of_mem S z.2.2.1 hz v

theorem cliffordGeneralSpinVerticalRetainedCylinderToSplit_tail
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : L.CliffordGeneralSpinVerticalRetainedCylinderSource S)
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
    (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z).2.2 v =
      V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v
          (z.1.2.2 ⟨v.1, v.2⟩) *
        L.retainedIntegralSpinTailAction S z.2.2.2 v * g v := by
  rfl

end PositiveDefiniteIntegralLattice
