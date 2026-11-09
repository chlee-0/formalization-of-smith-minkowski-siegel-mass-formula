import SMSFormula.RationalCliffordGeneralSpinHorizontalExceptionalChartToBlock
import SMSFormula.RationalCliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition

/-!
# Transition coherence for horizontal exceptional identity charts

The fixed-set chart-to-block theorem identifies each finite parameter product
with the restriction of the established exceptional Haar product to the
coordinatewise identity-chart carrier.  This file proves that those carriers
and restricted measures split exactly under enlargement of the exceptional
set.

The established transition homeomorphism separates the old exceptional
coordinates from the newly exceptional coordinates.  It sends the larger
identity-chart carrier to the product of the corresponding old and new
identity-chart carriers, and it sends the restricted Haar measure to their
literal product.  There is no transition scalar.  Interaction with the
normalized integral tail is deliberately left to the next step.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

local instance horizontalExceptionalChartTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalExceptionalChartTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance
    horizontalExceptionalChartTransitionPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalExceptionalChartTransitionPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance
    horizontalExceptionalChartTransitionPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalExceptionalChartTransitionPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalExceptionalChartTransitionPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance
    horizontalExceptionalChartTransitionPadicGSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance horizontalExceptionalChartTransitionPadicGSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

local instance horizontalExceptionalChartTransitionIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalExceptionalChartTransitionIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalExceptionalChartTransitionExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalExceptionalChartTransitionExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalExceptionalChartTransitionTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalExceptionalChartTransitionTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalExceptionalChartTransitionNewExceptionalSecondCountable
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalExceptionalChartTransitionNewExceptionalBorelSpace
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  Pi.borelSpace

/-! ## New-coordinate identity-chart factor -/

/-- Identity-chart carrier on the coordinates newly made exceptional when
passing from `S` to `T`. -/
def cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  Set.pi Set.univ fun
      v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

theorem measurableSet_cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) := by
  apply MeasurableSet.pi Set.countable_univ
  intro v _
  exact
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_source.measurableSet

theorem measurableSet_cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier S T) := by
  apply MeasurableSet.pi Set.countable_univ
  intro v _
  exact
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_source.measurableSet

/-- Coordinatewise restricted Haar measure on the newly exceptional identity
charts. -/
def cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  Measure.pi fun
      v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
    (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1).restrict
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

/-- Restriction of the established new-coordinate Haar product is precisely
the coordinatewise restricted product. -/
theorem restrict_cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_identityChart
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).restrict
        (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier S T) =
      V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure S T := by
  unfold cliffordGeneralSpinHorizontalNewExceptionalProductMeasure
    cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier
    cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure
  rw [Measure.restrict_pi_pi]

/-! ## Exact exceptional transition coherence -/

/-- Splitting the larger exceptional product pulls the product of the old and
new identity-chart carriers back to the larger identity-chart carrier. -/
theorem preimage_cliffordGeneralSpinHorizontalExceptionalTransition_identityChartCarrier
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST ⁻¹'
        ((V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ
          (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier S T)) =
      V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier T := by
  ext g
  simp only [Set.mem_preimage, Set.mem_prod,
    cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier,
    cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier,
    Set.mem_pi, Set.mem_univ, true_implies,
    cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph]
  constructor
  · rintro ⟨hOld, hNew⟩ v
    by_cases hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S
    · exact hOld ⟨v.1, hv⟩
    · exact hNew ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩
  · intro h
    constructor
    · intro v
      exact h ⟨v.1,
        V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST v.2⟩
    · intro v
      exact h ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩

/-- The transition homeomorphism sends the larger identity-chart carrier
onto the product of the old and newly exceptional carriers. -/
theorem image_cliffordGeneralSpinHorizontalExceptionalTransition_identityChartCarrier
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST ''
        V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier T =
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ
        (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier S T) := by
  rw [← V.preimage_cliffordGeneralSpinHorizontalExceptionalTransition_identityChartCarrier
    S T hST]
  exact Set.image_preimage_eq _
    (V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST).surjective

/-- The fixed-set chart restrictions are exactly coherent under the
established exceptional-coordinate transition, with no transition scalar. -/
theorem map_cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST)
        (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure T) =
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S).prod
        (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure S T) := by
  let e :=
    V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST
  let carrier :=
    (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ
      (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier S T)
  have hcarrier : MeasurableSet carrier :=
    (V.measurableSet_cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S).prod
      (V.measurableSet_cliffordGeneralSpinHorizontalNewExceptionalIdentityChartCarrier S T)
  rw [← V.restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart T]
  rw [← V.preimage_cliffordGeneralSpinHorizontalExceptionalTransition_identityChartCarrier
    S T hST]
  rw [← Measure.restrict_map e.measurable hcarrier]
  rw [V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_map_transition S T hST]
  rw [← Measure.prod_restrict]
  rw [V.restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart S]
  rw [V.restrict_cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_identityChart S T]

/-! ## Attachment of the normalized common tail -/

/-- At a fixed exceptional set, retain the identity chart on the exceptional
coordinates and the complete normalized integral tail. -/
def cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S).prod
    (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)

/-- The preceding measure is literally the established exceptional/tail
source restricted only in its exceptional coordinates. -/
theorem restrict_cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S).restrict
        ((V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ
          Set.univ) =
      V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
    cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [V.restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart S]

/-- After splitting the larger exceptional/tail source, its identity-chart
restriction is the old identity-chart factor, the newly exceptional
identity-chart factor, and the unchanged normalized common tail. -/
theorem
    map_cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure_largerTransition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph S T hST)
        (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure T) =
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S).prod
        ((V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure S T).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure T) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure T) := by
    rw [← V.restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart T]
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S) := by
    rw [← V.restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart S]
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure S T) := by
    rw [← V.restrict_cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_identityChart
      S T]
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  have hidTail :
      Measure.map (fun g ↦ g)
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) =
        V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T :=
    Measure.map_id
  have hAssoc :
      Measure.map (Homeomorph.prodAssoc
          (V.CliffordGeneralSpinHorizontalExceptionalProduct S)
          (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T)
          (V.CliffordGeneralSpinHorizontalIntegralTail T))
        (((V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S).prod
          (V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure S T)).prod
            (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) =
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S).prod
        ((V.cliffordGeneralSpinHorizontalNewExceptionalIdentityChartRestrictedMeasure S T).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) := by
    exact Measure.prodAssoc_prod
  unfold cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph
    cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure
  change Measure.map
    ((Homeomorph.prodAssoc _ _ _) ∘
      Prod.map
        (V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST)
        (fun g ↦ g)) _ = _
  rw [← Measure.map_map, ← Measure.map_prod_map,
    V.map_cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure_transition
      S T hST,
    hidTail, hAssoc]
  all_goals fun_prop

end RationalQuadraticSpaceMatrix
