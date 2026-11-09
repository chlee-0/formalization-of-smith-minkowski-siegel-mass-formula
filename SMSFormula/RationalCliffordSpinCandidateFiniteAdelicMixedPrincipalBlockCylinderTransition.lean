import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockProductComap

/-!
# Measure transitions for mixed finite-adelic principal-block cylinders

For finite exceptional sets `S ⊆ T`, this module conjugates the direct
source-coordinate transition comparison through the exact exceptional and
integral-tail splittings.  The finite exceptional product and normalized
infinite tail split as the literal old/new product measures.  Consequently,
comapping the `T` mixed-block cylinder along the direct block embedding gives
the literal transition volume times the `S` mixed-block cylinder.

The infinite-tail proof is a direct product-measure argument.  A reusable
partition theorem for `Measure.infinitePi` is proved from finite-cylinder
uniqueness and then combined with explicit reindexing equivalences.  No
topology or measure is transported through the restricted-family block
equivalence, and no global finite-adelic measure is constructed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MeasureTheory.Measure

variable {ι : Type*} {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

/-- Splitting the coordinates of an infinite product of probability measures
by a decidable predicate is measure preserving. -/
theorem measurePreserving_cliffordSpinCandidateInfinitePiEquivPiSubtypeProd
    (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd X p)
      (Measure.infinitePi μ)
      ((Measure.infinitePi fun i : Subtype p => μ i).prod
        (Measure.infinitePi fun i : {i // ¬ p i} => μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd X p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [e.map_apply]
  have hpre :
      e ⁻¹' Set.pi (s : Set ι) t =
        Set.pi (s.subtype p : Set (Subtype p)) (fun i => t i) ×ˢ
          Set.pi (s.subtype (fun i => ¬ p i) : Set {i // ¬ p i})
            (fun i => t i) := by
    ext ⟨f, g⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
      Finset.mem_subtype, e]
    constructor
    · intro h
      constructor
      · intro i hi
        simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2] using h i hi
      · intro i hi
        simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2] using h i hi
    · rintro ⟨hf, hg⟩ i hi
      by_cases hpi : p i
      · simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, hpi] using
          hf ⟨i, hpi⟩ hi
      · simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, hpi] using
          hg ⟨i, hpi⟩ hi
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi, Measure.infinitePi_pi]
  · have hp :
        (∏ i ∈ s.subtype p, μ i (t i)) =
          ∏ i ∈ (s.filter p).attach, μ i.1 (t i.1) := by
        unfold Finset.subtype
        rw [Finset.prod_map]
        rfl
    have hnp :
        (∏ i ∈ s.subtype (fun i => ¬ p i), μ i (t i)) =
          ∏ i ∈ (s.filter (fun i => ¬ p i)).attach,
            μ i.1 (t i.1) := by
        unfold Finset.subtype
        rw [Finset.prod_map]
        rfl
    rw [hp, hnp,
      Finset.prod_attach (s.filter p) (fun i => μ i (t i)),
      Finset.prod_attach (s.filter (fun i => ¬ p i))
        (fun i => μ i (t i))]
    exact Finset.prod_filter_mul_prod_filter_not s p (fun i => μ i (t i))
  · intro i hi
    exact ht i
  · intro i hi
    exact ht i

end MeasureTheory.Measure

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockCylinderTransitionMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

/-! ## Exact index reindexings -/

private def exceptionalOldIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} ≃ {v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} // v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} where
  toFun v :=
    ⟨⟨v.1,
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST v.2⟩,
      v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def exceptionalNewIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} ≃
      {v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} //
        v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} where
  toFun v :=
    ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
      (Finset.mem_sdiff.mp v.2).2⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.1.2, v.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def tailNewIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} ≃ {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} where
  toFun v :=
    ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
      (Finset.mem_sdiff.mp v.2).1⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.2, v.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def tailCommonIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordSpinCandidateAdmissibleIntegralPlace T ≃
      {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S //
        v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} where
  toFun v :=
    ⟨⟨v.1, fun hv =>
      v.2 (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv)⟩,
      v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A place good for the larger normalized block is also good for the
smaller one. -/
private def tailCommonPlace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace T) :
    V.CliffordSpinCandidateAdmissibleIntegralPlace S :=
  ⟨v.1, fun hv =>
    v.2 (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv)⟩

/-- The two good local-factor wrappers at a common place are canonically
homeomorphic by the identity on the ambient p-adic Spin point. -/
private def tailCommonLocalHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
        (tailCommonPlace V S T hST v) ≃ₜ
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor T v where
  toFun g := ⟨g.1, fun _ => g.2 (tailCommonPlace V S T hST v).2⟩
  invFun g := ⟨g.1, fun _ => g.2 v.2⟩
  left_inv g := by ext; rfl
  right_inv g := by ext; rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- The common-place homeomorphism preserves the normalized local
probability measure. -/
private theorem tailCommonLocalHomeomorph_measurePreserving
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace T) :
    MeasurePreserving
      (tailCommonLocalHomeomorph V S T hST v)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S (tailCommonPlace V S T hST v))
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        T v) := by
  let e := tailCommonLocalHomeomorph V S T hST v
  let jT :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion T v
  have hjT : MeasurableEmbedding jT :=
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
      T v.1 v.2).isOpenEmbedding_subtypeVal.measurableEmbedding
  refine ⟨e.measurable, ?_⟩
  apply hjT.map_injective
  rw [Measure.map_map hjT.measurable e.measurable]
  change
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
          S (tailCommonPlace V S T hST v))
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S (tailCommonPlace V S T hST v)) =
      Measure.map jT
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          T v)
  rw [
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S (tailCommonPlace V S T hST v),
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      T v]
  rfl

/-! ## Exceptional and tail measure splittings -/

/-- The finite exceptional product at `T` splits into the old exceptional
product at `S` and the unrestricted product on the new coordinates `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_map_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionHomeomorph
          S T hST)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure T) =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T) := by
  let p : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} → Prop := fun v => v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
  let oldReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} =>
        V.HeightOnePadicCliffordSpinCandidateGroup v.1)
      (exceptionalOldIndexEquiv V S T hST).symm
  let newReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} =>
        V.HeightOnePadicCliffordSpinCandidateGroup v.1)
      (exceptionalNewIndexEquiv V S T).symm
  have hPart :=
    measurePreserving_piEquivPiSubtypeProd
      (fun v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} =>
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1)
      p
  have hOld :=
    measurePreserving_piCongrLeft
      (fun v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} =>
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1)
      (exceptionalOldIndexEquiv V S T hST).symm
  have hNew :=
    measurePreserving_piCongrLeft
      (fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} =>
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1)
      (exceptionalNewIndexEquiv V S T).symm
  have hCombined := (hOld.prod hNew).comp hPart
  have hfun :
      (Prod.map oldReindex newReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T} =>
              V.HeightOnePadicCliffordSpinCandidateGroup v.1)
            p) =
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionHomeomorph
          S T hST := by
    funext g
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl
  simpa only [
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure,
    finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure,
    hfun] using hCombined.map_eq

set_option backward.isDefEq.respectTransparency false in
/-- The normalized integral tail at `S` splits into the normalized finite
product on the new coordinates `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)` and the normalized common tail outside
`T`. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_map_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionHomeomorph
          S T hST)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S) =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
        S T).prod
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace T) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          T v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      T v
  let p : V.CliffordSpinCandidateAdmissibleIntegralPlace S → Prop := fun v => v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T
  let newReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} =>
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
          ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩)
      (tailNewIndexEquiv V S T).symm
  let commonIndexReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
          (tailCommonPlace V S T hST v))
      (tailCommonIndexEquiv V S T hST).symm
  let commonFiberReindex :=
    MeasurableEquiv.piCongrRight fun
      v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
        (tailCommonLocalHomeomorph V S T hST v).toMeasurableEquiv
  let commonReindex := commonIndexReindex.trans commonFiberReindex
  have hPart :=
    Measure.measurePreserving_cliffordSpinCandidateInfinitePiEquivPiSubtypeProd
      (fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v)
      p
  have hNew :
      MeasurePreserving newReindex
        (Measure.infinitePi fun
          v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // p v} =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              S v.1)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
          S T) := by
    refine ⟨newReindex.measurable, ?_⟩
    simpa only [
      finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure,
      Measure.infinitePi_eq_pi] using
        (Measure.infinitePi_map_piCongrLeft
          (fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩)
          (tailNewIndexEquiv V S T).symm)
  have hCommonIndex :
      MeasurePreserving commonIndexReindex
        (Measure.infinitePi fun
          v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              S v.1)
        (Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              S (tailCommonPlace V S T hST v)) := by
    refine ⟨commonIndexReindex.measurable, ?_⟩
    simpa only [commonIndexReindex] using
      (Measure.infinitePi_map_piCongrLeft
        (fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
            S (tailCommonPlace V S T hST v))
        (tailCommonIndexEquiv V S T hST).symm)
  have hCommonFiber :
      MeasurePreserving commonFiberReindex
        (Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              S (tailCommonPlace V S T hST v))
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) := by
    refine ⟨commonFiberReindex.measurable, ?_⟩
    unfold
      finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
    change
      Measure.map
          (fun g v => tailCommonLocalHomeomorph V S T hST v (g v))
          (Measure.infinitePi fun
            v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
              V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
                S (tailCommonPlace V S T hST v)) =
        Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              T v
    rw [Measure.infinitePi_map_pi
      (μ := fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace T =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S (tailCommonPlace V S T hST v))
      (f := fun v g => tailCommonLocalHomeomorph V S T hST v g)
      (fun v => (tailCommonLocalHomeomorph V S T hST v).measurable)]
    congr 1
    funext v
    exact (tailCommonLocalHomeomorph_measurePreserving V S T hST v).map_eq
  have hCommon :
      MeasurePreserving commonReindex
        (Measure.infinitePi fun
          v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
            V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
              S v.1)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    hCommonFiber.comp hCommonIndex
  letI : SFinite
      (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // p v} =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // p v} =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) :=
      inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // p v} =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // p v} =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  letI : SFinite
      (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) :=
      inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hCombined := (MeasurePreserving.prod
    (μa := Measure.infinitePi fun
      v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // p v} =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1)
    (μc := Measure.infinitePi fun
      v : {v : V.CliffordSpinCandidateAdmissibleIntegralPlace S // ¬ p v} =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure S v.1)
    hNew hCommon).comp hPart
  have hfun :
      (Prod.map newReindex commonReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
              V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
                S v)
            p) =
        V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionHomeomorph
          S T hST := by
    funext g
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl
  simpa only [
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure,
    hfun] using hCombined.map_eq

/-! ## Nested transition coordinates -/

/-- Split the `T` source coordinates and reassociate them as
`old exceptional × (new unrestricted × common tail)`. -/
def finiteAdelicCliffordSpinCandidateAdmissibleLargerTransitionSourceHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T) ≃ₜ
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)) :=
  (Homeomorph.prodCongr
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionHomeomorph
        S T hST)
      (Homeomorph.refl _)).trans
    (Homeomorph.prodAssoc _ _ _)

/-- Split the `S` source tail as
`old exceptional × (new integral × common tail)`. -/
def finiteAdelicCliffordSpinCandidateAdmissibleSmallerTransitionSourceHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) ≃ₜ
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)) :=
  Homeomorph.prodCongr
    (Homeomorph.refl _)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionHomeomorph
      S T hST)

/-- In nested transition coordinates, the conjugated mixed-block embedding is
the literal identity on old exceptional coordinates and the common tail, with
only the new integral coordinates included into the unrestricted groups. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceHomeomorph_exact
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleLargerTransitionSourceHomeomorph
        S T hST
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
          S T hST g) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceInclusion S T
        (V.finiteAdelicCliffordSpinCandidateAdmissibleSmallerTransitionSourceHomeomorph
          S T hST g) := by
  change
    let q :=
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv S T hST
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
            S T hST g).1),
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
          S T hST g).2)
    (q.1.1, q.1.2, q.2) =
      _
  rw [
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinate_exact
      S T hST g]
  rfl

/-- The `T` exceptional/tail source measure becomes the literal nested product
of the old exceptional, new unrestricted, and common-tail measures. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_map_largerTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleLargerTransitionSourceHomeomorph
          S T hST)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          T) =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure T) :=
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite V T
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure T) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability
      V T
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  have hidTail :
      Measure.map (fun g => g)
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) =
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T := by
    exact Measure.map_id
  have hAssoc :
      Measure.map
          (Homeomorph.prodAssoc
            (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S)
            (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T)
            (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T))
          (((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
              (V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure
                S T)).prod
            (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T)) =
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure
            S T).prod
            (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T)) := by
    exact Measure.prodAssoc_prod
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleLargerTransitionSourceHomeomorph
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  change
    Measure.map
        ((Homeomorph.prodAssoc
          (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S)
          (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T)
          (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)) ∘
          Prod.map
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionHomeomorph
              S T hST)
            (fun g => g))
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure T).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T)) =
      _
  rw [
    ← Measure.map_map,
    ← Measure.map_prod_map,
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_map_transition
      S T hST,
    hidTail,
    hAssoc]
  all_goals fun_prop

/-- The `S` exceptional/tail source measure becomes the literal nested product
of the old exceptional, new normalized integral, and common-tail measures. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_map_smallerTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleSmallerTransitionSourceHomeomorph
          S T hST)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S) =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
          S T).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S) :=
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite V S
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S) :=
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability
      V S
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  have hid :
      Measure.map
          (Homeomorph.refl
            (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S))
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S) =
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S := by
    exact Measure.map_id
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleSmallerTransitionSourceHomeomorph
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  rw [
    Homeomorph.coe_prodCongr,
    ← Measure.map_prod_map,
    hid,
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_map_transition
      S T hST]
  all_goals fun_prop

/-- The conjugated exceptional/tail coordinate embedding is measurably
embedded; this follows directly by conjugating the genuine mixed-block
measurable embedding by the two direct source homeomorphisms. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinate_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
        S T hST) := by
  simpa only [
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom,
    MonoidHom.coe_comp,
    Function.comp_def] using
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph T).symm
        |>.measurableEmbedding.comp
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
              S T hST).comp
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph S
              |>.measurableEmbedding)))

/-- The exact transition formula on the direct exceptional/tail source
carriers. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        T).comap
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
          S T hST) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S := by
  let larger :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleLargerTransitionSourceHomeomorph S T hST
  let smaller :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleSmallerTransitionSourceHomeomorph S T hST
  let coordinate :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
      S T hST
  let inclusion :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceInclusion S T
  have hCoordinate : MeasurableEmbedding coordinate :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinate_measurableEmbedding
      S T hST
  have hInclusion : MeasurableEmbedding inclusion := by
    let hIdOld :=
      (MeasurableEquiv.refl
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S))
        |>.measurableEmbedding
    let hIdTail :=
      (MeasurableEquiv.refl
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T))
        |>.measurableEmbedding
    have hNewTail :=
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusion_measurableEmbedding
        S T).prodMap hIdTail
    simpa only [
      inclusion,
      finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceInclusion] using
        hIdOld.prodMap hNewTail
  have hfun : larger ∘ coordinate = inclusion ∘ smaller := by
    funext g
    exact
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceHomeomorph_exact
        S T hST g
  calc
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        T).comap coordinate =
        ((Measure.map larger
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
            T)).comap larger).comap coordinate := by
          rw [larger.measurableEmbedding.comap_map]
    _ = (Measure.map larger
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
            T)).comap (larger ∘ coordinate) := by
          rw [Measure.comap_comap
            hCoordinate.measurableSet_image'
            larger.injective
            larger.measurableEmbedding.measurableSet_image']
    _ = (Measure.map larger
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
            T)).comap (inclusion ∘ smaller) := by rw [hfun]
    _ = ((Measure.map larger
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
            T)).comap inclusion).comap smaller := by
          rw [Measure.comap_comap
            smaller.measurableEmbedding.measurableSet_image'
            hInclusion.injective
            hInclusion.measurableSet_image']
    _ = (((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
            ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure
              S T).prod
              (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
                T))).comap inclusion).comap smaller := by
          rw [
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_map_largerTransition
              S T hST]
    _ = (V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
            ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
              S T).prod
              (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
                T)))).comap smaller := by
          rw [
            V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceProduct_comap_eq_volume_smul
              S T]
    _ = V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
          (((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
            ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
              S T).prod
              (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
                T))).comap smaller) := by
          rw [Measure.comap_smul]
    _ = V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S := by
          rw [
            ← V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_map_smallerTransition
              S T hST,
            smaller.measurableEmbedding.comap_map]

/-! ## Exact mixed-cylinder transition -/

/-- Comapping the `T` direct mixed-block cylinder along the literal
componentwise block embedding gives the literal transition volume times the
`S` cylinder. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure T).comap
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
          S T hST) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
        V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure S := by
  let sourceToMixedS :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph S
  let sourceToMixedT :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph T
  let embedding :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
      S T hST
  let coordinate :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
      S T hST
  have hEmbedding : MeasurableEmbedding embedding :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
      S T hST
  have hCoordinate : MeasurableEmbedding coordinate :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinate_measurableEmbedding
      S T hST
  have hfun :
      embedding ∘ sourceToMixedS = sourceToMixedT ∘ coordinate := by
    funext g
    change
      embedding (sourceToMixedS g) =
        sourceToMixedT
          (sourceToMixedT.symm (embedding (sourceToMixedS g)))
    exact (sourceToMixedT.apply_symm_apply _).symm
  unfold finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
  calc
    (Measure.map sourceToMixedT
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          T)).comap embedding =
        Measure.map sourceToMixedS
          (((Measure.map sourceToMixedT
              (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
                T)).comap embedding).comap sourceToMixedS) := by
          rw [
            sourceToMixedS.measurableEmbedding.map_comap,
            sourceToMixedS.surjective.range_eq,
            Measure.restrict_univ]
    _ = Measure.map sourceToMixedS
          ((Measure.map sourceToMixedT
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
              T)).comap (embedding ∘ sourceToMixedS)) := by
          rw [Measure.comap_comap
            sourceToMixedS.measurableEmbedding.measurableSet_image'
            hEmbedding.injective
            hEmbedding.measurableSet_image']
    _ = Measure.map sourceToMixedS
          ((Measure.map sourceToMixedT
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
              T)).comap (sourceToMixedT ∘ coordinate)) := by
          rw [hfun]
    _ = Measure.map sourceToMixedS
          (((Measure.map sourceToMixedT
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
              T)).comap sourceToMixedT).comap coordinate) := by
          rw [Measure.comap_comap
            hCoordinate.measurableSet_image'
            sourceToMixedT.injective
            sourceToMixedT.measurableEmbedding.measurableSet_image']
    _ = Measure.map sourceToMixedS
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
            T).comap coordinate) := by
          rw [sourceToMixedT.measurableEmbedding.comap_map]
    _ = Measure.map sourceToMixedS
          (V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
              S) := by
          rw [
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_comap_transition
              S T hST]
    _ = V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
          Measure.map sourceToMixedS
            (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
              S) := by
          rw [Measure.map_smul]

end RationalQuadraticSpaceMatrix
