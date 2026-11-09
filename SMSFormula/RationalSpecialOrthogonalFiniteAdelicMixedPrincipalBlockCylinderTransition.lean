import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockProductComap

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
theorem measurePreserving_infinitePiEquivPiSubtypeProd
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

local instance mixedPrincipalBlockCylinderTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance mixedPrincipalBlockCylinderTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance mixedPrincipalBlockCylinderTransitionGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance mixedPrincipalBlockCylinderTransitionGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance mixedPrincipalBlockCylinderTransitionGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance mixedPrincipalBlockCylinderTransitionIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockCylinderTransitionIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockCylinderTransitionLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockCylinderTransitionLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockCylinderTransitionExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderTransitionExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Pi.borelSpace

local instance mixedPrincipalBlockCylinderTransitionNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderTransitionNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance mixedPrincipalBlockCylinderTransitionNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderTransitionNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  Pi.borelSpace

local instance mixedPrincipalBlockCylinderTransitionTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderTransitionTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

local instance mixedPrincipalBlockCylinderTransitionMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderTransitionMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

/-! ## Exact index reindexings -/

private def exceptionalOldIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    {v // v ∈ S} ≃ {v : {v // v ∈ T} // v.1 ∈ S} where
  toFun v := ⟨⟨v.1, hST v.2⟩, v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def exceptionalNewIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ T \ S} ≃ {v : {v // v ∈ T} // v.1 ∉ S} where
  toFun v :=
    ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
      (Finset.mem_sdiff.mp v.2).2⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.1.2, v.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def tailNewIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ T \ S} ≃ {v : {v // v ∉ S} // v.1 ∈ T} where
  toFun v :=
    ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
      (Finset.mem_sdiff.mp v.2).1⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.2, v.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def tailCommonIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    {v // v ∉ T} ≃ {v : {v // v ∉ S} // v.1 ∉ T} where
  toFun v := ⟨⟨v.1, fun hv => v.2 (hST hv)⟩, v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Exceptional and tail measure splittings -/

/-- The finite exceptional product at `T` splits into the old exceptional
product at `S` and the unrestricted product on the new coordinates `T \ S`. -/
theorem
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_map_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicSpecialOrthogonalExceptionalTransitionHomeomorph
          S T hST)
        (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure T) =
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
        (V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T) := by
  let p : {v // v ∈ T} → Prop := fun v => v.1 ∈ S
  let oldReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈ S} =>
        V.HeightOnePadicSpecialOrthogonalGroup v.1)
      (exceptionalOldIndexEquiv S T hST).symm
  let newReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈ T \ S} =>
        V.HeightOnePadicSpecialOrthogonalGroup v.1)
      (exceptionalNewIndexEquiv S T).symm
  have hPart :=
    measurePreserving_piEquivPiSubtypeProd
      (fun v : {v // v ∈ T} =>
        V.heightOnePadicInvariantDifferentialGroupMeasure v.1)
      p
  have hOld :=
    measurePreserving_piCongrLeft
      (fun v : {v // v ∈ S} =>
        V.heightOnePadicInvariantDifferentialGroupMeasure v.1)
      (exceptionalOldIndexEquiv S T hST).symm
  have hNew :=
    measurePreserving_piCongrLeft
      (fun v : {v // v ∈ T \ S} =>
        V.heightOnePadicInvariantDifferentialGroupMeasure v.1)
      (exceptionalNewIndexEquiv S T).symm
  have hCombined := (hOld.prod hNew).comp hPart
  have hfun :
      (Prod.map oldReindex newReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : {v // v ∈ T} =>
              V.HeightOnePadicSpecialOrthogonalGroup v.1)
            p) =
        V.finiteAdelicSpecialOrthogonalExceptionalTransitionHomeomorph
          S T hST := by
    funext g
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl
  simpa only [
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure,
    finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure,
    hfun] using hCombined.map_eq

set_option backward.isDefEq.respectTransparency false in
/-- The normalized integral tail at `S` splits into the normalized finite
product on the new coordinates `T \ S` and the normalized common tail outside
`T`. -/
theorem
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_map_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionHomeomorph
          S T hST)
        (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) =
      (V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
        S T).prod
        (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      IsProbabilityMeasure
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isProbability
      V v
  let p : {v // v ∉ S} → Prop := fun v => v.1 ∈ T
  let newReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈ T \ S} =>
        V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)
      (tailNewIndexEquiv S T).symm
  let commonReindex :=
    MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∉ T} =>
        V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)
      (tailCommonIndexEquiv S T hST).symm
  have hPart :=
    Measure.measurePreserving_infinitePiEquivPiSubtypeProd
      (fun v : {v // v ∉ S} =>
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
      p
  have hNew :
      MeasurePreserving newReindex
        (Measure.infinitePi fun
          v : {v : {v // v ∉ S} // p v} =>
            V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
              v.1.1)
        (V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
          S T) := by
    refine ⟨newReindex.measurable, ?_⟩
    simpa only [
      finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure,
      Measure.infinitePi_eq_pi] using
        (Measure.infinitePi_map_piCongrLeft
          (fun v : {v // v ∈ T \ S} =>
            V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
          (tailNewIndexEquiv S T).symm)
  have hCommon :
      MeasurePreserving commonReindex
        (Measure.infinitePi fun
          v : {v : {v // v ∉ S} // ¬ p v} =>
            V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
              v.1.1)
        (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) := by
    refine ⟨commonReindex.measurable, ?_⟩
    simpa only [
      finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure] using
        (Measure.infinitePi_map_piCongrLeft
          (fun v : {v // v ∉ T} =>
            V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
          (tailCommonIndexEquiv S T hST).symm)
  letI : SFinite
      (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} =>
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} =>
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) :=
      inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} =>
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} =>
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  letI : SFinite
      (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} =>
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} =>
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) :=
      inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} =>
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} =>
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hCombined := (hNew.prod hCommon).comp hPart
  have hfun :
      (Prod.map newReindex commonReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : {v // v ∉ S} =>
              V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)
            p) =
        V.finiteAdelicSpecialOrthogonalIntegralTailTransitionHomeomorph
          S T hST := by
    funext g
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl
  simpa only [
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure,
    hfun] using hCombined.map_eq

/-! ## Nested transition coordinates -/

/-- Split the `T` source coordinates and reassociate them as
`old exceptional × (new unrestricted × common tail)`. -/
def finiteAdelicSpecialOrthogonalLargerTransitionSourceHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T) ≃ₜ
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T ×
          V.FiniteAdelicSpecialOrthogonalIntegralTail T)) :=
  (Homeomorph.prodCongr
      (V.finiteAdelicSpecialOrthogonalExceptionalTransitionHomeomorph
        S T hST)
      (Homeomorph.refl _)).trans
    (Homeomorph.prodAssoc _ _ _)

/-- Split the `S` source tail as
`old exceptional × (new integral × common tail)`. -/
def finiteAdelicSpecialOrthogonalSmallerTransitionSourceHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) ≃ₜ
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
          V.FiniteAdelicSpecialOrthogonalIntegralTail T)) :=
  Homeomorph.prodCongr
    (Homeomorph.refl _)
    (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionHomeomorph
      S T hST)

/-- In nested transition coordinates, the conjugated mixed-block embedding is
the literal identity on old exceptional coordinates and the common tail, with
only the new integral coordinates included into the unrestricted groups. -/
theorem
    finiteAdelicSpecialOrthogonalTransitionSourceHomeomorph_exact
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) :
    V.finiteAdelicSpecialOrthogonalLargerTransitionSourceHomeomorph
        S T hST
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
          S T hST g) =
      V.finiteAdelicSpecialOrthogonalTransitionSourceInclusion S T
        (V.finiteAdelicSpecialOrthogonalSmallerTransitionSourceHomeomorph
          S T hST g) := by
  change
    let q :=
      (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv S T hST
          ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
            S T hST g).1),
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
          S T hST g).2)
    (q.1.1, q.1.2, q.2) =
      _
  rw [
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinate_exact
      S T hST g]
  rfl

/-- The `T` exceptional/tail source measure becomes the literal nested product
of the old exceptional, new unrestricted, and common-tail measures. -/
theorem
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_map_largerTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicSpecialOrthogonalLargerTransitionSourceHomeomorph
          S T hST)
        (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
          T) =
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
        ((V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T).prod
          (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure T) :=
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isSigmaFinite V T
  letI : SFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure T) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) :=
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability
      V T
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  have hidTail :
      Measure.map (fun g => g)
          (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) =
        V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T := by
    exact Measure.map_id
  have hAssoc :
      Measure.map
          (Homeomorph.prodAssoc
            (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S)
            (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T)
            (V.FiniteAdelicSpecialOrthogonalIntegralTail T))
          (((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
              (V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure
                S T)).prod
            (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T)) =
        (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
          ((V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure
            S T).prod
            (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T)) := by
    exact Measure.prodAssoc_prod
  unfold
    finiteAdelicSpecialOrthogonalLargerTransitionSourceHomeomorph
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
  change
    Measure.map
        ((Homeomorph.prodAssoc
          (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S)
          (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T)
          (V.FiniteAdelicSpecialOrthogonalIntegralTail T)) ∘
          Prod.map
            (V.finiteAdelicSpecialOrthogonalExceptionalTransitionHomeomorph
              S T hST)
            (fun g => g))
        ((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure T).prod
          (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T)) =
      _
  rw [
    ← Measure.map_map,
    ← Measure.map_prod_map,
    V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure_map_transition
      S T hST,
    hidTail,
    hAssoc]
  all_goals fun_prop

/-- The `S` exceptional/tail source measure becomes the literal nested product
of the old exceptional, new normalized integral, and common-tail measures. -/
theorem
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_map_smallerTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicSpecialOrthogonalSmallerTransitionSourceHomeomorph
          S T hST)
        (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
          S) =
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
        ((V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
          S T).prod
          (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) :=
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isSigmaFinite V S
  letI : SFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability
      V S
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  have hid :
      Measure.map
          (Homeomorph.refl
            (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S))
          (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) =
        V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S := by
    exact Measure.map_id
  unfold
    finiteAdelicSpecialOrthogonalSmallerTransitionSourceHomeomorph
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
  rw [
    Homeomorph.coe_prodCongr,
    ← Measure.map_prod_map,
    hid,
    V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_map_transition
      S T hST]
  all_goals fun_prop

/-- The conjugated exceptional/tail coordinate embedding is measurably
embedded; this follows directly by conjugating the genuine mixed-block
measurable embedding by the two direct source homeomorphisms. -/
theorem
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinate_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
        S T hST) := by
  simpa only [
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom,
    MonoidHom.coe_comp,
    Function.comp_def] using
      ((V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph T).symm
        |>.measurableEmbedding.comp
          ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
              S T hST).comp
            (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S
              |>.measurableEmbedding)))

/-- The exact transition formula on the direct exceptional/tail source
carriers. -/
theorem
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
        T).comap
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
          S T hST) =
      V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
        V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
          S := by
  let larger :=
    V.finiteAdelicSpecialOrthogonalLargerTransitionSourceHomeomorph S T hST
  let smaller :=
    V.finiteAdelicSpecialOrthogonalSmallerTransitionSourceHomeomorph S T hST
  let coordinate :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
      S T hST
  let inclusion :=
    V.finiteAdelicSpecialOrthogonalTransitionSourceInclusion S T
  have hCoordinate : MeasurableEmbedding coordinate :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinate_measurableEmbedding
      S T hST
  have hInclusion : MeasurableEmbedding inclusion := by
    let hIdOld :=
      (MeasurableEquiv.refl
        (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S))
        |>.measurableEmbedding
    let hIdTail :=
      (MeasurableEquiv.refl
        (V.FiniteAdelicSpecialOrthogonalIntegralTail T))
        |>.measurableEmbedding
    have hNewTail :=
      (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusion_measurableEmbedding
        S T).prodMap hIdTail
    simpa only [
      inclusion,
      finiteAdelicSpecialOrthogonalTransitionSourceInclusion] using
        hIdOld.prodMap hNewTail
  have hfun : larger ∘ coordinate = inclusion ∘ smaller := by
    funext g
    exact
      V.finiteAdelicSpecialOrthogonalTransitionSourceHomeomorph_exact
        S T hST g
  calc
    (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
        T).comap coordinate =
        ((Measure.map larger
          (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
            T)).comap larger).comap coordinate := by
          rw [larger.measurableEmbedding.comap_map]
    _ = (Measure.map larger
          (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
            T)).comap (larger ∘ coordinate) := by
          rw [Measure.comap_comap
            hCoordinate.measurableSet_image'
            larger.injective
            larger.measurableEmbedding.measurableSet_image']
    _ = (Measure.map larger
          (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
            T)).comap (inclusion ∘ smaller) := by rw [hfun]
    _ = ((Measure.map larger
          (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
            T)).comap inclusion).comap smaller := by
          rw [Measure.comap_comap
            smaller.measurableEmbedding.measurableSet_image'
            hInclusion.injective
            hInclusion.measurableSet_image']
    _ = (((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
            ((V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure
              S T).prod
              (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
                T))).comap inclusion).comap smaller := by
          rw [
            V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_map_largerTransition
              S T hST]
    _ = (V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
          ((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
            ((V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
              S T).prod
              (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
                T)))).comap smaller := by
          rw [
            V.finiteAdelicSpecialOrthogonalTransitionSourceProduct_comap_eq_volume_smul
              S T]
    _ = V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
          (((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
            ((V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
              S T).prod
              (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
                T))).comap smaller) := by
          rw [Measure.comap_smul]
    _ = V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
        V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
          S := by
          rw [
            ← V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_map_smallerTransition
              S T hST,
            smaller.measurableEmbedding.comap_map]

/-! ## Exact mixed-cylinder transition -/

/-- Comapping the `T` direct mixed-block cylinder along the literal
componentwise block embedding gives the literal transition volume times the
`S` cylinder. -/
theorem
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure T).comap
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
          S T hST) =
      V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
        V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S := by
  let sourceToMixedS :=
    V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S
  let sourceToMixedT :=
    V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph T
  let embedding :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
      S T hST
  let coordinate :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
      S T hST
  have hEmbedding : MeasurableEmbedding embedding :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
      S T hST
  have hCoordinate : MeasurableEmbedding coordinate :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinate_measurableEmbedding
      S T hST
  have hfun :
      embedding ∘ sourceToMixedS = sourceToMixedT ∘ coordinate := by
    funext g
    change
      embedding (sourceToMixedS g) =
        sourceToMixedT
          (sourceToMixedT.symm (embedding (sourceToMixedS g)))
    exact (sourceToMixedT.apply_symm_apply _).symm
  unfold finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
  calc
    (Measure.map sourceToMixedT
        (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
          T)).comap embedding =
        Measure.map sourceToMixedS
          (((Measure.map sourceToMixedT
              (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
                T)).comap embedding).comap sourceToMixedS) := by
          rw [
            sourceToMixedS.measurableEmbedding.map_comap,
            sourceToMixedS.surjective.range_eq,
            Measure.restrict_univ]
    _ = Measure.map sourceToMixedS
          ((Measure.map sourceToMixedT
            (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
              T)).comap (embedding ∘ sourceToMixedS)) := by
          rw [Measure.comap_comap
            sourceToMixedS.measurableEmbedding.measurableSet_image'
            hEmbedding.injective
            hEmbedding.measurableSet_image']
    _ = Measure.map sourceToMixedS
          ((Measure.map sourceToMixedT
            (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
              T)).comap (sourceToMixedT ∘ coordinate)) := by
          rw [hfun]
    _ = Measure.map sourceToMixedS
          (((Measure.map sourceToMixedT
            (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
              T)).comap sourceToMixedT).comap coordinate) := by
          rw [Measure.comap_comap
            hCoordinate.measurableSet_image'
            sourceToMixedT.injective
            sourceToMixedT.measurableEmbedding.measurableSet_image']
    _ = Measure.map sourceToMixedS
          ((V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
            T).comap coordinate) := by
          rw [sourceToMixedT.measurableEmbedding.comap_map]
    _ = Measure.map sourceToMixedS
          (V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
            V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
              S) := by
          rw [
            V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_comap_transition
              S T hST]
    _ = V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
          Measure.map sourceToMixedS
            (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
              S) := by
          rw [Measure.map_smul]

end RationalQuadraticSpaceMatrix
