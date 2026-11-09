import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockTransition
import Mathlib.Topology.Defs.Induced

/-!
# Direct embeddings between mixed finite-adelic principal blocks

For finite exceptional sets `S ⊆ T`, this module embeds the direct mixed
`S`-block into the direct mixed `T`-block without transporting any topology
through the restricted-family carrier.  Its range is the literal open
subcarrier on which every new `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)` coordinate remains integral.

Conjugating by the direct exceptional/tail splittings records the exact
coordinate formula: the old exceptional coordinates and common tail are
unchanged, while each new finite coordinate is included from its integral
subgroup into the full local group.

The module also proves reusable binary and nested product-comap lemmas for
measurable embeddings and sigma-finite measures.  These are the precise
measure-theoretic input needed for the subsequent cylinder transition
formula.  No measure is transported through the restricted-family block
equivalence and no global finite-adelic measure is constructed.
-/

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- Comapping a product measure along the product of two measurable embeddings
is the product of the two comapped measures. -/
theorem comap_prodMap_cliffordSpinCandidate
    {f : α → β} {g : γ → δ}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (μ : Measure β) (ν : Measure δ)
    [SigmaFinite μ] [SigmaFinite ν]
    [SigmaFinite (μ.comap f)] [SigmaFinite (ν.comap g)] :
    (μ.prod ν).comap (Prod.map f g) =
      (μ.comap f).prod (ν.comap g) := by
  symm
  apply prod_eq
  intro s t hs ht
  rw [(hf.prodMap hg).comap_apply, Set.prodMap_image_prod,
    prod_prod, hf.comap_apply, hg.comap_apply]

/-- Nested specialization of `comap_prodMap`: the old and common-tail
coordinates are unchanged, and only the middle coordinate is embedded. -/
theorem comap_id_prodMap_id_cliffordSpinCandidate
    {ε ζ : Type*} [MeasurableSpace ε] [MeasurableSpace ζ]
    {f : γ → δ} (hf : MeasurableEmbedding f)
    (μ : Measure ε) (ν : Measure δ) (κ : Measure ζ)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    [SigmaFinite (ν.comap f)] :
    (μ.prod (ν.prod κ)).comap
        (Prod.map (fun x => x) (Prod.map f (fun x => x))) =
      μ.prod ((ν.comap f).prod κ) := by
  have hμ : MeasurableEmbedding (fun x : ε => x) :=
    MeasurableEmbedding.id
  have hκ : MeasurableEmbedding (fun x : ζ => x) :=
    MeasurableEmbedding.id
  letI : SigmaFinite (κ.comap (fun x => x)) := by
    rw [comap_id]
    infer_instance
  letI : SigmaFinite (μ.comap (fun x => x)) := by
    rw [comap_id]
    infer_instance
  letI : SigmaFinite
      ((ν.prod κ).comap (Prod.map f (fun x => x))) := by
    rw [comap_prodMap_cliffordSpinCandidate hf hκ, comap_id]
    infer_instance
  rw [comap_prodMap_cliffordSpinCandidate hμ (hf.prodMap hκ)]
  rw [comap_id, comap_prodMap_cliffordSpinCandidate hf hκ, comap_id]

end MeasureTheory.Measure

namespace RationalQuadraticSpaceMatrix

noncomputable section

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
  BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∈
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
        ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∈
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
        ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockEmbeddingNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  Pi.borelSpace

/-! ## Inclusion of the new integral coordinates -/

/-- Componentwise inclusion of the new integral coordinates into the new
unrestricted exceptional coordinates. -/
def finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T →*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T where
  toFun g v := (g v).1
  map_one' := by
    funext v
    rfl
  map_mul' := by
    intro g h
    funext v
    rfl

/-- The new-coordinate inclusion is literal componentwise subtype coercion. -/
@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T)
    (v : {v // v ∈
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom S T g v =
      (g v).1 :=
  rfl

/-- The componentwise inclusion of the finitely many new integral factors is
continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
        S T) := by
  apply continuous_pi
  intro v
  exact continuous_subtype_val.comp (continuous_apply v)

/-- The finite product of open integral-subgroup inclusions is a measurable
embedding. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
        S T) := by
  have hlocal :
      ∀ v : {v // v ∈
          (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
            (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)},
        Topology.IsOpenEmbedding
          (fun g :
              V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
                S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ =>
            (g : V.HeightOnePadicCliffordSpinCandidateGroup v.1)) := by
    intro v
    exact
      (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v.1 (Finset.mem_sdiff.mp v.2).2)
        |>.isOpenEmbedding_subtypeVal
  exact (Topology.IsOpenEmbedding.piMap hlocal).measurableEmbedding

/-! ## The direct mixed-block embedding -/

/-- Direct componentwise inclusion of the mixed `S`-block into the mixed
`T`-block for `S ⊆ T`.  The underlying local matrix is unchanged. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock T where
  toFun g v :=
    ⟨(g v).1, fun hvT => (g v).2 (fun hvS =>
      hvT
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hvS))⟩
  map_one' := by
    funext v
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    funext v
    apply Subtype.ext
    rfl

/-- The direct transition embedding is literally the identity on every
underlying local Clifford--Spin candidate component. -/
@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
      S T hST g v).1 = (g v).1 :=
  rfl

/-- The direct mixed-block transition embedding is continuous for the
displayed dependent-product topologies. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
        S T hST) := by
  apply continuous_pi
  intro v
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (continuous_apply v)

/-- The literal subcarrier of the `T`-block where every new coordinate in
`(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)` remains integral. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock T) :=
  {g | ∀ v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)},
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 (g v.1).1}

/-- The transition range is open: it imposes finitely many open integral
local-factor conditions. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange_isOpen
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange S T) := by
  rw [show
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange S T =
        ⋂ v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)},
          {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 (g v.1).1} by
    ext g
    simp [finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange]]
  apply isOpen_iInter_of_finite
  intro v
  change IsOpen
    ((fun g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock T =>
      (g v.1).1) ⁻¹'
        {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g})
  exact
    (V.isOpen_heightOnePadicCliffordSpinCandidateIsIntegral v.1).preimage
      (continuous_subtype_val.comp (continuous_apply v.1))

/-- The `S`-block is directly homeomorphic to the literal integral-coordinate
range inside the `T`-block. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRangeHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S ≃ₜ
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange S T where
  toFun g :=
    ⟨V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
        S T hST g, by
      intro v
      exact (g v.1).2 (Finset.mem_sdiff.mp v.2).2⟩
  invFun g v :=
    ⟨(g.1 v).1, by
      intro hvS
      by_cases hvT : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T
      · exact g.2 ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvS⟩⟩
      · exact (g.1 v).2 hvT⟩
  left_inv := by
    intro g
    funext v
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    funext v
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_apply v)
  continuous_invFun := by
    apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact
      continuous_subtype_val.comp
        ((continuous_apply v).comp continuous_subtype_val)

/-- The direct block transition is a measurable embedding, obtained from its
explicit homeomorphism onto the literal open transition range. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
        S T hST) :=
  ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange_isOpen
      S T).isOpenEmbedding_subtypeVal.comp
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRangeHomeomorph
      S T hST).isOpenEmbedding
  ).measurableEmbedding

/-- The set-theoretic range of the transition embedding is exactly the
literal new-coordinate integrality subcarrier. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbedding_range
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Set.range
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
          S T hST) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange S T := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    intro v
    exact (a v.1).2 (Finset.mem_sdiff.mp v.2).2
  · intro hg
    let y :
        V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRange S T :=
      ⟨g, hg⟩
    refine
      ⟨(V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRangeHomeomorph
        S T hST).symm y, ?_⟩
    exact congrArg Subtype.val
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionRangeHomeomorph
        S T hST).apply_symm_apply y)

/-- Conjugation of the direct mixed-block embedding by the direct
exceptional/tail product splittings. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →*
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T) :=
  (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv T).symm.toMonoidHom.comp
    ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
      S T hST).comp
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv S).toMonoidHom)

/-- Exact product-coordinate formula for the conjugated embedding: old
exceptional coordinates and the common tail are fixed, while new integral
coordinates are included into the new unrestricted exceptional product. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinate_exact
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv S T hST
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
          S T hST g).1),
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
        S T hST g).2) =
      ((g.1, fun v =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
            S T
            (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv
              S T hST g.2).1 v),
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv
          S T hST g.2).2) := by
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [
        finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom,
        finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv,
        finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTailHom,
        finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed]
    · funext v
      have hvS :
          v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S :=
        (Finset.mem_sdiff.mp v.2).2
      simp [
        finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom,
        finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv,
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv,
        finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTailHom,
        finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed,
        hvS]
  · funext v
    apply Subtype.ext
    have hvS :
        v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S :=
      fun hv =>
        v.2
          (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv)
    simp [
      finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom,
      finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom,
      finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv,
      finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit,
      finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv,
      finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTailHom,
      finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail,
      finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom,
      finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed,
      hvS]

/-- The conjugated exceptional/tail coordinate embedding is continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionCoordinateHom
        S T hST) :=
  (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv T).symm.continuous.comp
    ((V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
      S T hST).comp
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv S).continuous)

end

end RationalQuadraticSpaceMatrix
