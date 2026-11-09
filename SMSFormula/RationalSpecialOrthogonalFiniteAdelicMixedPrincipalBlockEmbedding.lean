import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockTransition
import Mathlib.Topology.Defs.Induced

/-!
# Direct embeddings between mixed finite-adelic principal blocks

For finite exceptional sets `S ⊆ T`, this module embeds the direct mixed
`S`-block into the direct mixed `T`-block without transporting any topology
through the restricted-family carrier.  Its range is the literal open
subcarrier on which every new `T \ S` coordinate remains integral.

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
theorem comap_prodMap
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
theorem comap_id_prodMap_id
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
    rw [comap_prodMap hf hκ, comap_id]
    infer_instance
  rw [comap_prodMap hμ (hf.prodMap hκ)]
  rw [comap_id, comap_prodMap hf hκ, comap_id]

end MeasureTheory.Measure

namespace RationalQuadraticSpaceMatrix

noncomputable section

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance mixedPrincipalBlockEmbeddingDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance mixedPrincipalBlockEmbeddingPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance mixedPrincipalBlockEmbeddingGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance mixedPrincipalBlockEmbeddingGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
  BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance mixedPrincipalBlockEmbeddingGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance mixedPrincipalBlockEmbeddingIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockEmbeddingIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockEmbeddingLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockEmbeddingLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockEmbeddingMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockEmbeddingMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance mixedPrincipalBlockEmbeddingNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockEmbeddingNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance mixedPrincipalBlockEmbeddingNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockEmbeddingNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  Pi.borelSpace

/-! ## Inclusion of the new integral coordinates -/

/-- Componentwise inclusion of the new integral coordinates into the new
unrestricted exceptional coordinates. -/
def finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T →*
      V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T where
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
theorem finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T)
    (v : {v // v ∈ T \ S}) :
    V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom S T g v =
      (g v).1 :=
  rfl

/-- The componentwise inclusion of the finitely many new integral factors is
continuous. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
        S T) := by
  apply continuous_pi
  intro v
  exact continuous_subtype_val.comp (continuous_apply v)

/-- The finite product of open integral-subgroup inclusions is a measurable
embedding. -/
theorem
    finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
        S T) := by
  have hlocal :
      ∀ v : {v // v ∈ T \ S},
        Topology.IsOpenEmbedding
          (fun g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 =>
            (g : V.HeightOnePadicSpecialOrthogonalGroup v.1)) := by
    intro v
    exact
      (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1)
        |>.isOpenEmbedding_subtypeVal
  exact (Topology.IsOpenEmbedding.piMap hlocal).measurableEmbedding

/-! ## The direct mixed-block embedding -/

/-- Direct componentwise inclusion of the mixed `S`-block into the mixed
`T`-block for `S ⊆ T`.  The underlying local matrix is unchanged. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S →*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock T where
  toFun g v :=
    ⟨(g v).1, fun hvT => (g v).2 (fun hvS => hvT (hST hvS))⟩
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
underlying local special-orthogonal component. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
      S T hST g v).1 = (g v).1 :=
  rfl

/-- The direct mixed-block transition embedding is continuous for the
displayed dependent-product topologies. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
        S T hST) := by
  apply continuous_pi
  intro v
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (continuous_apply v)

/-- The literal subcarrier of the `T`-block where every new coordinate in
`T \ S` remains integral. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock T) :=
  {g | ∀ v : {v // v ∈ T \ S},
    V.HeightOnePadicSpecialOrthogonalIsIntegral v.1 (g v.1).1}

/-- The transition range is open: it imposes finitely many open integral
local-factor conditions. -/
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange_isOpen
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange S T) := by
  rw [show
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange S T =
        ⋂ v : {v // v ∈ T \ S},
          {g | V.HeightOnePadicSpecialOrthogonalIsIntegral v.1 (g v.1).1} by
    ext g
    simp [finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange]]
  apply isOpen_iInter_of_finite
  intro v
  change IsOpen
    ((fun g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock T =>
      (g v.1).1) ⁻¹'
        (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v.1 :
          Set (V.HeightOnePadicSpecialOrthogonalGroup v.1)))
  exact
    (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1).preimage
      (continuous_subtype_val.comp (continuous_apply v.1))

/-- The `S`-block is directly homeomorphic to the literal integral-coordinate
range inside the `T`-block. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRangeHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S ≃ₜ
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange S T where
  toFun g :=
    ⟨V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
        S T hST g, by
      intro v
      exact (g v.1).2 (Finset.mem_sdiff.mp v.2).2⟩
  invFun g v :=
    ⟨(g.1 v).1, by
      intro hvS
      by_cases hvT : v ∈ T
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
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
        S T hST) :=
  ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange_isOpen
      S T).isOpenEmbedding_subtypeVal.comp
    (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRangeHomeomorph
      S T hST).isOpenEmbedding
  ).measurableEmbedding

/-- The set-theoretic range of the transition embedding is exactly the
literal new-coordinate integrality subcarrier. -/
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbedding_range
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Set.range
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
          S T hST) =
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange S T := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    intro v
    exact (a v.1).2 (Finset.mem_sdiff.mp v.2).2
  · intro hg
    let y :
        V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRange S T :=
      ⟨g, hg⟩
    refine
      ⟨(V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRangeHomeomorph
        S T hST).symm y, ?_⟩
    exact congrArg Subtype.val
      ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionRangeHomeomorph
        S T hST).apply_symm_apply y)

/-- Conjugation of the direct mixed-block embedding by the direct
exceptional/tail product splittings. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) →*
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T) :=
  (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv T).symm.toMonoidHom.comp
    ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
      S T hST).comp
      (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv S).toMonoidHom)

/-- Exact product-coordinate formula for the conjugated embedding: old
exceptional coordinates and the common tail are fixed, while new integral
coordinates are included into the new unrestricted exceptional product. -/
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinate_exact
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv S T hST
        ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
          S T hST g).1),
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
        S T hST g).2) =
      ((g.1, fun v =>
          V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
            S T
            (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv
              S T hST g.2).1 v),
        (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv
          S T hST g.2).2) := by
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [
        finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom,
        finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom]
    · funext v
      have hvS := (Finset.mem_sdiff.mp v.2).2
      simpa [
        finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom,
        finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom] using
        V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_apply_notMem
          S g v.1 hvS
  · funext v
    apply Subtype.ext
    have hvS : v.1 ∉ S := fun hv => v.2 (hST hv)
    simpa [
      finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom,
      finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom] using
      V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_apply_notMem
        S g v.1 hvS

/-- The conjugated exceptional/tail coordinate embedding is continuous. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionCoordinateHom
        S T hST) :=
  (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv T).symm.continuous.comp
    ((V.continuous_finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
      S T hST).comp
      (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv S).continuous)

end

end RationalQuadraticSpaceMatrix
