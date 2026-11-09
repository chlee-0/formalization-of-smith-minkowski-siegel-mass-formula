import SMSFormula.RationalSpecialOrthogonalFiniteAdelicGenuinePrincipalBlockCarrier

/-!
# Measures on genuine finite-adelic principal blocks

The coherent cylinder on the direct mixed `S`-block is transported through
the inverse of the genuine/direct block homeomorphism.  This gives a
left-invariant measure on the genuine open finite-adelic principal block,
with a literal map-back formula.

For `S ⊆ T`, the genuine block inclusion is the identity on the underlying
finite-adelic element.  It is continuous and measurably embedded.  The exact
conjugation square with the direct mixed-block embedding transfers the
already proved coherent-cylinder compatibility to the genuine blocks.

No measure on the full finite-adelic group is constructed here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance genuinePrincipalBlockMeasurePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance genuinePrincipalBlockMeasureGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance genuinePrincipalBlockMeasureGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance genuinePrincipalBlockMeasureGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance genuinePrincipalBlockMeasureLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance genuinePrincipalBlockMeasureLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance genuinePrincipalBlockMeasureMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance genuinePrincipalBlockMeasureMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance genuinePrincipalBlockMeasureFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance genuinePrincipalBlockMeasureFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance genuinePrincipalBlockMeasureGenuineMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  borel _

local instance genuinePrincipalBlockMeasureGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  ⟨rfl⟩

/-! ## The transported genuine-block measure -/

/-- The coherent cylinder transported from the direct mixed block to the
genuine open finite-adelic principal block. -/
def finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  Measure.map
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S).symm
    (V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
      S)

/-- Mapping the genuine-block measure back by simultaneous evaluation
recovers the literal coherent mixed-block cylinder. -/
theorem
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_map
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S)
        (V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
          S) =
      V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        S := by
  unfold
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
  exact
    MeasurableEquiv.map_map_symm
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
        |>.toMeasurableEquiv)

/-- Equivalently, the genuine-block measure is the comap of the coherent
mixed cylinder along simultaneous evaluation. -/
theorem
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_eq_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S =
      (V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        S).comap
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S) := by
  let e :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
  let μ :=
    V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
      S
  change Measure.map e.symm μ = μ.comap e
  calc
    Measure.map e.symm μ =
        (Measure.map e (Measure.map e.symm μ)).comap e := by
          rw [e.measurableEmbedding.comap_map]
    _ = μ.comap e := by
      exact congrArg (fun ν : Measure _ => ν.comap e)
        (MeasurableEquiv.map_map_symm e.toMeasurableEquiv)

/-- The transported genuine empty-block measure has total mass one. -/
@[simp]
theorem
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_empty_univ
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
        ∅ Set.univ = 1 := by
  rw [finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure]
  rw [Measure.map_apply
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph
      ∅).symm.measurable MeasurableSet.univ]
  simp

/-- Scalar multiplication preserves the left invariance of the unscaled
direct mixed-block cylinder. -/
instance
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        S) := by
  letI : Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S) :=
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_isMulLeftInvariant
      V S
  unfold
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
  constructor
  intro g
  rw [Measure.map_smul]
  rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self g]

/-- The transported measure is left invariant on the genuine principal
block. -/
instance
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
        S) := by
  letI : Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
        S) :=
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure_isMulLeftInvariant
      V S
  unfold
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
  exact
    isMulLeftInvariant_map
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockContinuousMulEquiv
        S).symm.toMulHom
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph
        S).symm.measurable
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph
        S).symm.surjective

/-! ## Genuine block inclusions -/

/-- Inclusion of the genuine `S` block into the genuine `T` block for
`S ⊆ T`.  The underlying finite-adelic element is unchanged. -/
def finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S →*
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock T where
  toFun a := ⟨a.1, by
    change
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv a.1 ∈
        V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock T
    exact
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock_mono hST
        a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The genuine block inclusion is literally the identity on the underlying
finite-adelic element. -/
@[simp]
theorem
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
      S T hST a).1 = a.1 :=
  rfl

/-- The genuine block inclusion is continuous for the subtype topologies
inherited from the finite adeles. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
        S T hST) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The genuine block inclusion conjugates exactly to the direct mixed-block
transition embedding. -/
theorem
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_conjugation
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph T
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
          S T hST a) =
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
        S T hST
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
          a) := by
  funext v
  apply Subtype.ext
  rfl

/-- The genuine block inclusion is a measurable embedding.  This follows
from its exact conjugation to the already verified direct mixed-block
embedding, not from any unrestricted local-family topology. -/
theorem
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
        S T hST) := by
  let eS :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
  let eT :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph T
  let j :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
      S T hST
  let i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
      S T hST
  have hfun : i = eT.symm ∘ j ∘ eS := by
    funext a
    apply eT.injective
    change eT (i a) = eT (eT.symm (j (eS a)))
    rw [eT.apply_symm_apply]
    exact
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_conjugation
        S T hST a
  rw [hfun]
  exact
    eT.symm.measurableEmbedding.comp
      ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
        S T hST).comp eS.measurableEmbedding)

/-! ## Exact compatibility on genuine blocks -/

/-- The coherent genuine-block measures comap literally along every genuine
principal-block inclusion. -/
theorem
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
        T).comap
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
          S T hST) =
      V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
        S := by
  let eS :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
  let eT :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph T
  let j :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbeddingHom
      S T hST
  let i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
      S T hST
  let μS :=
    V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
      S
  let μT :=
    V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
      T
  have hi :
      MeasurableEmbedding i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_measurableEmbedding
      S T hST
  have hj :
      MeasurableEmbedding j :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
      S T hST
  have hfun : eT ∘ i = j ∘ eS := by
    funext a
    exact
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_conjugation
        S T hST a
  rw [
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_eq_comap
      T,
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_eq_comap
      S]
  change (μT.comap eT).comap i = μS.comap eS
  calc
    (μT.comap eT).comap i =
        μT.comap (eT ∘ i) := by
          rw [Measure.comap_comap
            hi.measurableSet_image'
            eT.injective
            eT.measurableEmbedding.measurableSet_image']
    _ = μT.comap (j ∘ eS) := by rw [hfun]
    _ = (μT.comap j).comap eS := by
      rw [Measure.comap_comap
        eS.measurableEmbedding.measurableSet_image'
        hj.injective
        hj.measurableSet_image']
    _ = μS.comap eS := by
      rw [
        V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure_comap
          S T hST]

end RationalQuadraticSpaceMatrix
