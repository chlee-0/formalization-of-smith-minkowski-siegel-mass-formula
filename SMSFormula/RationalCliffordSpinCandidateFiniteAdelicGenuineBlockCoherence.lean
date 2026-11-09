import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicGenuineAdmissibleBlockMeasure
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicCoherentBlockCylinder

/-!
# Coherent measures on genuine finite-adelic Clifford--Spin blocks

The preceding transition layer made the scaled cylinders on the explicit
mixed local blocks strictly compatible.  This module transports those
cylinders through the completed genuine/mixed block homeomorphisms.

For `S ⊆ T`, the genuine transition map is the literal identity on the
underlying finite-adelic point.  Its conjugation through simultaneous local
evaluation is exactly the completed mixed-block transition embedding.  The
coherent genuine measures therefore comap exactly along block transitions.

The same compatibility is recorded after inclusion into the full finite-
adelic Spin-candidate carrier: the larger supported ambient cylinder restricts
to the smaller one.  No measure on the full carrier is constructed by gluing
these cylinders here, and no analytic top-form or Tamagawa normalization is
asserted.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance finiteAdelicSpinGenuineCoherencePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinGenuineCoherenceGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance finiteAdelicSpinGenuineCoherenceGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicSpinGenuineCoherenceGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance finiteAdelicSpinGenuineCoherenceLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinGenuineCoherenceLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinGenuineCoherenceMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinGenuineCoherenceMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicSpinGenuineCoherenceFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance finiteAdelicSpinGenuineCoherenceFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance finiteAdelicSpinGenuineCoherenceGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Coherent transport to genuine blocks -/

/-- The coherent mixed cylinder transported to the genuine admissible block. -/
def finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Measure.map
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S).symm
    (V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
      S)

/-- Simultaneous local evaluation maps the coherent genuine measure back to
the literal coherent mixed cylinder. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_map
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S)
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
        S := by
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
  exact MeasurableEquiv.map_map_symm
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
      |>.toMeasurableEquiv)

/-- Equivalently, the coherent genuine measure is the comap of the coherent
mixed cylinder along simultaneous local evaluation. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
        S).comap
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
          S) := by
  let e :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
  let μ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
      S
  change Measure.map e.symm μ = μ.comap e
  calc
    Measure.map e.symm μ =
        (Measure.map e (Measure.map e.symm μ)).comap e := by
          rw [e.measurableEmbedding.comap_map]
    _ = μ.comap e := by
      exact congrArg (fun ν : Measure _ => ν.comap e)
        (MeasurableEquiv.map_map_symm e.toMeasurableEquiv)

/-- Coherent transport is exactly baseline-relative scalar multiplication of
the unscaled genuine-block measure. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_weight_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
        V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
          S := by
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
  rw [Measure.map_smul]

/-- The coherent empty-block transport is the already constructed raw
empty-block measure.  No mass-one statement is made. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_empty
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        ∅ =
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        ∅ := by
  rw [
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_weight_smul]
  simp

/-- The coherent genuine-block measure remains left invariant. -/
instance
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S) := by
  rw [
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_weight_smul]
  constructor
  intro g
  rw [Measure.map_smul]
  rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self g]

/-! ## Literal genuine-block transitions -/

/-- Inclusion from the genuine admissible `S` block into the genuine
admissible `T` block for `S ⊆ T`.  The underlying finite-adelic point is
unchanged. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock T where
  toFun a := ⟨a.1, by
    change
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a.1 ∈
        V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
          (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T)
    have ha :
        V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a.1 ∈
          V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
            (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :=
      a.2
    exact
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock_mono
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST) ha⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The genuine transition is literally the identity on the underlying
finite-adelic point. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
      S T hST a).1 = a.1 :=
  rfl

/-- The genuine transition is continuous for the inherited subtype
topologies. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
        S T hST) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The genuine transition conjugates exactly to the direct mixed-block
transition embedding. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_conjugation
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph T
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
          S T hST a) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
        S T hST
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
          a) := by
  funext v
  apply Subtype.ext
  rfl

/-- The genuine transition is a measurable embedding, by its exact
conjugation to the completed mixed-block transition. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
        S T hST) := by
  let eS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
  let eT :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph T
  let j :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
      S T hST
  let i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
      S T hST
  have hfun : i = eT.symm ∘ j ∘ eS := by
    funext a
    apply eT.injective
    change eT (i a) = eT (eT.symm (j (eS a)))
    rw [eT.apply_symm_apply]
    exact
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_conjugation
        S T hST a
  rw [hfun]
  exact eT.symm.measurableEmbedding.comp
    ((V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
      S T hST).comp eS.measurableEmbedding)

/-! ## Exact genuine and ambient compatibility -/

/-- The coherent genuine measures comap literally along every genuine block
transition. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        T).comap
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
          S T hST) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S := by
  let eS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
  let eT :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph T
  let j :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbeddingHom
      S T hST
  let i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
      S T hST
  let μS :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
      S
  let μT :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
      T
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_measurableEmbedding
      S T hST
  have hj : MeasurableEmbedding j :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockTransitionEmbedding_measurableEmbedding
      S T hST
  have hfun : eT ∘ i = j ∘ eS := by
    funext a
    exact
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_conjugation
        S T hST a
  rw [
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_comap
      T,
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_comap
      S]
  change (μT.comap eT).comap i = μS.comap eS
  calc
    (μT.comap eT).comap i = μT.comap (eT ∘ i) := by
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
        V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure_comap
          S T hST]

/-- Pushing the smaller coherent measure into the larger genuine block gives
the restriction of the larger coherent measure to the transition range. -/
theorem
    map_finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
          S T hST)
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S) =
      (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        T).restrict
        (Set.range
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
            S T hST)) := by
  let i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
      S T hST
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_measurableEmbedding
      S T hST
  rw [←
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_comap_transition
      S T hST]
  exact hi.map_comap _

/-- The transition followed by inclusion into the full finite-adelic carrier
is literally the smaller block inclusion. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_comp_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
        T
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
          S T hST a) =
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
        S a :=
  rfl

/-- The coherent genuine-block measure pushed into the full finite-adelic
carrier. -/
def finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure V.FiniteAdelicCliffordSpinCandidateGroup :=
  Measure.map
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S)
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
      S)

/-- The coherent ambient cylinder is the baseline-relative scalar multiple of
the raw ambient cylinder. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_eq_weight_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
        V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
          S := by
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
  rw [
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_weight_smul,
    Measure.map_smul]

/-- Comapping the larger coherent ambient cylinder to the smaller genuine
block recovers the smaller coherent genuine-block measure. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        T).comap
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          S) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S := by
  let iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
  let iT :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      T
  let j :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
      S T hST
  let μT :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
      T
  have hiS : MeasurableEmbedding iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S
  have hiT : MeasurableEmbedding iT :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      T
  have hj : MeasurableEmbedding j :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_measurableEmbedding
      S T hST
  have hfun : iS = iT ∘ j := by
    funext a
    rfl
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
  change (Measure.map iT μT).comap iS = _
  calc
    (Measure.map iT μT).comap iS =
        (Measure.map iT μT).comap (iT ∘ j) := by rw [hfun]
    _ = ((Measure.map iT μT).comap iT).comap j := by
      rw [Measure.comap_comap
        hj.measurableSet_image'
        hiT.injective
        hiT.measurableSet_image']
    _ = μT.comap j := by rw [hiT.comap_map]
    _ =
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S := by
      rw [
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_comap_transition
          S T hST]

/-- In the common full finite-adelic carrier, the larger coherent ambient
cylinder restricts exactly to the smaller coherent ambient cylinder. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_restrict_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        T).restrict
        (Set.range
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
            S)) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S := by
  let iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
  have hiS : MeasurableEmbedding iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S
  calc
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        T).restrict (Set.range iS) =
        Measure.map iS
          ((V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
            T).comap iS) :=
      (hiS.map_comap _).symm
    _ = Measure.map iS
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S) := by
      rw [
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_comap_transition
          S T hST]
    _ =
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S :=
      rfl

end RationalQuadraticSpaceMatrix
