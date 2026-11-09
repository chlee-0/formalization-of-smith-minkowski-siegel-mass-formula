import SMSFormula.RationalIdeleDifferentialGenuinePrincipalBlockTopology

/-!
# Coherent differential measures on genuine finite-idele blocks

Transport the exact exceptional/tail source measure through the fixed-block
homeomorphism to the literal block inside `RationalFiniteAdeleˣ`.  Conjugating
the already certified source transition gives a measurable embedding between
genuine blocks, and the transported measures comap exactly.

No ambient measure, directed supremum, or equality with compact-normalized
finite-idele Haar is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 400000

local instance rationalIdeleGenuineMeasurePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleGenuineMeasureLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleGenuineMeasureLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleGenuineMeasureLocalSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := by
  letI : SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ×
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ᵐᵒᵖ) :=
    inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance rationalIdeleGenuineMeasureIntegralSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rationalIdeleGenuineMeasureIntegralBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  Subtype.borelSpace _

local instance rationalIdeleGenuineMeasureExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialExceptionalProduct S) :=
  Pi.borelSpace

local instance rationalIdeleGenuineMeasureTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialIntegralTail S) :=
  Pi.borelSpace

local instance rationalIdeleGenuineMeasureFiniteMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel _

local instance rationalIdeleGenuineMeasureFiniteBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

local instance rationalIdeleGenuineMeasureBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The exact differential source cylinder transported to its literal genuine
finite-idele principal block. -/
noncomputable def rationalIdeleDifferentialGenuinePrincipalBlockMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Measure.map
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S)
    (rationalIdeleDifferentialExceptionalTailSourceMeasure S)

/-- Extracting local coordinates maps the genuine block measure back to the
literal exceptional/tail source. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockMeasure_map_extract
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
          S).symm
        (rationalIdeleDifferentialGenuinePrincipalBlockMeasure S) =
      rationalIdeleDifferentialExceptionalTailSourceMeasure S := by
  unfold rationalIdeleDifferentialGenuinePrincipalBlockMeasure
  exact MeasurableEquiv.map_symm_map
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S
      |>.toMeasurableEquiv)

/-- The transported block measure is equivalently the source measure comapped
along coordinate extraction. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockMeasure_eq_comap
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalIdeleDifferentialGenuinePrincipalBlockMeasure S =
      (rationalIdeleDifferentialExceptionalTailSourceMeasure S).comap
        (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
          S).symm := by
  let e :=
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S
  let mu := rationalIdeleDifferentialExceptionalTailSourceMeasure S
  change Measure.map e mu = mu.comap e.symm
  calc
    Measure.map e mu =
        (Measure.map e.symm (Measure.map e mu)).comap e.symm := by
      rw [e.symm.measurableEmbedding.comap_map]
    _ = mu.comap e.symm := by
      exact congrArg (fun nu : Measure _ ↦ nu.comap e.symm)
        (MeasurableEquiv.map_symm_map e.toMeasurableEquiv)

/-! ## Genuine block transitions -/

/-- The genuine block transition obtained by conjugating the exact source
transition through fixed-block homeomorphisms. -/
def rationalIdeleDifferentialGenuinePrincipalBlockTransition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    RationalIdeleDifferentialGenuinePrincipalBlock S →
      RationalIdeleDifferentialGenuinePrincipalBlock T :=
  rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph T ∘
    rationalIdeleDifferentialExceptionalTailTransition S T hST ∘
      (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
        S).symm

theorem rationalIdeleDifferentialGenuinePrincipalBlockTransition_measurableEmbedding
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST) :=
  (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph T
    |>.measurableEmbedding).comp
    ((rationalIdeleDifferentialExceptionalTailTransition_measurableEmbedding
      S T hST).comp
      (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
        S |>.symm.measurableEmbedding))

/-- Genuine differential block measures comap literally along every finite
exceptional-set transition. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockMeasure_comap_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (rationalIdeleDifferentialGenuinePrincipalBlockMeasure T).comap
        (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST) =
      rationalIdeleDifferentialGenuinePrincipalBlockMeasure S := by
  let eS :=
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S
  let eT :=
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph T
  let j := rationalIdeleDifferentialExceptionalTailTransition S T hST
  let i := rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST
  let muS := rationalIdeleDifferentialExceptionalTailSourceMeasure S
  let muT := rationalIdeleDifferentialExceptionalTailSourceMeasure T
  have hi : MeasurableEmbedding i :=
    rationalIdeleDifferentialGenuinePrincipalBlockTransition_measurableEmbedding
      S T hST
  have hj : MeasurableEmbedding j :=
    rationalIdeleDifferentialExceptionalTailTransition_measurableEmbedding
      S T hST
  have hfun : eT.symm ∘ i = j ∘ eS.symm := by
    funext x
    exact eT.symm_apply_apply _
  rw [rationalIdeleDifferentialGenuinePrincipalBlockMeasure_eq_comap T,
    rationalIdeleDifferentialGenuinePrincipalBlockMeasure_eq_comap S]
  change (muT.comap eT.symm).comap i = muS.comap eS.symm
  calc
    (muT.comap eT.symm).comap i = muT.comap (eT.symm ∘ i) := by
      rw [Measure.comap_comap hi.measurableSet_image' eT.symm.injective
        eT.symm.measurableEmbedding.measurableSet_image']
    _ = muT.comap (j ∘ eS.symm) := by rw [hfun]
    _ = (muT.comap j).comap eS.symm := by
      rw [Measure.comap_comap eS.symm.measurableEmbedding.measurableSet_image'
        hj.injective hj.measurableSet_image']
    _ = muS.comap eS.symm := by
      rw [rationalIdeleDifferentialExceptionalTailSourceMeasure_comap_transition
        S T hST]

end RationalQuadraticSpaceMatrix
