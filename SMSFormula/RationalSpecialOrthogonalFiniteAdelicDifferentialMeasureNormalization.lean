import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasure

/-!
# Normalization of the finite-adelic differential measure

The coherent empty principal block has total mass one.  Its image is an open
neighborhood of the identity in the genuine finite-adelic special-orthogonal
group, and the global measure gives this image literal mass one.  Left
invariance therefore supplies a finite-measure open neighborhood at every
point.  This proves nontriviality and local finiteness directly; the genuine
second-countable Borel topology then supplies sigma-finiteness.  Regularity is
left to a separate direct local-compactness argument for the general carrier.

No real factor, reference Haar measure, or unrestricted local-family topology
is used.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000

local instance finiteAdelicDifferentialNormalizationFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance finiteAdelicDifferentialNormalizationFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-- The genuine finite-adelic special-orthogonal matrix group is second
countable. -/
noncomputable instance finiteAdelicSpecialOrthogonalGroupSecondCountableTopology
    (V : RationalQuadraticSpaceMatrix n) :
    SecondCountableTopology V.FiniteAdelicSpecialOrthogonalGroup := by
  letI : SecondCountableTopology (Fin n → RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele ×
        (Matrix (Fin n) (Fin n) RationalFiniteAdele)ᵐᵒᵖ) :=
    inferInstance
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology V.finiteAdelicOrthogonalMatrixSubgroup :=
    TopologicalSpace.secondCountableTopology_induced
      V.finiteAdelicOrthogonalMatrixSubgroup
      (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ
      ((↑) : V.finiteAdelicOrthogonalMatrixSubgroup →
        (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ)
  exact TopologicalSpace.secondCountableTopology_induced
    V.FiniteAdelicSpecialOrthogonalGroup
    V.finiteAdelicOrthogonalMatrixSubgroup
    ((↑) : V.FiniteAdelicSpecialOrthogonalGroup →
      V.finiteAdelicOrthogonalMatrixSubgroup)

local instance finiteAdelicDifferentialNormalizationGenuineMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  borel _

local instance finiteAdelicDifferentialNormalizationGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  ⟨rfl⟩

/-! ## Literal mass of the normalized empty block -/

/-- The global finite-adelic differential measure gives the literal genuine
empty principal block mass one. -/
@[simp]
theorem finiteAdelicInvariantDifferentialGroupMeasure_emptyBlock
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicInvariantDifferentialGroupMeasure
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅ :
          Set V.FiniteAdelicSpecialOrthogonalGroup) = 1 := by
  let val :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock ∅ →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  have hval : MeasurableEmbedding val :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding
      ∅
  have hcomap :=
    V.finiteAdelicInvariantDifferentialGroupMeasure_comap_genuineBlock ∅
  have h := congrArg
    (fun μ : Measure
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock ∅) =>
        μ Set.univ) hcomap
  change
    (Measure.comap val V.finiteAdelicInvariantDifferentialGroupMeasure)
        Set.univ =
      V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
        ∅ Set.univ at h
  rw [hval.comap_apply] at h
  have himage :
      val '' Set.univ =
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅ :
          Set V.FiniteAdelicSpecialOrthogonalGroup) := by
    ext a
    simp only [val, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [himage,
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_empty_univ]
    at h
  exact h

/-- The general finite-adelic invariant-differential measure is nonzero. -/
theorem finiteAdelicInvariantDifferentialGroupMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicInvariantDifferentialGroupMeasure ≠ 0 := by
  intro hzero
  have hmass := V.finiteAdelicInvariantDifferentialGroupMeasure_emptyBlock
  rw [hzero] at hmass
  simp at hmass

/-! ## Local finiteness and sigma-finiteness -/

/-- Translates of the normalized open empty block give a finite-measure
neighborhood of every finite-adelic point. -/
instance finiteAdelicInvariantDifferentialGroupMeasure_isLocallyFinite
    (V : RationalQuadraticSpaceMatrix n) :
    IsLocallyFiniteMeasure
      V.finiteAdelicInvariantDifferentialGroupMeasure := by
  constructor
  intro g
  let K : Set V.FiniteAdelicSpecialOrthogonalGroup :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅
  let L : V.FiniteAdelicSpecialOrthogonalGroup ≃ₜ
      V.FiniteAdelicSpecialOrthogonalGroup :=
    Homeomorph.mulLeft g
  let U : Set V.FiniteAdelicSpecialOrthogonalGroup :=
    (fun a => g * a) '' K
  have hKopen : IsOpen K :=
    V.isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅
  have hUopen : IsOpen U := by
    change IsOpen (L '' K)
    exact L.isOpen_image.mpr hKopen
  have hg : g ∈ U := by
    refine ⟨1, ?_, ?_⟩
    · exact Subgroup.one_mem _
    · simp
  refine ⟨U, hUopen.mem_nhds hg, ?_⟩
  calc
    V.finiteAdelicInvariantDifferentialGroupMeasure U =
        Measure.map (fun a => g * a)
          V.finiteAdelicInvariantDifferentialGroupMeasure U := by
      rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self g]
    _ = V.finiteAdelicInvariantDifferentialGroupMeasure K := by
      rw [(measurableEmbedding_mulLeft g).map_apply]
      change
        V.finiteAdelicInvariantDifferentialGroupMeasure
            ((fun a => g * a) ⁻¹' ((fun a => g * a) '' K)) =
          V.finiteAdelicInvariantDifferentialGroupMeasure K
      rw [Set.preimage_image_eq _ (measurableEmbedding_mulLeft g).injective]
    _ = 1 := V.finiteAdelicInvariantDifferentialGroupMeasure_emptyBlock
    _ < ∞ := ENNReal.one_lt_top

/-- The general finite-adelic differential measure is sigma-finite.  This is
the second-countable consequence of the explicit local-finiteness proof. -/
instance finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure := by
  exact sigmaFinite_of_locallyFinite

end RationalQuadraticSpaceMatrix
