import SMSFormula.MeasureDirectedSup
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicGenuinePrincipalBlockMeasure

/-!
# General finite-adelic invariant-differential measure

The genuine finite-adelic principal blocks form a directed open cover.  Their
coherently normalized differential measures map to a monotone family of
ambient measures.  The pointwise directed supremum on measurable sets is
therefore a measure, and its comap to every genuine principal block is exactly
the block measure.

The resulting finite-adelic measure is left invariant.  The proof localizes a
given translating element and a given ambient block in their union block and
uses the verified blockwise left invariance.  No unrestricted-family topology,
reference Haar rescaling, or full-adelic measure is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

local instance finiteAdelicDifferentialMeasurePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicDifferentialMeasureDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteAdelicDifferentialMeasureGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance finiteAdelicDifferentialMeasureGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicDifferentialMeasureGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance finiteAdelicDifferentialMeasureLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicDifferentialMeasureLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance finiteAdelicDifferentialMeasureMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicDifferentialMeasureMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicDifferentialMeasureFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance finiteAdelicDifferentialMeasureFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance finiteAdelicDifferentialMeasureGenuineMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  borel _

local instance finiteAdelicDifferentialMeasureGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  ⟨rfl⟩

/-! ## The directed genuine open cover -/

theorem finiteAdelicSpecialOrthogonalGenuinePrincipalBlock_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S :
      Set V.FiniteAdelicSpecialOrthogonalGroup) ⊆
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup T := by
  intro a ha
  change
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv a ∈
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock T
  exact
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock_mono hST ha

theorem exists_mem_finiteAdelicSpecialOrthogonalGenuinePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      a ∈ V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S := by
  obtain ⟨S, hS⟩ :=
    V.exists_mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
      (V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv a)
  exact ⟨S, hS⟩

theorem iUnion_finiteAdelicSpecialOrthogonalGenuinePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n) :
    (⋃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S :
        Set V.FiniteAdelicSpecialOrthogonalGroup)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨S, hS⟩ := V.exists_mem_finiteAdelicSpecialOrthogonalGenuinePrincipalBlock a
  exact Set.mem_iUnion.2 ⟨S, hS⟩

def finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure V.FiniteAdelicSpecialOrthogonalGroup :=
  Measure.map
    (fun a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S => a.1)
    (V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S)

theorem finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (fun a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S =>
        a.1) := by
  let f :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  have hf : Topology.IsEmbedding f :=
    (V.isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S
      |>.isOpenEmbedding_subtypeVal).isEmbedding
  apply hf.measurableEmbedding
  simpa [f] using
    (V.isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup
      S).measurableSet

theorem finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_apply_image
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Set (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S)) :
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure S
        ((fun a :
          V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S => a.1) '' s) =
      V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S
        s := by
  unfold finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
  rw [(V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding S).map_apply]
  rw [Set.preimage_image_eq _ (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding S).injective]

theorem finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure S ≤ V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure T := by
  let i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
      S T hST
  let valS :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  let valT :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock T →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  let μS :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S
  let μT :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure T
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_measurableEmbedding
      S T hST
  have hcompat : μT.comap i = μS :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_comap
      S T hST
  have hmap : Measure.map i μS = μT.restrict (Set.range i) := by
    rw [← hcompat, hi.map_comap]
  unfold finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
  change Measure.map valS μS ≤ Measure.map valT μT
  calc
    Measure.map valS μS =
        Measure.map valT (Measure.map i μS) := by
          rw [Measure.map_map
            continuous_subtype_val.measurable hi.measurable]
          rfl
    _ = Measure.map valT (μT.restrict (Set.range i)) := by rw [hmap]
    _ ≤ Measure.map valT μT := by
      exact
        Measure.map_mono Measure.restrict_le_self
          continuous_subtype_val.measurable

theorem finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_apply_image_of_subset
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T)
    (s : Set (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S)) :
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure T
        ((fun a :
          V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S => a.1) '' s) =
      V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S
        s := by
  let i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
      S T hST
  let μS :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S
  let μT :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure T
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_measurableEmbedding
      S T hST
  have hcompat : μT.comap i = μS :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_comap
      S T hST
  have hset :
      (fun a :
          V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S => a.1) '' s =
        (fun a :
          V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock T => a.1) ''
          (i '' s) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨i b, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨_b, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, rfl⟩
  rw [hset, V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_apply_image T]
  rw [← hi.comap_apply μT s, hcompat]

def finiteAdelicInvariantDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FiniteAdelicSpecialOrthogonalGroup :=
  Measure.directedSup V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
    (fun _ _ hST => V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_mono hST)

theorem finiteAdelicInvariantDifferentialGroupMeasure_comap_genuineBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicInvariantDifferentialGroupMeasure.comap
        (fun a :
          V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S => a.1) =
      V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S := by
  apply Measure.ext
  intro s hs
  let valS :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  have hval : MeasurableEmbedding valS :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubtypeVal_measurableEmbedding S
  rw [hval.comap_apply]
  unfold finiteAdelicInvariantDifferentialGroupMeasure
  rw [Measure.directedSup_apply _ _
    (hval.measurableSet_image.mpr hs)]
  apply le_antisymm
  · apply iSup_le
    intro T
    let U := S ∪ T
    calc
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure T (valS '' s) ≤
          V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure U (valS '' s) :=
        V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_mono (Finset.subset_union_right) (valS '' s)
      _ =
          V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
            S s :=
        V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_apply_image_of_subset
          (Finset.subset_union_left) s
  · exact le_iSup_of_le S
      (le_of_eq (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_apply_image S s).symm)

private theorem finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_map_mul_left_le
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalGroup)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hg :
      g ∈ V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map (fun a => g * a) (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure T) ≤
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure (S ∪ T) := by
  let U := S ∪ T
  let i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusionHom
      T U Finset.subset_union_right
  let gU : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock U :=
    ⟨g, V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlock_mono Finset.subset_union_left hg⟩
  let μT :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure T
  let μU :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure U
  let valT :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock T →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  let valU :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock U →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => a.1
  let leftG :
      V.FiniteAdelicSpecialOrthogonalGroup →
        V.FiniteAdelicSpecialOrthogonalGroup :=
    fun a => g * a
  let leftGU :
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock U →
        V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock U :=
    fun a => gU * a
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockInclusion_measurableEmbedding
      T U Finset.subset_union_right
  have hcompat : μU.comap i = μT :=
    V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_comap
      T U Finset.subset_union_right
  have hmapi : Measure.map i μT ≤ μU := by
    rw [← hcompat, hi.map_comap]
    exact Measure.restrict_le_self
  have hleftG : Measurable leftG :=
    measurable_const_mul g
  have hleftGU : Measurable leftGU :=
    measurable_const_mul gU
  unfold finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
  change Measure.map leftG (Measure.map valT μT) ≤
    Measure.map valU μU
  calc
    Measure.map leftG (Measure.map valT μT) =
        Measure.map valU (Measure.map leftGU (Measure.map i μT)) := by
      rw [
        Measure.map_map hleftG continuous_subtype_val.measurable,
        Measure.map_map hleftGU hi.measurable,
        Measure.map_map continuous_subtype_val.measurable
          (hleftGU.comp hi.measurable)]
      apply congrArg (fun f => Measure.map f μT)
      funext a
      rfl
    _ ≤ Measure.map valU (Measure.map leftGU μU) := by
      exact Measure.map_mono
        (Measure.map_mono hmapi hleftGU)
        continuous_subtype_val.measurable
    _ = Measure.map valU μU := by
      rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self gU]

theorem finiteAdelicInvariantDifferentialGroupMeasure_map_mul_left_le
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicSpecialOrthogonalGroup) :
    Measure.map (fun a => g * a) V.finiteAdelicInvariantDifferentialGroupMeasure ≤ V.finiteAdelicInvariantDifferentialGroupMeasure := by
  obtain ⟨S, hg⟩ := V.exists_mem_finiteAdelicSpecialOrthogonalGenuinePrincipalBlock g
  apply Measure.le_iff.2
  intro A hA
  have hleft : Measurable (fun a :
      V.FiniteAdelicSpecialOrthogonalGroup => g * a) :=
    measurable_const_mul g
  rw [Measure.map_apply hleft hA]
  unfold finiteAdelicInvariantDifferentialGroupMeasure
  rw [
    Measure.directedSup_apply _ _ (hleft hA),
    Measure.directedSup_apply _ _ hA]
  apply iSup_le
  intro T
  calc
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure T ((fun a => g * a) ⁻¹' A) =
        Measure.map (fun a => g * a) (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure T) A := by
      rw [Measure.map_apply hleft hA]
    _ ≤ V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure (S ∪ T) A :=
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_map_mul_left_le g S hg T A
    _ ≤ ⨆ U, V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure U A :=
      le_iSup (fun U => V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure U A) (S ∪ T)

instance finiteAdelicInvariantDifferentialGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulLeftInvariant V.finiteAdelicInvariantDifferentialGroupMeasure := by
  constructor
  intro g
  apply le_antisymm
  · exact V.finiteAdelicInvariantDifferentialGroupMeasure_map_mul_left_le g
  · let leftG :
        V.FiniteAdelicSpecialOrthogonalGroup →
          V.FiniteAdelicSpecialOrthogonalGroup :=
      fun a => g * a
    let leftGInv :
        V.FiniteAdelicSpecialOrthogonalGroup →
          V.FiniteAdelicSpecialOrthogonalGroup :=
      fun a => g⁻¹ * a
    have hleftG : Measurable leftG :=
      measurable_const_mul g
    have hleftGInv : Measurable leftGInv :=
      measurable_const_mul g⁻¹
    calc
      V.finiteAdelicInvariantDifferentialGroupMeasure =
          Measure.map leftG (Measure.map leftGInv V.finiteAdelicInvariantDifferentialGroupMeasure) := by
        rw [Measure.map_map hleftG hleftGInv]
        have hfun : leftG ∘ leftGInv = id := by
          funext a
          simp [leftG, leftGInv]
        rw [hfun, Measure.map_id]
      _ ≤ Measure.map leftG V.finiteAdelicInvariantDifferentialGroupMeasure :=
        Measure.map_mono
          (V.finiteAdelicInvariantDifferentialGroupMeasure_map_mul_left_le g⁻¹) hleftG

end RationalQuadraticSpaceMatrix
