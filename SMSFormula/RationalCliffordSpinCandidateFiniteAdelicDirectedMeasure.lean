import SMSFormula.MeasureDirectedSup
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicGenuineBlockCoherence

/-!
# A directed finite-adelic measure for the Clifford--Spin candidate

The coherently scaled measures on genuine admissible principal blocks form a
compatible directed system.  This module pushes them to the full finite-
adelic carrier and takes their pointwise directed supremum on measurable sets.

The resulting measure comaps exactly to the coherent measure on every genuine
block and is globally left invariant.  It is also nonzero.  No empty-block
mass-one formula, local finiteness, regularity, analytic top-form
identification, or Tamagawa normalization is asserted.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000

local instance finiteAdelicSpinDirectedMeasureDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteAdelicSpinDirectedMeasureFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance finiteAdelicSpinDirectedMeasureFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance finiteAdelicSpinDirectedMeasureGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## The directed genuine open cover -/

/-- Enlarging the supplied exceptional set enlarges the genuine admissible
principal block. -/
theorem finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
        S : Set V.FiniteAdelicCliffordSpinCandidateGroup) ⊆
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
        T := by
  intro a ha
  change
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T)
  have ha' :
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a ∈
        V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
          (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :=
    ha
  exact
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock_mono
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST) ha'

/-- Every genuine finite-adelic Spin-candidate point belongs to an admissible
principal block. -/
theorem exists_mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.FiniteAdelicCliffordSpinCandidateGroup) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      a ∈
        V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
          S := by
  obtain ⟨S, hS⟩ :=
    V.exists_mem_finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
      (V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a)
  refine ⟨S, ?_⟩
  change
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv a ∈
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)
  exact
    V.finiteAdelicCliffordSpinCandidateRestrictedFamilyPrincipalBlock_mono
      (by
        intro v hv
        exact Finset.mem_union_left _ hv)
      hS

/-- The admissible genuine principal blocks cover the full finite-adelic
Spin-candidate carrier. -/
theorem iUnion_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n) :
    (⋃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
        S : Set V.FiniteAdelicCliffordSpinCandidateGroup)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨S, hS⟩ :=
    V.exists_mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
      a
  exact Set.mem_iUnion.2 ⟨S, hS⟩

/-! ## Monotone ambient cylinders -/

/-- Coherent supported ambient cylinders are monotone under enlargement of
the exceptional set. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S ≤
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        T := by
  rw [←
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_restrict_transition
      S T hST]
  exact Measure.restrict_le_self

/-- A coherent ambient cylinder evaluates on the image of a block set as the
coherent measure of that set. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_apply_image
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Set
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          S '' s) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S s := by
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
  rw [
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S).map_apply,
    Set.preimage_image_eq _
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
        S).injective]

/-- Every larger coherent ambient cylinder gives the same values on images
from a smaller genuine block. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_apply_image_of_subset
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T)
    (s : Set
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        T
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          S '' s) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S s := by
  let iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
  let μT :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
      T
  have hiS : MeasurableEmbedding iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S
  have hcompat :
      μT.comap iS =
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_comap_transition
      S T hST
  rw [← hiS.comap_apply μT s, hcompat]

/-! ## Directed finite-adelic measure and exact block recovery -/

/-- The full finite-adelic Spin measure obtained as the directed supremum of
the coherent supported ambient cylinders. -/
def finiteAdelicCliffordSpinCandidateCoherentGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FiniteAdelicCliffordSpinCandidateGroup :=
  Measure.directedSup
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
    (fun _ _ hST =>
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_mono
        hST)

/-- Comapping the directed measure to any genuine admissible block recovers
its coherent block measure exactly. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_comap_genuineBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.comap
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          S) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S := by
  apply Measure.ext
  intro s hs
  let iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
  have hiS : MeasurableEmbedding iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S
  rw [hiS.comap_apply]
  unfold finiteAdelicCliffordSpinCandidateCoherentGroupMeasure
  rw [Measure.directedSup_apply _ _ (hiS.measurableSet_image.mpr hs)]
  apply le_antisymm
  · apply iSup_le
    intro T
    let U := S ∪ T
    calc
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          T (iS '' s) ≤
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          U (iS '' s) :=
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_mono
          Finset.subset_union_right (iS '' s)
      _ =
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S s :=
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_apply_image_of_subset
          Finset.subset_union_left s
  · exact le_iSup_of_le S
      (le_of_eq
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_apply_image
          S s).symm)

/-- Restriction of the directed measure to the image of a genuine block is
the ambient pushforward of that block's coherent measure. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_restrict_genuineBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.restrict
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
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.restrict
        (Set.range iS) =
      Measure.map iS
        (V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.comap iS) :=
      (hiS.map_comap _).symm
    _ = Measure.map iS
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S) := by
      rw [V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_comap_genuineBlock]
    _ =
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S :=
      rfl

/-! ## Global left invariance -/

private theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_map_mul_left_le
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicCliffordSpinCandidateGroup)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hg :
      g ∈
        V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
          S)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map (fun a => g * a)
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          T) ≤
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        (S ∪ T) := by
  let U := S ∪ T
  let i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransitionHom
      T U Finset.subset_union_right
  let gU :
      V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock U :=
    ⟨g,
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock_mono
        Finset.subset_union_left hg⟩
  let μT :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
      T
  let μU :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
      U
  let valT :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      T
  let valU :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      U
  let leftG :
      V.FiniteAdelicCliffordSpinCandidateGroup →
        V.FiniteAdelicCliffordSpinCandidateGroup :=
    fun a => g * a
  let leftGU :
      V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock U →
        V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock U :=
    fun a => gU * a
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockTransition_measurableEmbedding
      T U Finset.subset_union_right
  have hmapi : Measure.map i μT ≤ μU := by
    rw [
      V.map_finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_transition
        T U Finset.subset_union_right]
    exact Measure.restrict_le_self
  have hleftG : Measurable leftG :=
    measurable_const_mul g
  have hleftGU : Measurable leftGU :=
    measurable_const_mul gU
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
  change Measure.map leftG (Measure.map valT μT) ≤
    Measure.map valU μU
  calc
    Measure.map leftG (Measure.map valT μT) =
        Measure.map valU (Measure.map leftGU (Measure.map i μT)) := by
      rw [
        Measure.map_map hleftG
          (V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
            T).measurable,
        Measure.map_map hleftGU hi.measurable,
        Measure.map_map
          (V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
            U).measurable
          (hleftGU.comp hi.measurable)]
      apply congrArg (fun f => Measure.map f μT)
      funext a
      rfl
    _ ≤ Measure.map valU (Measure.map leftGU μU) := by
      exact Measure.map_mono
        (Measure.map_mono hmapi hleftGU)
        (V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          U).measurable
    _ = Measure.map valU μU := by
      rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self gU]

/-- Left translation sends the directed measure below itself. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_map_mul_left_le
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicCliffordSpinCandidateGroup) :
    Measure.map (fun a => g * a)
        V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure ≤
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  obtain ⟨S, hg⟩ :=
    V.exists_mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
      g
  apply Measure.le_iff.2
  intro A hA
  have hleft : Measurable
      (fun a : V.FiniteAdelicCliffordSpinCandidateGroup => g * a) :=
    measurable_const_mul g
  rw [Measure.map_apply hleft hA]
  unfold finiteAdelicCliffordSpinCandidateCoherentGroupMeasure
  rw [
    Measure.directedSup_apply _ _ (hleft hA),
    Measure.directedSup_apply _ _ hA]
  apply iSup_le
  intro T
  calc
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        T ((fun a => g * a) ⁻¹' A) =
      Measure.map (fun a => g * a)
        (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          T) A := by
      rw [Measure.map_apply hleft hA]
    _ ≤
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        (S ∪ T) A :=
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_map_mul_left_le
        g S hg T A
    _ ≤
      ⨆ U,
        V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          U A :=
      le_iSup
        (fun U =>
          V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
            U A)
        (S ∪ T)

/-- The directed finite-adelic Spin measure is globally left invariant. -/
instance finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulLeftInvariant
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  constructor
  intro g
  apply le_antisymm
  · exact
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_map_mul_left_le g
  · let leftG :
        V.FiniteAdelicCliffordSpinCandidateGroup →
          V.FiniteAdelicCliffordSpinCandidateGroup :=
      fun a => g * a
    let leftGInv :
        V.FiniteAdelicCliffordSpinCandidateGroup →
          V.FiniteAdelicCliffordSpinCandidateGroup :=
      fun a => g⁻¹ * a
    have hleftG : Measurable leftG :=
      measurable_const_mul g
    have hleftGInv : Measurable leftGInv :=
      measurable_const_mul g⁻¹
    calc
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure =
          Measure.map leftG
            (Measure.map leftGInv
              V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure) := by
        rw [Measure.map_map hleftG hleftGInv]
        have hfun : leftG ∘ leftGInv = id := by
          funext a
          simp [leftG, leftGInv]
        rw [hfun, Measure.map_id]
      _ ≤ Measure.map leftG
          V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
        Measure.map_mono
          (V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_map_mul_left_le
            g⁻¹)
          hleftG

/-! ## Nontriviality without a mass-one normalization -/

/-- Every coherent genuine block measure is nonzero. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S ≠ 0 := by
  intro hzero
  have huniv :
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          S Set.univ ≠ 0 := by
    rw [
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_weight_smul,
      Measure.smul_apply,
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure_univ]
    apply mul_ne_zero
    · exact
        V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero S
    · exact Finset.prod_ne_zero_iff.mpr fun v _ => by
        letI : Measure.IsHaarMeasure
            (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1) :=
          V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure
            v.1
        exact isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  rw [hzero] at huniv
  exact huniv rfl

/-- The directed finite-adelic Spin measure is nonzero, although its baseline
block mass is not evaluated. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure ≠ 0 := by
  intro hzero
  have hblock :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_comap_genuineBlock
      ∅
  rw [hzero] at hblock
  have hz :
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
          ∅ = 0 := by
    simpa using hblock.symm
  exact
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_ne_zero
      ∅ hz

end RationalQuadraticSpaceMatrix
