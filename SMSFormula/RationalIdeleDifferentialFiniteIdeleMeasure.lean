import SMSFormula.MeasureDirectedSup
import SMSFormula.RationalIdeleDifferentialGenuinePrincipalBlockOpen

/-!
# Directed differential measure on rational finite ideles

Push every coherent genuine principal-block cylinder into the common finite-
idele carrier.  Literal unchanged-point transitions make the ambient cylinders
monotone, so their directed supremum is a genuine measure.  It recovers every
block measure exactly by comap and restriction.

Identification with compact-normalized finite-idele Haar is downstream.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleFiniteMeasureDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleFiniteMeasureAmbientMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel _

local instance rationalIdeleFiniteMeasureAmbientBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

local instance rationalIdeleFiniteMeasureBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- Inclusion of a genuine differential block into the common finite-idele
carrier. -/
def rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialGenuinePrincipalBlock S → RationalFiniteAdeleˣ :=
  fun x ↦ x.1

theorem continuous_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S) :=
  continuous_subtype_val

/-- Ambient inclusion of a genuine differential block is a measurable
embedding. -/
theorem
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S) :=
  (isOpen_isRationalIdeleDifferentialGenuinePrincipalBlock S)
    |>.isOpenEmbedding_subtypeVal.measurableEmbedding

/-- A block transition followed by ambient inclusion is the smaller ambient
inclusion literally. -/
@[simp]
theorem rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_comp_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (x : RationalIdeleDifferentialGenuinePrincipalBlock S) :
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion T
        (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST x) =
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S x :=
  rationalIdeleDifferentialGenuinePrincipalBlockTransition_val S T hST x

/-- Mapping a smaller block measure through its transition gives the larger
block measure restricted to the transition range. -/
theorem map_rationalIdeleDifferentialGenuinePrincipalBlockMeasure_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST)
        (rationalIdeleDifferentialGenuinePrincipalBlockMeasure S) =
      (rationalIdeleDifferentialGenuinePrincipalBlockMeasure T).restrict
        (Set.range
          (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST)) := by
  let j := rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST
  have hj : MeasurableEmbedding j :=
    rationalIdeleDifferentialGenuinePrincipalBlockTransition_measurableEmbedding
      S T hST
  rw [←
    rationalIdeleDifferentialGenuinePrincipalBlockMeasure_comap_transition
      S T hST]
  exact hj.map_comap _

/-- A coherent genuine block cylinder pushed into the common finite-idele
carrier. -/
def rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure RationalFiniteAdeleˣ :=
  Measure.map
    (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S)
    (rationalIdeleDifferentialGenuinePrincipalBlockMeasure S)

/-- Ambient differential block cylinders are monotone under enlargement of
the exceptional set. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_mono
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure S ≤
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T := by
  let iS := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  let iT := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion T
  let j := rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST
  let muS := rationalIdeleDifferentialGenuinePrincipalBlockMeasure S
  let muT := rationalIdeleDifferentialGenuinePrincipalBlockMeasure T
  have hiT : Measurable iT :=
    (continuous_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
      T).measurable
  have hj : Measurable j :=
    (rationalIdeleDifferentialGenuinePrincipalBlockTransition_measurableEmbedding
      S T hST).measurable
  have hcomp : iT ∘ j = iS := by
    funext x
    exact
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_comp_transition
        S T hST x
  unfold rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
  change Measure.map iS muS ≤ Measure.map iT muT
  calc
    Measure.map iS muS = Measure.map (iT ∘ j) muS := by rw [hcomp]
    _ = Measure.map iT (Measure.map j muS) := by
      rw [Measure.map_map hiT hj]
    _ ≤ Measure.map iT muT := by
      apply Measure.map_mono _ hiT
      rw [map_rationalIdeleDifferentialGenuinePrincipalBlockMeasure_transition
        S T hST]
      exact Measure.restrict_le_self

/-- The directed differential measure assembled from all finite-exceptional
principal blocks. -/
def rationalFiniteIdeleDifferentialDirectedMeasure :
    Measure RationalFiniteAdeleˣ :=
  Measure.directedSup
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
    (fun _ _ hST ↦
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_mono hST)

/-- On measurable sets the directed measure is the literal supremum of its
finite-exceptional ambient cylinders. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_apply
    {s : Set RationalFiniteAdeleˣ} (hs : MeasurableSet s) :
    rationalFiniteIdeleDifferentialDirectedMeasure s =
      ⨆ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
        rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure S s :=
  Measure.directedSup_apply _ _ hs

/-! ## Exact block recovery -/

/-- An ambient block cylinder evaluates on a block image as the original block
measure. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_apply_image
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Set (RationalIdeleDifferentialGenuinePrincipalBlock S)) :
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure S
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S '' s) =
      rationalIdeleDifferentialGenuinePrincipalBlockMeasure S s := by
  unfold rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
  rw [
    (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S).map_apply,
    Set.preimage_image_eq _
      (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
        S).injective]

/-- Every larger ambient cylinder has the same value on an image from a
smaller block. -/
theorem
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_apply_image_of_subset
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T)
    (s : Set (RationalIdeleDifferentialGenuinePrincipalBlock S)) :
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S '' s) =
      rationalIdeleDifferentialGenuinePrincipalBlockMeasure S s := by
  let iS := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  let muT := rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T
  have hiS : MeasurableEmbedding iS :=
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S
  have hcompat :
      muT.comap iS = rationalIdeleDifferentialGenuinePrincipalBlockMeasure S := by
    let iT := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion T
    let j := rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST
    have hiT : MeasurableEmbedding iT :=
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
        T
    have hj : MeasurableEmbedding j :=
      rationalIdeleDifferentialGenuinePrincipalBlockTransition_measurableEmbedding
        S T hST
    have hcomp : iT ∘ j = iS := by
      funext x
      exact
        rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_comp_transition
          S T hST x
    unfold muT rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
    change (Measure.map iT
      (rationalIdeleDifferentialGenuinePrincipalBlockMeasure T)).comap iS = _
    rw [← hcomp,
      ← Measure.comap_comap
        hj.measurableSet_image' hiT.injective hiT.measurableSet_image',
      hiT.comap_map,
      rationalIdeleDifferentialGenuinePrincipalBlockMeasure_comap_transition]
  rw [← hiS.comap_apply muT s, hcompat]

/-- Comapping the directed finite-idele measure to any principal block recovers
its coherent block measure exactly. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_comap_genuineBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalFiniteIdeleDifferentialDirectedMeasure.comap
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S) =
      rationalIdeleDifferentialGenuinePrincipalBlockMeasure S := by
  apply Measure.ext
  intro s hs
  let iS := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  have hiS : MeasurableEmbedding iS :=
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S
  rw [hiS.comap_apply]
  unfold rationalFiniteIdeleDifferentialDirectedMeasure
  rw [Measure.directedSup_apply _ _ (hiS.measurableSet_image.mpr hs)]
  apply le_antisymm
  · apply iSup_le
    intro T
    let U := S ∪ T
    calc
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T (iS '' s) ≤
        rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure U (iS '' s) :=
        rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_mono
          Finset.subset_union_right (iS '' s)
      _ = rationalIdeleDifferentialGenuinePrincipalBlockMeasure S s :=
        rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_apply_image_of_subset
          Finset.subset_union_left s
  · exact le_iSup_of_le S
      (le_of_eq
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_apply_image
          S s).symm)

/-- Restricting the directed measure to a block image recovers the ambient
pushforward of that block's coherent measure. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_restrict_genuineBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalFiniteIdeleDifferentialDirectedMeasure.restrict
        (Set.range
          (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S)) =
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure S := by
  let iS := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  have hiS : MeasurableEmbedding iS :=
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S
  calc
    rationalFiniteIdeleDifferentialDirectedMeasure.restrict (Set.range iS) =
      Measure.map iS
        (rationalFiniteIdeleDifferentialDirectedMeasure.comap iS) :=
      (hiS.map_comap _).symm
    _ = Measure.map iS
        (rationalIdeleDifferentialGenuinePrincipalBlockMeasure S) := by
      rw [rationalFiniteIdeleDifferentialDirectedMeasure_comap_genuineBlock]
    _ = rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure S :=
      rfl

end RationalQuadraticSpaceMatrix
