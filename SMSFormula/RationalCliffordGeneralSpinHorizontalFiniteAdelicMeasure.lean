import SMSFormula.MeasureDirectedSup
import SMSFormula.RationalCliffordGeneralSpinHorizontalGenuinePrincipalBlockOpen

/-!
# Directed horizontal measure on finite-adelic GSpin

The literal-inclusion theorem permits each coherent genuine block cylinder to
be pushed into the common intrinsic finite-adelic `GSpin` carrier.  These
ambient cylinders are monotone under enlargement of the exceptional set, so
their directed supremum is a genuine measure on that carrier.

The directed measure recovers every block measure exactly by comap and
restriction.  Global Haar invariance, the real factor, and identification of
the common quotient scale are handled downstream.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalFiniteAdelicMeasureDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalFiniteAdelicMeasureFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFiniteAdelicMeasureFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalFiniteAdelicMeasureBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- Inclusion of a genuine horizontal block into the common intrinsic
finite-adelic `GSpin` carrier. -/
def cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S →
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  fun x ↦ x.1

theorem continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) :=
  continuous_subtype_val

/-- Ambient inclusion of every genuine horizontal principal block is a
measurable embedding. -/
theorem
    cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) :=
  (V.isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock S)
    |>.isOpenEmbedding_subtypeVal.measurableEmbedding

/-- The block transition followed by ambient inclusion is literally the
smaller ambient inclusion. -/
@[simp]
theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_comp_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (x : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion T
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition
          S T hST x) =
      V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S x :=
  V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_val S T hST x

/-- Pushing the smaller block measure through the literal transition gives
the restriction of the larger block measure to the transition range. -/
theorem map_cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST)
        (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S) =
      (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure T).restrict
        (Set.range
          (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition
            S T hST)) := by
  let j := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST
  have hj : MeasurableEmbedding j :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_measurableEmbedding
      S T hST
  rw [←
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_comap_transition
      S T hST]
  exact hj.map_comap _

/-- A coherent genuine block cylinder pushed into the common finite-adelic
carrier. -/
def cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure V.FiniteAdelicCliffordGeneralSpinGroup :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S)
    (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S)

/-- The supported ambient cylinders are monotone under enlargement of the
exceptional set. -/
theorem cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S ≤
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T := by
  let iS := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  let iT := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion T
  let j := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST
  let μS := V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S
  let μT := V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure T
  have hiT : Measurable iT :=
    (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
      T).measurable
  have hj : Measurable j :=
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_measurableEmbedding
      S T hST).measurable
  have hcomp : iT ∘ j = iS := by
    funext x
    exact V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_comp_transition
      S T hST x
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
  change Measure.map iS μS ≤ Measure.map iT μT
  calc
    Measure.map iS μS = Measure.map (iT ∘ j) μS := by rw [hcomp]
    _ = Measure.map iT (Measure.map j μS) := by
      rw [Measure.map_map hiT hj]
    _ ≤ Measure.map iT μT := by
      apply Measure.map_mono _ hiT
      rw [V.map_cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_transition
        S T hST]
      exact Measure.restrict_le_self

/-- The horizontal finite-adelic measure obtained as the directed supremum of
the coherent supported block cylinders. -/
def finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FiniteAdelicCliffordGeneralSpinGroup :=
  Measure.directedSup
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
    (fun _ _ hST ↦
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_mono
        hST)

/-- On measurable sets the horizontal group measure is the literal supremum
of its finite-exceptional ambient cylinders. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_apply
    (V : RationalQuadraticSpaceMatrix n)
    {s : Set V.FiniteAdelicCliffordGeneralSpinGroup}
    (hs : MeasurableSet s) :
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure s =
      ⨆ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
        V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S s :=
  Measure.directedSup_apply _ _ hs

/-! ## Exact recovery on every genuine block -/

/-- An ambient block cylinder evaluates on the image of a block set as the
original coherent block measure. -/
theorem
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_apply_image
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Set (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S)) :
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S '' s) =
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S s := by
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
  rw [
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S).map_apply,
    Set.preimage_image_eq _
      (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
        S).injective]

/-- Every larger ambient cylinder gives the same value on an image from a
smaller genuine block. -/
theorem
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_apply_image_of_subset
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T)
    (s : Set (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S)) :
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S '' s) =
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S s := by
  let iS := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  let μT :=
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T
  have hiS : MeasurableEmbedding iS :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S
  have hcompat :
      μT.comap iS =
        V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S := by
    let iT := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion T
    let j := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST
    have hiT : MeasurableEmbedding iT :=
      V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
        T
    have hj : MeasurableEmbedding j :=
      V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_measurableEmbedding
        S T hST
    have hcomp : iT ∘ j = iS := by
      funext x
      exact
        V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_comp_transition
          S T hST x
    unfold μT cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
    change (Measure.map iT
      (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure T)).comap iS = _
    rw [← hcomp,
      ← Measure.comap_comap
        hj.measurableSet_image' hiT.injective hiT.measurableSet_image',
      hiT.comap_map,
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_comap_transition]
  rw [← hiS.comap_apply μT s, hcompat]

/-- Comapping the directed finite-adelic horizontal measure to any genuine
principal block recovers its coherent block measure exactly. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_comap_genuineBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.comap
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) =
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S := by
  apply Measure.ext
  intro s hs
  let iS := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  have hiS : MeasurableEmbedding iS :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S
  rw [hiS.comap_apply]
  unfold finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  rw [Measure.directedSup_apply _ _ (hiS.measurableSet_image.mpr hs)]
  apply le_antisymm
  · apply iSup_le
    intro T
    let U := S ∪ T
    calc
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T
          (iS '' s) ≤
        V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure U
          (iS '' s) :=
        V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_mono
          Finset.subset_union_right (iS '' s)
      _ = V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S s :=
        V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_apply_image_of_subset
          Finset.subset_union_left s
  · exact le_iSup_of_le S
      (le_of_eq
        (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_apply_image
          S s).symm)

/-- Restricting the directed measure to a genuine block image recovers the
ambient pushforward of that block's coherent measure. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_genuineBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (Set.range
          (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S)) =
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S := by
  let iS := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  have hiS : MeasurableEmbedding iS :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S
  calc
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (Set.range iS) =
      Measure.map iS
        (V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.comap iS) :=
      (hiS.map_comap _).symm
    _ = Measure.map iS
        (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S) := by
      rw [V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_comap_genuineBlock]
    _ = V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S :=
      rfl

end RationalQuadraticSpaceMatrix
