import SMSFormula.RationalCliffordGeneralSpinHorizontalGenuinePrincipalBlockTopology

/-!
# Coherent horizontal measures on genuine finite-adelic GSpin blocks

The fixed-block homeomorphism permits genuine measure transport from the
coherent restricted-family cylinders to genuine intrinsic finite-adelic
`GSpin` blocks.  Transitions are conjugated through those homeomorphisms, so
the transported measures comap literally.

No ambient finite-adelic measure, directed supremum, real factor, or quotient
disintegration is constructed here.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalGenuineMeasureFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalGenuineMeasureFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalGenuineMeasureBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The coherent restricted-family cylinder transported to the genuine
intrinsic finite-adelic `GSpin` block. -/
def cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph
      S).symm
    (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S)

/-- Simultaneous local evaluation maps the genuine measure back to the
literal coherent restricted-family cylinder. -/
theorem cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_map
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S)
        (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S) =
      V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S := by
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure
  exact MeasurableEquiv.map_map_symm
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
      |>.toMeasurableEquiv)

/-- Equivalently, the genuine measure is the comap of the coherent
restricted-family cylinder along local evaluation. -/
theorem
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_eq_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S =
      (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S).comap
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph
          S) := by
  let e :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
  let μ :=
    V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S
  change Measure.map e.symm μ = μ.comap e
  calc
    Measure.map e.symm μ =
        (Measure.map e (Measure.map e.symm μ)).comap e := by
      rw [e.measurableEmbedding.comap_map]
    _ = μ.comap e := by
      exact congrArg (fun ν : Measure _ ↦ ν.comap e)
        (MeasurableEquiv.map_map_symm e.toMeasurableEquiv)

/-! ## Genuine block transitions -/

/-- The genuine `S`-to-`T` transition obtained by conjugating the
restricted-family transition through the fixed-block homeomorphisms. -/
def cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S →
      V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock T :=
  (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph T).symm ∘
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST ∘
      V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S

theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST) :=
  (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph T
    |>.symm.measurableEmbedding).comp
    ((V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition_measurableEmbedding
      S T hST).comp
      (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
        |>.measurableEmbedding))

/-- The transported genuine measures comap exactly along every genuine block
transition. -/
theorem
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure T).comap
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST) =
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S := by
  let eS :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
  let eT :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph T
  let j :=
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST
  let i :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST
  let μS :=
    V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S
  let μT :=
    V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure T
  have hi : MeasurableEmbedding i :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_measurableEmbedding
      S T hST
  have hj : MeasurableEmbedding j :=
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition_measurableEmbedding
      S T hST
  have hfun : eT ∘ i = j ∘ eS := by
    funext x
    exact eT.apply_symm_apply _
  rw [
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_eq_comap T,
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_eq_comap S]
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
      rw [V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure_comap
        S T hST]

end RationalQuadraticSpaceMatrix
