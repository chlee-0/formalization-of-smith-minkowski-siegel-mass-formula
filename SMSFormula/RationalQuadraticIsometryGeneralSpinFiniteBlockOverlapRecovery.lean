import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberTransportedSourceRecovery
import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteExceptionalOverlapRecovery

/-!
# Recovery of the block finite presentation overlap

The transported common-source product measures are converted back to the
literal native block p-adic carriers and assembled over a certified
presentation support.  After adjoining the normalized block integral tail,
the resulting measure is exactly the restriction of the repository's fixed
unweighted block exceptional/tail source measure.

This is still an unweighted statement.  It does not compare the coherent
principal-block weights or identify the finite presentation scalar.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance finiteBlockRecoveryDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteBlockRecoveryPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The certified support identifies the block exceptional index type with
the displayed finite support. -/
def blockFiniteExceptionalPlaceEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    {v // v ∈ S ∪
      (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces} ≃
      {v // v ∈ S} where
  toFun v :=
    ⟨v.1, (Finset.mem_union.mp v.2).elim (fun hv ↦ hv) (fun hv ↦ hS.1 hv)⟩
  invFun v := ⟨v.1, Finset.mem_union_left _ v.2⟩
  left_inv v := by
    cases v
    rfl
  right_inv v := by
    cases v
    rfl

/-- The literal native block exceptional-product carrier obtained by pulling
the common selected-chart source back through the presentation at every
exceptional place. -/
def blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set ((P.blockSpace hx).CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Set.pi Set.univ fun v ↦
    P.blockPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx

theorem measurableSet_blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) := by
  apply MeasurableSet.univ_pi
  intro v
  exact
    (P.isOpen_blockPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx).measurableSet

set_option backward.isDefEq.respectTransparency false in
/-- The dependent product of transported overlap measures maps under the
existing inverse-presentation coordinate map to the literal restriction of
the fixed block exceptional Haar product. -/
theorem map_transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure_eq_restrict
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map
        (P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS)
        (P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx) =
      ((P.blockSpace hx)
        |>.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).restrict
        (P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) := by
  let I := {v // v ∈ S}
  let J := {v // v ∈ S ∪
    (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces}
  let e : J ≃ I := P.blockFiniteExceptionalPlaceEquiv hx hS
  let α : I → Type := fun v ↦
    P.transportedAmbientPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  let μ := fun v : I ↦
    P.transportedPadicCentralFiberSourceOverlapProductMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  let f := fun v : J ↦
    fun g : α (e v) ↦
      (by
        let h := P.transportedPadicCentralFiberSourceOverlapHomeomorphBlock
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
          (by
            simpa only [e, blockFiniteExceptionalPlaceEquiv] using g)
        simpa only [e, blockFiniteExceptionalPlaceEquiv] using h.1 :
        (P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1)
  have hlocal (v : J) :
      Measure.map (f v) (μ (e v)) =
        ((P.blockSpace hx)
          |>.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1).restrict
          (P.blockPadicCentralFiberSourceOverlap
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx) := by
    simp only [μ]
    let h := P.transportedPadicCentralFiberSourceOverlapHomeomorphBlock
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
    rw [show f v = Subtype.val ∘ h by
      funext g
      rfl]
    rw [← Measure.map_map continuous_subtype_val.measurable h.measurable]
    have htransport :
        Measure.map h
            (P.transportedPadicCentralFiberSourceOverlapProductMeasure
              (Rat.HeightOneSpectrum.primesEquiv (e v).1).1 hx) =
          P.blockPadicCentralFiberSourceOverlapHaarMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx := by
      simpa only [e, blockFiniteExceptionalPlaceEquiv] using
        P.map_transportedPadicCentralFiberSourceOverlapProductMeasure_to_block
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
    rw [htransport]
    simpa only [e, blockFiniteExceptionalPlaceEquiv,
      heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure] using
      P.map_blockPadicCentralFiberSourceOverlapHaarMeasure_subtype
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  letI (v : J) : SigmaFinite (Measure.map (f v) (μ (e v))) := by
    rw [hlocal]
    infer_instance
  let reindex := (MeasurableEquiv.piCongrLeft α e).symm
  let fiber := fun g : (v : J) → α (e v) ↦ fun v ↦ f v (g v)
  have hreindex :
      Measure.map reindex (Measure.pi μ) = Measure.pi fun v : J ↦ μ (e v) := by
    have hback : MeasurePreserving reindex.symm
        (Measure.pi fun v : J ↦ μ (e v)) (Measure.pi μ) :=
      MeasureTheory.measurePreserving_piCongrLeft μ e
    exact (MeasurePreserving.symm reindex.symm hback).map_eq
  have hfiber : Measurable fiber := by
    apply measurable_pi_lambda
    intro v
    have hfv : Measurable (f v) := by
      let h := P.transportedPadicCentralFiberSourceOverlapHomeomorphBlock
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
      rw [show f v = Subtype.val ∘ h by
        funext g
        rfl]
      exact continuous_subtype_val.measurable.comp h.measurable
    exact hfv.comp (measurable_pi_apply v)
  have hpi :
      Measure.map fiber (Measure.pi fun v : J ↦ μ (e v)) =
        Measure.pi fun v ↦ Measure.map (f v) (μ (e v)) :=
    Measure.pi_map_pi fun v ↦ by
      have hfv : Measurable (f v) := by
        let h := P.transportedPadicCentralFiberSourceOverlapHomeomorphBlock
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
        rw [show f v = Subtype.val ∘ h by
          funext g
          rfl]
        exact continuous_subtype_val.measurable.comp h.measurable
      exact hfv.aemeasurable
  simp_rw [hlocal] at hpi
  have hfun :
      P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS =
        fiber ∘ reindex := by
    funext g v
    unfold blockFiniteExceptionalOverlapToExceptionalProduct fiber reindex f
    rfl
  rw [transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure,
    blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier,
    cliffordGeneralSpinHorizontalExceptionalProductMeasure,
    Measure.restrict_pi_pi, hfun]
  change Measure.map (fiber ∘ reindex) (Measure.pi μ) = _
  calc
    Measure.map (fiber ∘ reindex) (Measure.pi μ) =
        Measure.map fiber (Measure.map reindex (Measure.pi μ)) :=
      (Measure.map_map hfiber reindex.measurable).symm
    _ = Measure.map fiber (Measure.pi fun v : J ↦ μ (e v)) := by rw [hreindex]
    _ = _ := hpi

/-! ## Adjoining the normalized block integral tail -/

/-- The native block exceptional overlap, viewed inside the established
block exceptional/tail source. -/
def blockFiniteAdelicPresentationOverlapCylinderSourceCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set ((P.blockSpace hx).CliffordGeneralSpinHorizontalExceptionalProduct S ×
      (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail S) :=
  P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S ×ˢ Set.univ

theorem measurableSet_blockFiniteAdelicPresentationOverlapCylinderSourceCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (P.blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) :=
  (P.measurableSet_blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S).prod
    MeasurableSet.univ

/-- Forget the transported exceptional overlap proofs and retain the
normalized native block integral tail. -/
def blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx →
      (P.blockSpace hx).CliffordGeneralSpinHorizontalExceptionalProduct S ×
        (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail S :=
  Prod.map (P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS) id

theorem measurable_blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measurable
      (P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS) :=
  (P.measurable_blockFiniteExceptionalOverlapToExceptionalProduct hx hS).prodMap
    measurable_id

/-- After adjoining the probability-normalized good tail, the transported
source measure becomes the literal restriction of the established unweighted
block exceptional/tail source measure. -/
theorem map_transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure_eq_restrict
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map
        (P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS)
        (P.transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx) =
      ((P.blockSpace hx)
        |>.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S).restrict
        (P.blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) := by
  let μE := P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx
  let νE := (P.blockSpace hx).cliffordGeneralSpinHorizontalExceptionalProductMeasure S
  let μT := (P.blockSpace hx)
    |>.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S
  let f := P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS
  letI : SigmaFinite μE := Measure.pi.sigmaFinite _
  letI : SFinite μE := by infer_instance
  have hf : Measurable f :=
    P.measurable_blockFiniteExceptionalOverlapToExceptionalProduct hx hS
  have hE : Measure.map f μE =
      νE.restrict
        (P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) :=
    P.map_transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure_eq_restrict hx hS
  unfold blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource
    transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure
    cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
    blockFiniteAdelicPresentationOverlapCylinderSourceCarrier
  change Measure.map (Prod.map f id) (μE.prod μT) =
    (νE.prod μT).restrict
      (P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S ×ˢ Set.univ)
  rw [← Measure.map_prod_map μE μT hf measurable_id, hE, Measure.map_id]
  rw [← Measure.prod_restrict, Measure.restrict_univ]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
