import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberSourceOverlapRecovery
import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCylinderTransport

/-!
# Recovery of finite exceptional presentation overlaps

The local common-source measure recovered from the fixed p-adic horizontal
`GSpin` Haar is assembled over a certified presentation support.  Forgetting
the overlap proofs in every exceptional coordinate sends the dependent
product measure to the literal restriction of the repository's established
exceptional Haar product.

This is an unweighted restriction theorem.  In particular, it does not
compare the independently defined coherent principal-block weights or
identify the finite presentation scalar.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance finiteExceptionalRecoveryDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteExceptionalRecoveryPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The certified support identifies the ambient exceptional index type with
the displayed finite support. -/
def ambientFiniteExceptionalPlaceEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ≃
      {v // v ∈ S} where
  toFun v :=
    ⟨v.1, (Finset.mem_union.mp v.2).elim (fun hv ↦ hv) (fun hv ↦ hS.2.1 hv)⟩
  invFun v := ⟨v.1, Finset.mem_union_left _ v.2⟩
  left_inv v := by
    cases v
    rfl
  right_inv v := by
    cases v
    rfl

/-- The literal ambient exceptional-product carrier on which every local
coordinate belongs to the genuine common selected-chart source. -/
def ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Set.pi Set.univ fun v ↦
    P.transportedAmbientPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx

theorem measurableSet_ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) := by
  apply MeasurableSet.univ_pi
  intro v
  exact
    (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx).measurableSet

set_option backward.isDefEq.respectTransparency false in
/-- The dependent product of recovered local overlap measures is exactly the
restriction of the fixed exceptional horizontal Haar product.  The support
hypothesis is used only to identify the repository's exceptional index set
with the supplied finite presentation support. -/
theorem map_ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure_eq_restrict
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map
        (P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS)
        (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx) =
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).restrict
        (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) := by
  let I := {v // v ∈ S}
  let J := {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}
  let e : J ≃ I := P.ambientFiniteExceptionalPlaceEquiv hx hS
  let α : I → Type := fun v ↦
    P.transportedAmbientPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  letI (v : J) : BorelSpace (α (e v)) := Subtype.borelSpace _
  let μ := fun v : I ↦
    P.ambientPadicCentralFiberSourceOverlapProductMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  let f := fun v : J ↦
    fun g : α (e v) ↦
      (by
        simpa only [e, ambientFiniteExceptionalPlaceEquiv] using
          (g : V.HeightOnePadicCliffordGeneralSpinGroup (e v).1) :
        V.HeightOnePadicCliffordGeneralSpinGroup v.1)
  have hlocal (v : J) :
      Measure.map (f v) (μ (e v)) =
        (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1).restrict
          (P.transportedAmbientPadicCentralFiberSourceOverlap
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx) := by
    simp only [μ]
    rw [P.ambientPadicCentralFiberSourceOverlapProductMeasure_eq_haar]
    simpa only [e, ambientFiniteExceptionalPlaceEquiv, f, α,
      heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure] using
      P.map_ambientPadicCentralFiberSourceOverlapHaarMeasure_subtype
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
    simpa only [fiber, f, e, ambientFiniteExceptionalPlaceEquiv] using
      continuous_subtype_val.measurable.comp (measurable_pi_apply v)
  have hpi :
      Measure.map fiber (Measure.pi fun v : J ↦ μ (e v)) =
        Measure.pi fun v ↦ Measure.map (f v) (μ (e v)) :=
    Measure.pi_map_pi fun v ↦ continuous_subtype_val.measurable.aemeasurable
  simp_rw [hlocal] at hpi
  have hfun :
      P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS =
        fiber ∘ reindex := by
    funext g v
    unfold ambientFiniteExceptionalOverlapToExceptionalProduct fiber reindex
    change (g _).1 = (g _).1
    congr 2
  rw [ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure,
    ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier,
    cliffordGeneralSpinHorizontalExceptionalProductMeasure,
    Measure.restrict_pi_pi, hfun]
  change Measure.map (fiber ∘ reindex) (Measure.pi μ) = _
  calc
    Measure.map (fiber ∘ reindex) (Measure.pi μ) =
        Measure.map fiber (Measure.map reindex (Measure.pi μ)) :=
      (Measure.map_map hfiber reindex.measurable).symm
    _ = Measure.map fiber (Measure.pi fun v : J ↦ μ (e v)) := by rw [hreindex]
    _ = _ := hpi

/-! ## Adjoining the normalized integral tail -/

/-- The common exceptional overlap, viewed inside the established direct
exceptional/tail source. -/
def ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S ×ˢ Set.univ

theorem measurableSet_ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) :=
  (P.measurableSet_ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S).prod
    MeasurableSet.univ

/-- Forget the exceptional overlap proofs and retain the normalized ambient
integral tail. -/
def ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.AmbientFiniteAdelicPresentationOverlapCylinderSource S hx →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S :=
  Prod.map (P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS) id

theorem measurable_ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measurable
      (P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS) :=
  (P.measurable_ambientFiniteExceptionalOverlapToExceptionalProduct hx hS).prodMap
    measurable_id

/-- After adjoining the probability-normalized good tail, the recovered
exceptional overlap remains the literal restriction of the established
unweighted exceptional/tail source measure. -/
theorem map_ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure_eq_restrict
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map
        (P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS)
        (P.ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx) =
      (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S).restrict
        (P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) := by
  let μE := P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx
  let νE := V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S
  let μT := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S
  let f := P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS
  letI : SigmaFinite μE := Measure.pi.sigmaFinite _
  letI : SFinite μE := by infer_instance
  have hf : Measurable f :=
    P.measurable_ambientFiniteExceptionalOverlapToExceptionalProduct hx hS
  have hE : Measure.map f μE =
      νE.restrict
        (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) :=
    P.map_ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure_eq_restrict hx hS
  unfold ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource
    ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure
    cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
    ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier
  change Measure.map (Prod.map f id) (μE.prod μT) =
    (νE.prod μT).restrict
      (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S ×ˢ Set.univ)
  rw [← Measure.map_prod_map μE μT hf measurable_id, hE, Measure.map_id]
  rw [← Measure.prod_restrict, Measure.restrict_univ]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
