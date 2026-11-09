import SMSFormula.ConductorStratumMass
import SMSFormula.RationalAdeleRankOneAdelicBruhatFactorization

/-!
# The Bruhat coefficient's finite factor is the local integral

This file proves the identification: the finite factor of the
adelic Bruhat coefficient at a frequency is the local integral the conductor chain bounds.  Both
objects already exist in the repository; what separates them is a change of domain, and that is what
this file supplies.

The finite factor integrates over all finite-adelic vectors, against the ambient coordinate Haar,
the phase times the integral-vector indicator.  The local integral integrates over the integral
vectors, against their own probability Haar, the phase alone.  The bridge is that the coordinate
inclusion is measure preserving onto the ambient measure restricted to the integral vectors.

The bridge is pure Mathlib once located, and the locating is the work: the one-coordinate measure is
the comap of the ambient one along the subtype inclusion, so `MeasurableEmbedding.map_comap` pushes
it to the ambient measure restricted to the range, which is the integral finite adeles;
`Measure.pi_map_pi` raises that to the product coordinatewise; and `Measure.restrict_pi_pi` turns the
product of restrictions into the restriction of the product.  Nothing is constructed.

The indicator is the restriction, read off: the product indicator is one on the integral vectors and
zero off them, so the weighted ambient integral is the restricted integral.

Negative scope.  This identifies the two integrals.  It does not bound either, evaluate any Gauss
sum, or say anything about the archimedean factor; and the conductor decomposition of the
finite-adelic integral over the frequency is a separate statement about the frequency variable, not
about this one.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory SMSFormula.QuadraticPhaseDescent Matrix RationalQuadraticSpaceMatrix
open scoped ENNReal

variable {n : ℕ}

/-! ## The coordinate inclusion is measure preserving -/

/-- The subtype inclusion is a measurable embedding, the integral finite adeles being open. -/
theorem measurableEmbedding_integralFiniteAdele_val :
    MeasurableEmbedding (Subtype.val : IntegralFiniteAdele → RationalFiniteAdele) :=
  MeasurableEmbedding.subtype_coe isOpen_integralFiniteAdeleSubring.measurableSet

/-- Its range is the integral finite adeles. -/
theorem range_integralFiniteAdele_val :
    Set.range (Subtype.val : IntegralFiniteAdele → RationalFiniteAdele) =
      (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  rw [Subtype.range_coe]
  rfl

/-- One coordinate: the integral Haar pushes forward to the ambient Haar restricted to the integral
finite adeles -- the comap of a measurable embedding, pushed back. -/
theorem map_val_integralFiniteAdeleAddHaarMeasure :
    Measure.map (Subtype.val : IntegralFiniteAdele → RationalFiniteAdele)
        integralFiniteAdeleAddHaarMeasure =
      rationalFiniteAdeleAddHaarMeasure.restrict
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  rw [integralFiniteAdeleAddHaarMeasure,
    measurableEmbedding_integralFiniteAdele_val.map_comap,
    range_integralFiniteAdele_val]

/-- All coordinates: the same statement on vectors, by the product lemma. -/
theorem map_coordCoe_integralCoordinateHaar (n : ℕ) :
    Measure.map (fun (x : Fin n → IntegralFiniteAdele) i ↦ (x i : RationalFiniteAdele))
        (integralFiniteAdeleCoordinateAddHaarMeasure n) =
      (rationalFiniteAdeleCoordinateAddHaarMeasure n).restrict
        (Set.univ.pi fun _ : Fin n ↦ (integralFiniteAdeleSubring : Set RationalFiniteAdele)) := by
  have hmap : ∀ _ : Fin n, Measure.map
      (Subtype.val : IntegralFiniteAdele → RationalFiniteAdele)
        integralFiniteAdeleAddHaarMeasure =
      rationalFiniteAdeleAddHaarMeasure.restrict
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) :=
    fun _ ↦ map_val_integralFiniteAdeleAddHaarMeasure
  have hsig : ∀ i : Fin n, SigmaFinite
      ((integralFiniteAdeleAddHaarMeasure).map
        (Subtype.val : IntegralFiniteAdele → RationalFiniteAdele)) := by
    intro i
    rw [map_val_integralFiniteAdeleAddHaarMeasure]
    infer_instance
  rw [integralFiniteAdeleCoordinateAddHaarMeasure,
    Measure.pi_map_pi (μ := fun _ : Fin n ↦ integralFiniteAdeleAddHaarMeasure)
      (f := fun _ : Fin n ↦ (Subtype.val : IntegralFiniteAdele → RationalFiniteAdele))
      (fun _ ↦ measurable_subtype_coe.aemeasurable)]
  simp only [map_val_integralFiniteAdeleAddHaarMeasure]
  rw [← Measure.restrict_pi_pi]
  rfl

/-- SO the coordinate inclusion is measure preserving onto the restricted ambient measure. -/
theorem measurePreserving_coordCoe (n : ℕ) :
    MeasurePreserving (fun (x : Fin n → IntegralFiniteAdele) i ↦ (x i : RationalFiniteAdele))
      (integralFiniteAdeleCoordinateAddHaarMeasure n)
      ((rationalFiniteAdeleCoordinateAddHaarMeasure n).restrict
        (Set.univ.pi fun _ : Fin n ↦ (integralFiniteAdeleSubring : Set RationalFiniteAdele))) :=
  ⟨measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).subtype_val,
    map_coordCoe_integralCoordinateHaar n⟩

/-! ## The weighted ambient integral is the restricted one -/

/-- The product indicator is the set indicator of the integral vectors, read off from its two
evaluations. -/
theorem vectorIntegralIndicator_eq_indicator (F : (Fin n → RationalFiniteAdele) → ℂ)
    (x : Fin n → RationalFiniteAdele) :
    F x * rationalFiniteAdeleVectorIntegralIndicator x =
      (Set.univ.pi fun _ : Fin n ↦
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)).indicator F x := by
  by_cases hx : x ∈ Set.univ.pi fun _ : Fin n ↦
      (integralFiniteAdeleSubring : Set RationalFiniteAdele)
  · rw [Set.indicator_of_mem hx,
      rationalFiniteAdeleVectorIntegralIndicator_of_mem (fun i ↦ hx i (Set.mem_univ i)), mul_one]
  · rw [Set.indicator_of_notMem hx]
    have hi : ∃ i : Fin n, x i ∉ (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
      by_contra hcon
      push_neg at hcon
      exact hx fun i _ ↦ hcon i
    obtain ⟨i, hi⟩ := hi
    rw [rationalFiniteAdeleVectorIntegralIndicator, Finset.prod_eq_zero (Finset.mem_univ i)
      (rationalFiniteAdeleIntegralIndicator_of_not_mem hi), mul_zero]

/-! ## The identification -/

/-- The identification: the weighted ambient integral is the local integral over the integral
vectors -- a change of domain, nothing evaluated. -/
theorem integral_ambient_weighted_eq_local (F : (Fin n → RationalFiniteAdele) → ℂ)
    (hF : Measurable F) :
    ∫ x, F x * rationalFiniteAdeleVectorIntegralIndicator x
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      ∫ x : Fin n → IntegralFiniteAdele, F (fun i ↦ (x i : RationalFiniteAdele))
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hmeas : Measurable (fun (x : Fin n → IntegralFiniteAdele) i ↦
      (x i : RationalFiniteAdele)) :=
    measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).subtype_val
  rw [show (∫ x : Fin n → IntegralFiniteAdele, F (fun i ↦ (x i : RationalFiniteAdele))
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)) =
      ∫ y, F y ∂(Measure.map (fun (x : Fin n → IntegralFiniteAdele) i ↦
        (x i : RationalFiniteAdele)) (integralFiniteAdeleCoordinateAddHaarMeasure n)) from
      (integral_map hmeas.aemeasurable hF.aestronglyMeasurable).symm,
    map_coordCoe_integralCoordinateHaar n,
    ← MeasureTheory.integral_indicator
      (MeasurableSet.univ_pi fun _ ↦ isOpen_integralFiniteAdeleSubring.measurableSet)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x ↦ vectorIntegralIndicator_eq_indicator F x)

/-! ## The finite factor is the local integral -/

/-- The phase is measurable, the character being continuous and the form a finite sum of products. -/
theorem measurable_quadraticPhaseAt (V : RationalQuadraticSpaceMatrix n)
    (s : RationalFiniteAdele) :
    Measurable (fun y : Fin n → RationalFiniteAdele ↦
      ((V.rationalFiniteAdeleQuadraticPhaseAt s y : Circle) : ℂ)) := by
  have hc : Continuous (V.rationalFiniteAdeleQuadraticPhaseAt s) := by
    unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
      RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
    apply continuous_rationalFiniteAdeleFourierChar.comp
    fun_prop
  exact hc.subtype_val.measurable

/-- The identification: the adelic Bruhat coefficient's finite factor at a frequency is
the local integral of the frequency phase over the integral finite-adelic vectors -- the object the
conductor chain bounds.  Only the domain changes; the integrand is the same by `rfl`. -/
theorem gaussIntegralAt_eq_localIntegral (V : RationalQuadraticSpaceMatrix n)
    (s : RationalFiniteAdele) :
    V.rationalFiniteAdeleQuadraticGaussIntegralAt s =
      ∫ x : Fin n → IntegralFiniteAdele,
          complexFiniteChar (scaledQuadratic s V.finiteAdelicFormMatrix x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) := by
  rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt]
  exact integral_ambient_weighted_eq_local _ (measurable_quadraticPhaseAt V s)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
