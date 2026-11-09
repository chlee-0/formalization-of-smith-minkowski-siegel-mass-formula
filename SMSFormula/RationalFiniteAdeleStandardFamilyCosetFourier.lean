import SMSFormula.RationalFiniteAdeleStandardFamilySpanning
import SMSFormula.RationalFiniteAdeleHaarScaling

/-!
# The actual finite Fourier transform of every spanning piece

This supplies the last ingredient of the spanning decomposition.
The dilated-lattice indicator is literally the `N`-scaling pullback of the
standard indicator, so the already closed Fourier dilation covariance and the
self-duality of the standard indicator evaluate its transform exactly:

```text
Fhat(1_(N * Zhat^n))(w) = N^-n * 1_(Zhat^n)(N * w).
```

Since every coset indicator is a literal translate of that one, for every member
of its class, the already closed translation covariance then evaluates the
transform of every piece of the spanning decomposition, with the existing
character carrying the only dependence on the member.

No Haar measure is rescaled, no representative or section is chosen, and no
Poisson identity or theta transformation is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The dilated-lattice indicator is a scaling pullback -/

theorem standardDilatedIndicator_eq_scalePullback (n : ℕ) {N : ℕ} (hN : N ≠ 0) :
    standardDilatedIndicator n N =
      standardScalePullback N
        (rationalFiniteAdeleVectorIntegralIndicator :
          (Fin n → RationalFiniteAdele) → ℂ) := by
  funext x
  have hmem : x ∈ standardDilatedLattice n N ↔
      rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x ∈
        integralFiniteAdeleVectors n := by
    rw [standardDilatedLattice_eq_preimage hN]
    exact Iff.rfl
  by_cases hx : x ∈ standardDilatedLattice n N
  · rw [standardDilatedIndicator, Set.indicator_of_mem hx]
    show (1 : ℂ) = rationalFiniteAdeleVectorIntegralIndicator
      (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x)
    rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem (hmem.mp hx)]
  · rw [standardDilatedIndicator, Set.indicator_of_notMem hx]
    show (0 : ℂ) = rationalFiniteAdeleVectorIntegralIndicator
      (rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ x)
    rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem
      (fun hcon => hx (hmem.mpr hcon))]

/-! ## The transform of the dilated-lattice indicator -/

/-- The exact finite Fourier transform of the dilated-lattice indicator.  The
factor is the actual Haar factor of the dilation and the support condition is
the literal `N`-divided lattice; nothing is normalized. -/
theorem standardFiniteFourier_standardDilatedIndicator (n : ℕ) {N : ℕ}
    (hN : N ≠ 0) (hq : ((N : ℚ))⁻¹ ≠ 0) (w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (standardDilatedIndicator n N) w =
      ((N : ℂ))⁻¹ ^ n * rationalFiniteAdeleVectorIntegralIndicator (N • w) := by
  rw [standardDilatedIndicator_eq_scalePullback n hN,
    standardFiniteFourier_standardScalePullback n hN hq _ w]
  congr 1
  rw [standardFiniteFourier_eq_fourierIntegral,
    rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator]

/-- The transform is carried by the literal `N`-divided lattice. -/
theorem standardFiniteFourier_standardDilatedIndicator_eq_zero (n : ℕ) {N : ℕ}
    (hN : N ≠ 0) (hq : ((N : ℚ))⁻¹ ≠ 0) {w : Fin n → RationalFiniteAdele}
    (hw : w ∉ standardDividedLattice n N) :
    standardFiniteFourier (standardDilatedIndicator n N) w = 0 := by
  rw [standardFiniteFourier_standardDilatedIndicator n hN hq w,
    rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hw, mul_zero]

/-! ## The transform of every spanning piece -/

/-- The exact finite Fourier transform of a coset indicator, for every member of
the class.  The member enters only through the existing additive character, and
the remaining factor is the transform of the dilated-lattice indicator. -/
theorem standardFiniteFourier_standardCosetIndicator (n : ℕ) {N : ℕ}
    (hN : N ≠ 0) (hq : ((N : ℚ))⁻¹ ≠ 0)
    (y : Fin n → IntegralFiniteAdele) (w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (standardCosetIndicator n N
        ((y : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range))) w =
      (rationalFiniteAdeleFourierChar
        (-(dotProduct (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) w)) : ℂ) *
        (((N : ℂ))⁻¹ ^ n * rationalFiniteAdeleVectorIntegralIndicator (N • w)) := by
  have htrans : standardCosetIndicator n N
      ((y : (Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n N).range)) =
      fun x => standardDilatedIndicator n N
        (x + -(fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele))) := by
    rw [standardCosetIndicator_eq_translate n N y]
    funext x
    rw [← sub_eq_add_neg]
  rw [htrans, standardFiniteFourier_translate,
    standardFiniteFourier_standardDilatedIndicator n hN hq w]
  congr 2
  rw [neg_dotProduct]

/-! ## Coset indicators are family members -/

theorem standardDilatedIndicator_add_nsmul {N : ℕ} (hN : N ≠ 0)
    (z : Fin n → RationalFiniteAdele) {u : Fin n → RationalFiniteAdele}
    (hu : u ∈ integralFiniteAdeleVectors n) :
    standardDilatedIndicator n N (z + N • u) = standardDilatedIndicator n N z := by
  have hadd : rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ (z + N • u) =
      rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ z + u := by
    rw [show rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ (z + N • u) =
        rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ z +
          rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ (N • u) by
      funext i
      simp [rationalFiniteAdeleCoordinateScale, mul_add],
      rationalFiniteAdeleCoordinateScale_inv_nsmul hN]
  have hiff : z + N • u ∈ standardDilatedLattice n N ↔
      z ∈ standardDilatedLattice n N := by
    rw [standardDilatedLattice_eq_preimage hN]
    show rationalFiniteAdeleCoordinateScale ((N : ℚ))⁻¹ (z + N • u) ∈
      integralFiniteAdeleVectors n ↔ _
    rw [hadd]
    constructor
    · intro h i
      have := integralFiniteAdeleSubring.sub_mem (h i) (hu i)
      simpa using this
    · intro h i
      exact integralFiniteAdeleSubring.add_mem (h i) (hu i)
  by_cases hz : z ∈ standardDilatedLattice n N
  · rw [standardDilatedIndicator, Set.indicator_of_mem (hiff.mpr hz),
      Set.indicator_of_mem hz]
    rfl
  · rw [standardDilatedIndicator, Set.indicator_of_notMem (fun hc => hz (hiff.mp hc)),
      Set.indicator_of_notMem hz]

theorem isStandardCarried_standardCosetIndicator (n N : ℕ)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) :
    IsStandardCarried 1 (standardCosetIndicator n N alpha) := by
  intro x hx
  refine standardCosetIndicator_of_not_integral alpha (fun hmem => hx ?_)
  show (1 : ℕ) • x ∈ integralFiniteAdeleVectors n
  rwa [one_smul]

theorem isStandardPeriodic_standardCosetIndicator (n : ℕ) {N : ℕ} (hN : N ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) :
    IsStandardPeriodic N (standardCosetIndicator n N alpha) := by
  induction alpha using Quotient.inductionOn' with
  | _ y =>
    intro x u hu
    rw [standardCosetIndicator_eq_translate n N y]
    show standardDilatedIndicator n N
        (x + N • u - fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) =
      standardDilatedIndicator n N
        (x - fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele))
    rw [show x + N • u - (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) =
        (x - fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) + N • u by abel]
    exact standardDilatedIndicator_add_nsmul hN _ hu

theorem integrable_standardCosetIndicator (n : ℕ) {N : ℕ} (hN : N ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) :
    Integrable (standardCosetIndicator n N alpha)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
  integrable_of_isStandardCarried_isStandardPeriodic one_ne_zero hN
    (isStandardCarried_standardCosetIndicator n N alpha)
    (isStandardPeriodic_standardCosetIndicator n hN alpha)

/-! ## Assembling the transform of a family member -/

theorem integrable_negativeChar_mul {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hf : Integrable f (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (w : Fin n → RationalFiniteAdele) :
    Integrable (fun x => (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f x)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hc : Continuous fun x : Fin n → RationalFiniteAdele =>
      rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
    apply continuous_rationalFiniteAdeleFourierChar.comp
    fun_prop
  apply hf.bdd_mul hc.subtype_val.aestronglyMeasurable
  filter_upwards with x
  exact le_of_eq (Circle.norm_coe _)

theorem standardFiniteFourier_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → (Fin n → RationalFiniteAdele) → ℂ) (w : Fin n → RationalFiniteAdele)
    (hF : ∀ i ∈ s, Integrable (F i) (rationalFiniteAdeleCoordinateAddHaarMeasure n)) :
    standardFiniteFourier (fun x => ∑ i ∈ s, F i x) w =
      ∑ i ∈ s, standardFiniteFourier (F i) w := by
  show (∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) *
      ∑ i ∈ s, F i x ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) = _
  rw [show (fun x : Fin n → RationalFiniteAdele =>
      (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * ∑ i ∈ s, F i x) =
      fun x => ∑ i ∈ s, (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * F i x by
    funext x
    rw [Finset.mul_sum]]
  exact integral_finset_sum s fun i hi => integrable_negativeChar_mul (hF i hi) w

theorem standardFiniteFourier_const_mul (c : ℂ)
    (f : (Fin n → RationalFiniteAdele) → ℂ) (w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (fun x => c * f x) w = c * standardFiniteFourier f w := by
  show (∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * (c * f x)
      ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) = _
  rw [show (fun x : Fin n → RationalFiniteAdele =>
      (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * (c * f x)) =
      fun x => c * ((rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f x) by
    funext x
    ring]
  exact integral_const_mul _ _

/-- The actual finite Fourier transform of a scale-one family member is the
finite sum of its descent values against the transforms of the coset indicators,
each of which is explicit.  No Poisson identity is asserted. -/
theorem standardFiniteFourier_eq_sum_cosetFourier {N : ℕ} [NeZero N]
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic N g)
    (w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier g w =
      ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        standardFiniteFourier (standardCosetIndicator n N alpha) w := by
  conv_lhs => rw [standardScaleOne_eq_sum_cosetIndicator hcarried hperiodic]
  rw [standardFiniteFourier_finsetSum Finset.univ _ w
    (fun alpha _ => (integrable_standardCosetIndicator n (NeZero.ne N) alpha).const_mul _)]
  exact Finset.sum_congr rfl fun alpha _ =>
    standardFiniteFourier_const_mul _ _ w

end RationalQuadraticSpaceMatrix
