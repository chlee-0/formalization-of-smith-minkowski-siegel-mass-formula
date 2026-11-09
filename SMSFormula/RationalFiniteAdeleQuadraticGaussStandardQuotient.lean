import SMSFormula.RationalFiniteAdeleIntegralLatticeFiniteQuotient
import SMSFormula.RationalFiniteAdeleQuadraticGaussAnnihilator

/-!
# The standard finite quadratic Gauss integral as an exact finite quotient

This file proves that the actual standard-lattice quadratic phase with
rational parameter `t` is periodic modulo `t.den * Zhat^n`.  It also identifies
the old ambient indicator integral with the integral-subtype Haar integral and
then applies the section-free finite-quotient averaging theorem.

No residue representatives are chosen.  The polar-dual integral, finite Gauss
reciprocity value, dyadic/discriminant phase, and Weil index remain outside
this file.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

theorem measurableSet_integralFiniteAdeleVectors (d : ℕ) :
    MeasurableSet (integralFiniteAdeleVectors d) := by
  have heq :
      integralFiniteAdeleVectors d =
        Set.univ.pi fun _ : Fin d =>
          (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
    ext x
    simp [integralFiniteAdeleVectors]
  rw [heq]
  exact MeasurableSet.univ_pi fun _ =>
    isOpen_integralFiniteAdeleSubring.measurableSet

/-- Coordinatewise inclusion of the integral finite adeles into the ambient
finite adeles. -/
def integralFiniteAdeleCoordinateCoe (d : ℕ) :
    (Fin d → IntegralFiniteAdele) → (Fin d → RationalFiniteAdele) :=
  fun x i ↦ x i

theorem measurePreserving_integralFiniteAdeleCoordinateCoe (d : ℕ) :
    MeasurePreserving (integralFiniteAdeleCoordinateCoe d)
      (integralFiniteAdeleCoordinateAddHaarMeasure d)
      ((rationalFiniteAdeleCoordinateAddHaarMeasure d).restrict
        (integralFiniteAdeleVectors d)) := by
  let hscalar : MeasurePreserving
      (fun x : IntegralFiniteAdele ↦ (x : RationalFiniteAdele))
      integralFiniteAdeleAddHaarMeasure
      (rationalFiniteAdeleAddHaarMeasure.restrict
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    change Measure.map (fun x : IntegralFiniteAdele ↦
      (x : RationalFiniteAdele))
        (Measure.comap Subtype.val rationalFiniteAdeleAddHaarMeasure) = _
    exact map_comap_subtype_coe
      isOpen_integralFiniteAdeleSubring.measurableSet _
  have hpi := measurePreserving_pi
    (fun _ : Fin d ↦ integralFiniteAdeleAddHaarMeasure)
    (fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure.restrict
      (integralFiniteAdeleSubring : Set RationalFiniteAdele))
    (fun _ ↦ hscalar)
  have hset :
      integralFiniteAdeleVectors d =
        Set.univ.pi fun _ : Fin d =>
          (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
    ext x
    simp [integralFiniteAdeleVectors]
  refine ⟨hpi.measurable, ?_⟩
  change Measure.map (integralFiniteAdeleCoordinateCoe d)
      (Measure.pi fun _ : Fin d ↦ integralFiniteAdeleAddHaarMeasure) =
    (Measure.pi fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure).restrict
      (integralFiniteAdeleVectors d)
  rw [hset, Measure.restrict_pi_pi]
  exact hpi.map_eq

private theorem finiteAdelicQuadraticFormValue_nsmul
    (V : RationalQuadraticSpaceMatrix n) (m : ℕ)
    (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (m • x) =
      (m : RationalFiniteAdele) ^ 2 * V.finiteAdelicQuadraticFormValue x := by
  simp only [finiteAdelicQuadraticFormValue, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  ring_nf

private theorem rational_den_coefficient_mem_integral
    (t : ℚ) :
    algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ∈
      integralFiniteAdeleSubring := by
  have hcoeff :
      algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele (t.num : ℚ) := by
    rw [show (t.den : RationalFiniteAdele) =
      algebraMap ℚ RationalFiniteAdele (t.den : ℚ) by norm_num]
    rw [← map_mul, Rat.mul_den_eq_num]
  rw [hcoeff]
  exact integer_mem_integralFiniteAdeleSubring t.num

private theorem rational_den_sq_coefficient_mem_integral
    (t : ℚ) :
    algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ^ 2 ∈
      integralFiniteAdeleSubring := by
  rw [pow_two, ← mul_assoc]
  exact integralFiniteAdeleSubring.mul_mem
    (rational_den_coefficient_mem_integral t)
    (by
      exact_mod_cast
        integer_mem_integralFiniteAdeleSubring (t.den : ℤ))

private theorem finiteAdelicPolarPairing_mem_integral
    (L : PositiveDefiniteIntegralLattice n)
    (x y : Fin n → RationalFiniteAdele)
    (hx : x ∈ integralFiniteAdeleVectors n)
    (hy : y ∈ integralFiniteAdeleVectors n) :
    dotProduct x
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y) ∈
      integralFiniteAdeleSubring := by
  rw [L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix_eq_two_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  exact integralFiniteAdeleSubring.mul_mem
    (by norm_num)
    (L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring x y hx hy)

private theorem dotProduct_scaledFiniteAdelicPolarFrequency_nsmul
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) (m : ℕ)
    (x y : Fin n → RationalFiniteAdele) :
    dotProduct x (V.scaledFiniteAdelicPolarFrequency t (m • y)) =
      (algebraMap ℚ RationalFiniteAdele t * (m : RationalFiniteAdele)) *
        dotProduct x (V.finiteAdelicPolarMatrix.mulVec y) := by
  simp only [scaledFiniteAdelicPolarFrequency, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The standard finite quadratic phase restricted to the integral coordinate
lattice. -/
def rationalFiniteAdeleIntegralQuadraticPhase
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (x : Fin n → IntegralFiniteAdele) : ℂ :=
  (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
    (fun i ↦ (x i : RationalFiniteAdele)) : ℂ)

/-- The integral-lattice quadratic phase with rational parameter `t` is
periodic modulo `t.den * Zhat^n`. -/
theorem rationalFiniteAdeleIntegralQuadraticPhase_add_denDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈
      (integralFiniteAdeleCoordinateNatDilation n t.den).range) :
    rationalFiniteAdeleIntegralQuadraticPhase L t (x + z) =
      rationalFiniteAdeleIntegralQuadraticPhase L t x := by
  rcases hz with ⟨w, rfl⟩
  let xa : Fin n → RationalFiniteAdele := fun i ↦ x i
  let wa : Fin n → RationalFiniteAdele := fun i ↦ w i
  have hxa : xa ∈ integralFiniteAdeleVectors n := fun i ↦ (x i).property
  have hwa : wa ∈ integralFiniteAdeleVectors n := fun i ↦ (w i).property
  have harg :
      (fun i ↦ (((x +
        integralFiniteAdeleCoordinateNatDilation n t.den w) i :
          IntegralFiniteAdele) : RationalFiniteAdele)) =
        xa + t.den • wa := by
    rfl
  unfold rationalFiniteAdeleIntegralQuadraticPhase
  rw [harg]
  rw [L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase_add]
  have hq :
      L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue wa ∈
        integralFiniteAdeleSubring := by
    simpa [finiteAdelicQuadraticFormValue] using
      L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring
        wa wa hwa hwa
  have hphase :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
          (t.den • wa) = 1 := by
    unfold rationalFiniteAdeleQuadraticPhase
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [finiteAdelicQuadraticFormValue_nsmul]
    simpa [mul_assoc] using integralFiniteAdeleSubring.mul_mem
      (rational_den_sq_coefficient_mem_integral t) hq
  have hpair :
      rationalFiniteAdeleVectorPairingChar xa
        (L.rationalQuadraticSpaceMatrix.scaledFiniteAdelicPolarFrequency t
          (t.den • wa)) = 1 := by
    unfold rationalFiniteAdeleVectorPairingChar
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [dotProduct_scaledFiniteAdelicPolarFrequency_nsmul]
    exact integralFiniteAdeleSubring.mul_mem
      (rational_den_coefficient_mem_integral t)
      (finiteAdelicPolarPairing_mem_integral L xa wa hxa hwa)
  rw [hphase, hpair]
  simp [xa]

theorem rationalFiniteAdeleQuadraticPhase_mul_integralIndicator_eq_indicator
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    (fun x : Fin n → RationalFiniteAdele ↦
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator x) =
      (integralFiniteAdeleVectors n).indicator fun x ↦
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) := by
  funext x
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
    simp [hx]
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
    simp [hx]

/-- The ambient standard-lattice Gauss integral is exactly the quadratic
phase integral on the integral finite-adele coordinate subtype. -/
theorem rationalFiniteAdeleQuadraticGaussIntegral_eq_integralQuadraticPhase
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t =
      ∫ x : Fin n → IntegralFiniteAdele,
        rationalFiniteAdeleIntegralQuadraticPhase L t x
        ∂integralFiniteAdeleCoordinateAddHaarMeasure n := by
  unfold rationalFiniteAdeleQuadraticGaussIntegral
  rw [rationalFiniteAdeleQuadraticPhase_mul_integralIndicator_eq_indicator L t]
  rw [integral_indicator (measurableSet_integralFiniteAdeleVectors n)]
  have hcontinuous : Continuous
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t) := by
    unfold rationalFiniteAdeleQuadraticPhase finiteAdelicQuadraticFormValue
    apply continuous_rationalFiniteAdeleFourierChar.comp
    fun_prop
  rw [← (measurePreserving_integralFiniteAdeleCoordinateCoe n).map_eq]
  rw [integral_map
    (measurePreserving_integralFiniteAdeleCoordinateCoe n).aemeasurable
    hcontinuous.subtype_val.aestronglyMeasurable]
  rfl

private noncomputable instance rationalDenNeZero (t : ℚ) : NeZero t.den :=
  ⟨t.den_nz⟩

/-- Exact finite quotient formula for the standard finite quadratic Gauss
integral.  The quotient is literal and no residue representatives are chosen. -/
theorem rationalFiniteAdeleQuadraticGaussIntegral_eq_denQuotientSum
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t =
      (((t.den : ℝ) ^ n : ℂ)⁻¹) *
        ∑ q, addQuotientPeriodicLift
          (integralFiniteAdeleCoordinateNatDilation n t.den).range
          (rationalFiniteAdeleIntegralQuadraticPhase L t)
          (rationalFiniteAdeleIntegralQuadraticPhase_add_denDilation L t) q := by
  rw [rationalFiniteAdeleQuadraticGaussIntegral_eq_integralQuadraticPhase L t]
  exact integralFiniteAdeleCoordinate_integral_periodic_eq_inv_pow_sum
    n t.den (rationalFiniteAdeleIntegralQuadraticPhase L t)
      (rationalFiniteAdeleIntegralQuadraticPhase_add_denDilation L t)

end RationalQuadraticSpaceMatrix
