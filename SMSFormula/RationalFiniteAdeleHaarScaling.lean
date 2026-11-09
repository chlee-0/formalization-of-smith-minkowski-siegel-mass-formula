import SMSFormula.RationalFiniteAdeleStandardFamilyScaleNormalization

/-!
# The finite-adelic Haar scaling law

The Fourier dilation covariance of the standard compact family needs one
measure fact: how the finite-adelic additive Haar measure transforms under
multiplication by a nonzero rational.  This file proves it for the finite
coordinate measure itself.

The proof uses no new normalization.  Multiplication by a nonzero rational is an
additive automorphism of the finite adeles through the rational-algebra
structure, so the pushforward is again an additive Haar measure; Haar uniqueness
then makes it a scalar multiple, and the scalar is determined by the
mass `vol(m * Zhat) = m⁻¹` of the dilation set.
-/

noncomputable section

open MeasureTheory Measure RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

/-! ## Rational scaling as an additive automorphism -/

/-- Multiplication by a nonzero rational, as an additive automorphism of the
finite adeles.  Only the existing rational-algebra structure is used. -/
def rationalFiniteAdeleScaleAddEquiv {q : ℚ} (hq : q ≠ 0) :
    RationalFiniteAdele ≃+ RationalFiniteAdele where
  toFun x := algebraMap ℚ RationalFiniteAdele q * x
  invFun x := algebraMap ℚ RationalFiniteAdele q⁻¹ * x
  left_inv x := by
    show algebraMap ℚ RationalFiniteAdele q⁻¹ *
      (algebraMap ℚ RationalFiniteAdele q * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
  right_inv x := by
    show algebraMap ℚ RationalFiniteAdele q *
      (algebraMap ℚ RationalFiniteAdele q⁻¹ * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq, map_one, one_mul]
  map_add' x y := mul_add _ _ _

@[simp]
theorem rationalFiniteAdeleScaleAddEquiv_apply {q : ℚ} (hq : q ≠ 0)
    (x : RationalFiniteAdele) :
    rationalFiniteAdeleScaleAddEquiv hq x =
      algebraMap ℚ RationalFiniteAdele q * x := rfl

theorem continuous_rationalFiniteAdeleScaleAddEquiv {q : ℚ} (hq : q ≠ 0) :
    Continuous (rationalFiniteAdeleScaleAddEquiv hq) :=
  continuous_const.mul continuous_id

theorem continuous_rationalFiniteAdeleScaleAddEquiv_symm {q : ℚ} (hq : q ≠ 0) :
    Continuous (rationalFiniteAdeleScaleAddEquiv hq).symm :=
  continuous_const.mul continuous_id

/-! ## The preimage of the standard compact -/

theorem preimage_rationalFiniteAdeleScaleAddEquiv_inv {m : ℕ} (hm : m ≠ 0)
    (hq : ((m : ℚ))⁻¹ ≠ 0) :
    (rationalFiniteAdeleScaleAddEquiv hq) ⁻¹'
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) =
      integralFiniteAdeleNatDilationSet m := by
  have hcast : (m : RationalFiniteAdele) =
      algebraMap ℚ RationalFiniteAdele ((m : ℚ)) := by norm_num
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  ext x
  constructor
  · intro hx
    have hmem : algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * x ∈
      integralFiniteAdeleSubring := hx
    refine ⟨⟨algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * x, hmem⟩, ?_⟩
    show (m : ℕ) • (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * x) = x
    rw [nsmul_eq_mul, ← mul_assoc, hcast, ← map_mul, mul_inv_cancel₀ hmq,
      map_one, one_mul]
  · rintro ⟨y, rfl⟩
    show algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
      ((m : ℕ) • (y : RationalFiniteAdele)) ∈ integralFiniteAdeleSubring
    rw [nsmul_eq_mul, ← mul_assoc, hcast, ← map_mul, inv_mul_cancel₀ hmq,
      map_one, one_mul]
    exact y.property

/-! ## The scalar law -/

/-- The finite-adelic additive Haar measure transforms under division by a
nonzero natural number with the exact factor `m⁻¹`.  The scalar is determined
by the mass of the dilation set. -/
theorem map_rationalFiniteAdeleAddHaarMeasure_scale_inv {m : ℕ} (hm : m ≠ 0)
    (hq : ((m : ℚ))⁻¹ ≠ 0) :
    Measure.map (rationalFiniteAdeleScaleAddEquiv hq)
        rationalFiniteAdeleAddHaarMeasure =
      ((m : ℝ≥0))⁻¹ • rationalFiniteAdeleAddHaarMeasure := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  letI : Measure.IsAddHaarMeasure
      (Measure.map (rationalFiniteAdeleScaleAddEquiv hq)
        rationalFiniteAdeleAddHaarMeasure) :=
    AddEquiv.isAddHaarMeasure_map rationalFiniteAdeleAddHaarMeasure
      (rationalFiniteAdeleScaleAddEquiv hq)
      (continuous_rationalFiniteAdeleScaleAddEquiv hq)
      (continuous_rationalFiniteAdeleScaleAddEquiv_symm hq)
  have hval : Measure.map (rationalFiniteAdeleScaleAddEquiv hq)
      rationalFiniteAdeleAddHaarMeasure
      (integralFiniteAdelePositiveCompacts : Set RationalFiniteAdele) =
      ((m : ℝ≥0∞))⁻¹ := by
    have hset : (integralFiniteAdelePositiveCompacts : Set RationalFiniteAdele) =
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) := rfl
    rw [hset, Measure.map_apply
      (continuous_rationalFiniteAdeleScaleAddEquiv hq).measurable
      isOpen_integralFiniteAdeleSubring.measurableSet,
      preimage_rationalFiniteAdeleScaleAddEquiv_inv hm hq,
      rationalFiniteAdeleAddHaarMeasure_natDilationSet m hm]
  have huniq := Measure.addHaarMeasure_unique
    (Measure.map (rationalFiniteAdeleScaleAddEquiv hq)
      rationalFiniteAdeleAddHaarMeasure)
    integralFiniteAdelePositiveCompacts
  rw [huniq, hval]
  have hmne : ((m : ℝ≥0)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  ext s hs
  simp [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_inv hmne]
  rfl

/-! ## The coordinate law -/

theorem map_rationalFiniteAdeleCoordinateAddHaarMeasure_scale_inv (n : ℕ) {m : ℕ}
    (hm : m ≠ 0) (hq : ((m : ℚ))⁻¹ ≠ 0) :
    Measure.map
        (rationalFiniteAdeleCoordinateScale
          (n := n) ((m : ℚ))⁻¹)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      (((m : ℝ≥0))⁻¹ ^ n) •
        rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  let mu := fun _ : Fin n => rationalFiniteAdeleAddHaarMeasure
  let f := fun _ : Fin n =>
    (rationalFiniteAdeleScaleAddEquiv hq : RationalFiniteAdele → RationalFiniteAdele)
  have hmap (i : Fin n) : Measure.map (f i) (mu i) =
      ((m : ℝ≥0))⁻¹ • rationalFiniteAdeleAddHaarMeasure :=
    map_rationalFiniteAdeleAddHaarMeasure_scale_inv hm hq
  have hpi : Measure.map (fun (x : Fin n → RationalFiniteAdele) (i : Fin n) => f i (x i))
      (Measure.pi mu) =
      Measure.pi fun _ : Fin n => ((m : ℝ≥0))⁻¹ • rationalFiniteAdeleAddHaarMeasure := by
    calc
      Measure.map (fun (x : Fin n → RationalFiniteAdele) (i : Fin n) => f i (x i))
          (Measure.pi mu) =
          Measure.pi fun i : Fin n => Measure.map (f i) (mu i) :=
        Measure.pi_map_pi (μ := mu) (f := f)
          (hμ := fun i => by rw [hmap i]; infer_instance)
          (fun _ => (continuous_rationalFiniteAdeleScaleAddEquiv hq).measurable.aemeasurable)
      _ = _ := by
        congr 1
        funext i
        exact hmap i
  change Measure.map (fun (x : Fin n → RationalFiniteAdele) (i : Fin n) => f i (x i))
    (Measure.pi mu) = _
  rw [hpi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply,
    rationalFiniteAdeleCoordinateAddHaarMeasure,
    Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp
  congr 1
  rw [← ENNReal.coe_pow, inv_pow]

/-! ## The integral substitution and the Fourier dilation law -/

/-- Rational scaling of finite-adelic coordinate vectors, as a homeomorphism. -/
def rationalFiniteAdeleCoordinateScaleHomeomorph (n : ℕ) {q : ℚ} (hq : q ≠ 0) :
    (Fin n → RationalFiniteAdele) ≃ₜ (Fin n → RationalFiniteAdele) where
  toFun := rationalFiniteAdeleCoordinateScale q
  invFun := rationalFiniteAdeleCoordinateScale q⁻¹
  left_inv x := by
    rw [rationalFiniteAdeleCoordinateScale_trans,
      inv_mul_cancel₀ hq,
      rationalFiniteAdeleCoordinateScale_one]
  right_inv x := by
    rw [rationalFiniteAdeleCoordinateScale_trans,
      mul_inv_cancel₀ hq,
      rationalFiniteAdeleCoordinateScale_one]
  continuous_toFun :=
    continuous_rationalFiniteAdeleCoordinateScale q
  continuous_invFun :=
    continuous_rationalFiniteAdeleCoordinateScale q⁻¹

/-- The exact integral substitution for division by a nonzero natural number.
The factor is the actual Haar factor; no measure is renormalized. -/
theorem integral_rationalFiniteAdeleCoordinateScale_inv (n : ℕ) {m : ℕ}
    (hm : m ≠ 0) (hq : ((m : ℚ))⁻¹ ≠ 0)
    (F : (Fin n → RationalFiniteAdele) → ℂ) :
    (∫ x, F (rationalFiniteAdeleCoordinateScale ((m : ℚ))⁻¹ x)
      ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) =
      ((m : ℂ))⁻¹ ^ n *
        (∫ x, F x ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
  have he : MeasurableEmbedding
      (rationalFiniteAdeleCoordinateScale (n := n) ((m : ℚ))⁻¹) :=
    (rationalFiniteAdeleCoordinateScaleHomeomorph n hq).toMeasurableEquiv.measurableEmbedding
  rw [← he.integral_map,
    map_rationalFiniteAdeleCoordinateAddHaarMeasure_scale_inv n hm hq,
    integral_smul_nnreal_measure]
  have hcast : ((((m : ℝ≥0))⁻¹ ^ n : ℝ≥0) : ℝ) = ((m : ℝ))⁻¹ ^ n := by
    push_cast
    ring
  rw [NNReal.smul_def, hcast, Complex.real_smul]
  congr 1
  push_cast
  ring

/-! ## The Fourier dilation covariance -/

theorem dotProduct_rationalFiniteAdeleCoordinateScale_inv_nsmul {n : ℕ} {m : ℕ}
    (hm : m ≠ 0) (x w : Fin n → RationalFiniteAdele) :
    dotProduct (rationalFiniteAdeleCoordinateScale ((m : ℚ))⁻¹ x) (m • w) =
      dotProduct x w := by
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hcast : (m : RationalFiniteAdele) =
      algebraMap ℚ RationalFiniteAdele ((m : ℚ)) := by norm_num
  simp only [dotProduct, rationalFiniteAdeleCoordinateScale, Pi.smul_apply,
    nsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcast, show algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * x i *
      (algebraMap ℚ RationalFiniteAdele ((m : ℚ)) * w i) =
      (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
        algebraMap ℚ RationalFiniteAdele ((m : ℚ))) * (x i * w i) by ring,
    ← map_mul, inv_mul_cancel₀ hmq, map_one, one_mul]

/-- Fourier dilation covariance: pulling the test back along the `m`-scaling
multiplies its actual finite Fourier transform by the exact Haar factor `m⁻ⁿ`
and dilates the frequency by `m`.  Both the factor and the frequency change are
literal; no measure is renormalized. -/
theorem standardFiniteFourier_standardScalePullback (n : ℕ) {m : ℕ} (hm : m ≠ 0)
    (hq : ((m : ℚ))⁻¹ ≠ 0)
    (f : (Fin n → RationalFiniteAdele) → ℂ) (w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (standardScalePullback m f) w =
      ((m : ℂ))⁻¹ ^ n * standardFiniteFourier f (m • w) := by
  have hsub := integral_rationalFiniteAdeleCoordinateScale_inv n hm hq
    (fun y => (rationalFiniteAdeleFourierChar (-(dotProduct y (m • w))) : ℂ) * f y)
  have hlhs : standardFiniteFourier (standardScalePullback m f) w =
      ∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) *
        f (rationalFiniteAdeleCoordinateScale ((m : ℚ))⁻¹ x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) := rfl
  have hrhs : standardFiniteFourier f (m • w) =
      ∫ y, (rationalFiniteAdeleFourierChar (-(dotProduct y (m • w))) : ℂ) * f y
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) := rfl
  rw [hlhs, hrhs, ← hsub]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [dotProduct_rationalFiniteAdeleCoordinateScale_inv_nsmul hm]

end PositiveDefiniteIntegralLattice
