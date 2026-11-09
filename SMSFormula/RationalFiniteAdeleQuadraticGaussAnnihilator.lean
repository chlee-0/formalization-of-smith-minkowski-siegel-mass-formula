import SMSFormula.RationalFiniteAdeleIntegralLatticeDilation
import SMSFormula.RationalAdeleRankOneBruhatFactorization

/-!
# The finite quadratic Gauss autocorrelation kernel

This file performs the exact quadratic cancellation needed before estimating
the finite factor of the rank-one Bruhat coefficient.  For the literal polar
matrix `C = 2F`, translating the quadratic phase by `z` leaves a linear
character in `x` at frequency `t C z`.  The already certified self-dual
standard-lattice Fourier calculation then evaluates the inner autocorrelation
integral as the indicator of the exact annihilator locus.

No denominator estimate, adjugate containment, rational-height sum, or
Eisenstein functional is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators ComplexConjugate FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

private theorem measurableSet_integralFiniteAdeleVectors (d : ℕ) :
    MeasurableSet (integralFiniteAdeleVectors d) := by
  have heq :
      integralFiniteAdeleVectors d =
        Set.univ.pi fun _ : Fin d =>
          (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
    ext x
    constructor
    · intro hx i _hi
      exact hx i
    · intro hx i
      exact hx i (Set.mem_univ i)
  have hpi :
      MeasurableSet (Set.univ.pi fun _ : Fin d =>
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)) :=
    MeasurableSet.univ_pi fun _ =>
      isOpen_integralFiniteAdeleSubring.measurableSet
  rw [heq]
  exact hpi

private theorem rationalFiniteAdeleVectorIntegralIndicator_eq_indicator
    (d : ℕ) :
    (rationalFiniteAdeleVectorIntegralIndicator :
        (Fin d → RationalFiniteAdele) → ℂ) =
      (integralFiniteAdeleVectors d).indicator fun _ => (1 : ℂ) := by
  funext x
  by_cases hx : x ∈ integralFiniteAdeleVectors d
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
    simp [hx]
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
    simp [hx]

private theorem rationalFiniteAdeleVectorIntegralIndicator_add_of_mem
    (x z : Fin n → RationalFiniteAdele)
    (hz : z ∈ integralFiniteAdeleVectors n) :
    rationalFiniteAdeleVectorIntegralIndicator (x + z) =
      rationalFiniteAdeleVectorIntegralIndicator x := by
  unfold rationalFiniteAdeleVectorIntegralIndicator
  apply Finset.prod_congr rfl
  intro i _hi
  exact rationalFiniteAdeleIntegralIndicator_add_of_mem (x i) (z i) (hz i)

private theorem continuous_rationalFiniteAdeleQuadraticPhase
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    Continuous (V.rationalFiniteAdeleQuadraticPhase t) := by
  unfold rationalFiniteAdeleQuadraticPhase finiteAdelicQuadraticFormValue
  apply continuous_rationalFiniteAdeleFourierChar.comp
  fun_prop

private theorem integrable_quadraticPhase_mul_indicator
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    Integrable (fun x : Fin n → RationalFiniteAdele =>
      (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator x)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  apply (integrable_rationalFiniteAdeleVectorIntegralIndicator n).bdd_mul
  · exact (V.continuous_rationalFiniteAdeleQuadraticPhase t).subtype_val.aestronglyMeasurable
  · filter_upwards
    intro x
    exact le_of_eq (Circle.norm_coe _)

local instance rationalFiniteAdeleCoordinateAddHaarMeasure_isAddLeftInvariant
    (d : ℕ) :
    Measure.IsAddLeftInvariant
      (rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  refine ⟨fun z => ?_⟩
  change Measure.map (fun x => z + x)
      (Measure.pi fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure) =
    Measure.pi fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure
  have hpres := measurePreserving_pi
    (fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure)
    (fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure)
    (fun i => measurePreserving_add_left rationalFiniteAdeleAddHaarMeasure (z i))
  exact hpres.map_eq

/-- The finite-adelic polar matrix is literally twice the finite-adelic form
matrix.  The factor two remains visible at every dyadic place. -/
theorem finiteAdelicPolarMatrix_eq_two_smul
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicPolarMatrix =
      (2 : RationalFiniteAdele) • V.finiteAdelicFormMatrix := by
  apply Matrix.ext
  intro i j
  simp only [finiteAdelicPolarMatrix, polarMatrix, finiteAdelicFormMatrix,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [map_ofNat]

/-- The exact frequency left by translating a finite quadratic phase. -/
def scaledFiniteAdelicPolarFrequency
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (z : Fin n → RationalFiniteAdele) : Fin n → RationalFiniteAdele :=
  fun i => algebraMap ℚ RationalFiniteAdele t *
    (V.finiteAdelicPolarMatrix.mulVec z) i

/-- Polarization of the finite-adelic quadratic value with the literal matrix
`C = 2F`. -/
theorem finiteAdelicQuadraticFormValue_add
    (V : RationalQuadraticSpaceMatrix n)
    (x z : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (x + z) =
      V.finiteAdelicQuadraticFormValue x +
        V.finiteAdelicQuadraticFormValue z +
          dotProduct x (V.finiteAdelicPolarMatrix.mulVec z) := by
  have hsymm : V.finiteAdelicFormMatrix.IsSymm := V.form_symm.map _
  have hcross :
      dotProduct z (V.finiteAdelicFormMatrix.mulVec x) =
        dotProduct x (V.finiteAdelicFormMatrix.mulVec z) := by
    have hvec :
        Matrix.vecMul z V.finiteAdelicFormMatrix =
          V.finiteAdelicFormMatrix.mulVec z := by
      funext i
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hsymm.apply i j, mul_comm]
    rw [Matrix.dotProduct_mulVec z V.finiteAdelicFormMatrix x,
      hvec, dotProduct_comm]
  simp only [finiteAdelicQuadraticFormValue, Matrix.mulVec_add,
    dotProduct_add, add_dotProduct]
  rw [hcross, V.finiteAdelicPolarMatrix_eq_two_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The translated quadratic phase is the old phase, the phase at the
translation, and the residual linear character at frequency `t C z`. -/
theorem rationalFiniteAdeleQuadraticPhase_add
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (x z : Fin n → RationalFiniteAdele) :
    V.rationalFiniteAdeleQuadraticPhase t (x + z) =
      V.rationalFiniteAdeleQuadraticPhase t x *
        V.rationalFiniteAdeleQuadraticPhase t z *
          rationalFiniteAdeleVectorPairingChar x
            (V.scaledFiniteAdelicPolarFrequency t z) := by
  unfold rationalFiniteAdeleQuadraticPhase
  rw [V.finiteAdelicQuadraticFormValue_add]
  simp only [mul_add, AddChar.map_add_eq_mul]
  congr 2
  unfold scaledFiniteAdelicPolarFrequency
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem continuous_scaledFiniteAdelicPolarFrequency
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    Continuous (V.scaledFiniteAdelicPolarFrequency t) := by
  unfold scaledFiniteAdelicPolarFrequency
  fun_prop

/-- The exact finite-adelic annihilator locus for the translated quadratic
phase. -/
def finiteQuadraticGaussAnnihilatorLocus
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    Set (Fin n → RationalFiniteAdele) :=
  integralFiniteAdeleVectors n ∩
    V.scaledFiniteAdelicPolarFrequency t ⁻¹'
      integralFiniteAdeleVectors n

theorem measurableSet_finiteQuadraticGaussAnnihilatorLocus
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    MeasurableSet (V.finiteQuadraticGaussAnnihilatorLocus t) := by
  exact (measurableSet_integralFiniteAdeleVectors n).inter
    ((measurableSet_integralFiniteAdeleVectors n).preimage
      (V.continuous_scaledFiniteAdelicPolarFrequency t).measurable)

/-- Exact finite-lattice autocorrelation kernel.  The inner integral is
supported precisely where the translated polar frequency belongs to the
standard integral finite-adelic lattice. -/
theorem integral_quadraticPhase_translate_mul_inv
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (z : Fin n → RationalFiniteAdele) :
    (∫ x : Fin n → RationalFiniteAdele,
        (((V.rationalFiniteAdeleQuadraticPhase t (x + z)) *
            (V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      (V.rationalFiniteAdeleQuadraticPhase t z : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator
          (V.scaledFiniteAdelicPolarFrequency t z) := by
  let w := V.scaledFiniteAdelicPolarFrequency t z
  have hpoint : ∀ x : Fin n → RationalFiniteAdele,
      (((V.rationalFiniteAdeleQuadraticPhase t (x + z)) *
          (V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator x =
      (V.rationalFiniteAdeleQuadraticPhase t z : ℂ) *
        (((rationalFiniteAdeleCoordinateFourierChar n (x * w) : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x) := by
    intro x
    have hcircle :
        V.rationalFiniteAdeleQuadraticPhase t (x + z) *
            (V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ =
          V.rationalFiniteAdeleQuadraticPhase t z *
            rationalFiniteAdeleVectorPairingChar x
              (V.scaledFiniteAdelicPolarFrequency t z) := by
      rw [V.rationalFiniteAdeleQuadraticPhase_add]
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [hcircle]
    simp only [Circle.coe_mul]
    rw [rationalFiniteAdeleCoordinateFourierChar_mul_eq_dotProduct]
    change _ = _ * (((rationalFiniteAdeleVectorPairingChar x w : Circle) : ℂ) * _)
    simp [w, mul_assoc]
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hfourier :=
    rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator n (-w)
  rw [Fourier.fourierIntegral_def] at hfourier
  have hintegrand :
      (fun x : Fin n → RationalFiniteAdele =>
        ((rationalFiniteAdeleCoordinateFourierChar n (x * w) : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x) =
      (fun x : Fin n → RationalFiniteAdele =>
        rationalFiniteAdeleCoordinateFourierChar n (- (x * (-w))) •
          rationalFiniteAdeleVectorIntegralIndicator x) := by
    funext x
    simp [Circle.smul_def]
  rw [hintegrand, hfourier]
  by_cases hw : w ∈ integralFiniteAdeleVectors n
  · have hneg : -w ∈ integralFiniteAdeleVectors n := fun i =>
      integralFiniteAdeleSubring.neg_mem (hw i)
    rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hw,
      rationalFiniteAdeleVectorIntegralIndicator_of_mem hneg]
  · have hneg : -w ∉ integralFiniteAdeleVectors n := by
      intro h
      exact hw (fun i => by simpa using
        integralFiniteAdeleSubring.neg_mem (h i))
    rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hw,
      rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hneg]

/-- Translation by an integral finite-adelic vector does not change the
standard-lattice quadratic Gauss integral.  This is Haar translation on the
existing coordinate measure, not a new compact-group normalization. -/
theorem integral_quadraticPhase_translate_of_mem
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (x : Fin n → RationalFiniteAdele)
    (hx : x ∈ integralFiniteAdeleVectors n) :
    (∫ z : Fin n → RationalFiniteAdele,
        (V.rationalFiniteAdeleQuadraticPhase t (x + z) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator z
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      V.rationalFiniteAdeleQuadraticGaussIntegral t := by
  let f : (Fin n → RationalFiniteAdele) → ℂ := fun z =>
    (V.rationalFiniteAdeleQuadraticPhase t z : ℂ) *
      rationalFiniteAdeleVectorIntegralIndicator z
  calc
    (∫ z : Fin n → RationalFiniteAdele,
        (V.rationalFiniteAdeleQuadraticPhase t (x + z) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator z
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      ∫ z : Fin n → RationalFiniteAdele, f (x + z)
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
          apply integral_congr_ae
          filter_upwards
          intro z
          simp only [f]
          rw [show rationalFiniteAdeleVectorIntegralIndicator z =
              rationalFiniteAdeleVectorIntegralIndicator (x + z) by
            simpa [add_comm] using
              (rationalFiniteAdeleVectorIntegralIndicator_add_of_mem z x hx).symm]
    _ = ∫ z : Fin n → RationalFiniteAdele, f z
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n :=
      integral_add_left_eq_self f x
    _ = V.rationalFiniteAdeleQuadraticGaussIntegral t := rfl

private theorem integrable_quadraticPhase_autocorrelation
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    Integrable (fun p :
        (Fin n → RationalFiniteAdele) × (Fin n → RationalFiniteAdele) =>
      rationalFiniteAdeleVectorIntegralIndicator p.1 *
        (((V.rationalFiniteAdeleQuadraticPhase t (p.2 + p.1)) *
            (V.rationalFiniteAdeleQuadraticPhase t p.2)⁻¹ : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator p.2)
      ((rationalFiniteAdeleCoordinateAddHaarMeasure n).prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
  have hbase :=
    (integrable_rationalFiniteAdeleVectorIntegralIndicator n).mul_prod
      (integrable_rationalFiniteAdeleVectorIntegralIndicator n)
  have hphase : AEStronglyMeasurable
      (fun p :
          (Fin n → RationalFiniteAdele) × (Fin n → RationalFiniteAdele) =>
        ((((V.rationalFiniteAdeleQuadraticPhase t (p.2 + p.1)) *
            (V.rationalFiniteAdeleQuadraticPhase t p.2)⁻¹ : Circle) : ℂ)))
      ((rationalFiniteAdeleCoordinateAddHaarMeasure n).prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
    have hc : Continuous
        (fun p :
            (Fin n → RationalFiniteAdele) × (Fin n → RationalFiniteAdele) =>
          V.rationalFiniteAdeleQuadraticPhase t (p.2 + p.1) *
            (V.rationalFiniteAdeleQuadraticPhase t p.2)⁻¹) := by
      exact
        ((V.continuous_rationalFiniteAdeleQuadraticPhase t).comp
          (continuous_snd.add continuous_fst)).mul
        ((V.continuous_rationalFiniteAdeleQuadraticPhase t).comp
          continuous_snd).inv
    exact hc.subtype_val.aestronglyMeasurable
  have hbound : ∀ᵐ p :
      (Fin n → RationalFiniteAdele) × (Fin n → RationalFiniteAdele)
      ∂((rationalFiniteAdeleCoordinateAddHaarMeasure n).prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)),
      ‖((((V.rationalFiniteAdeleQuadraticPhase t (p.2 + p.1)) *
          (V.rationalFiniteAdeleQuadraticPhase t p.2)⁻¹ : Circle) : ℂ))‖ ≤ 1 := by
    filter_upwards
    intro p
    exact le_of_eq (Circle.norm_coe _)
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    hbase.bdd_mul hphase hbound

set_option synthInstance.maxHeartbeats 100000

/-- The average of the exact autocorrelation kernel is the squared norm of
the original finite quadratic Gauss integral. -/
theorem integral_integral_quadraticPhase_translate_mul_inv
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    (∫ z : Fin n → RationalFiniteAdele,
        rationalFiniteAdeleVectorIntegralIndicator z *
          (∫ x : Fin n → RationalFiniteAdele,
            (((V.rationalFiniteAdeleQuadraticPhase t (x + z)) *
                (V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
              rationalFiniteAdeleVectorIntegralIndicator x
            ∂rationalFiniteAdeleCoordinateAddHaarMeasure n)
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      starRingEnd ℂ (V.rationalFiniteAdeleQuadraticGaussIntegral t) *
        V.rationalFiniteAdeleQuadraticGaussIntegral t := by
  let μ := rationalFiniteAdeleCoordinateAddHaarMeasure n
  let G := V.rationalFiniteAdeleQuadraticGaussIntegral t
  letI : ∀ _ : Fin n, SigmaFinite rationalFiniteAdeleAddHaarMeasure :=
    fun _ => rationalFiniteAdeleAddHaarMeasure_sigmaFinite
  letI : SFinite μ := by
    dsimp [μ]
    unfold rationalFiniteAdeleCoordinateAddHaarMeasure
    infer_instance
  let h : (Fin n → RationalFiniteAdele) →
      (Fin n → RationalFiniteAdele) → ℂ := fun z x =>
    rationalFiniteAdeleVectorIntegralIndicator z *
      (((V.rationalFiniteAdeleQuadraticPhase t (x + z)) *
          (V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator x
  have hint : Integrable (Function.uncurry h) (μ.prod μ) := by
    simpa [h, μ] using V.integrable_quadraticPhase_autocorrelation t
  have hinner : ∀ x : Fin n → RationalFiniteAdele,
      (∫ z : Fin n → RationalFiniteAdele, h z x ∂μ) =
        G * (((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x := by
    intro x
    calc
      (∫ z : Fin n → RationalFiniteAdele, h z x ∂μ) =
          (∫ z : Fin n → RationalFiniteAdele,
              (V.rationalFiniteAdeleQuadraticPhase t (x + z) : ℂ) *
                rationalFiniteAdeleVectorIntegralIndicator z ∂μ) *
            ((((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
              rationalFiniteAdeleVectorIntegralIndicator x) := by
            rw [← integral_mul_const]
            apply integral_congr_ae
            filter_upwards
            intro z
            simp only [h, Circle.coe_mul]
            ring
      _ = G * ((((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
              rationalFiniteAdeleVectorIntegralIndicator x) := by
            by_cases hx : x ∈ integralFiniteAdeleVectors n
            · rw [V.integral_quadraticPhase_translate_of_mem t x hx]
            · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
              simp
      _ = G * (((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
            rationalFiniteAdeleVectorIntegralIndicator x := by ring
  have hinv :
      (∫ x : Fin n → RationalFiniteAdele,
          ((((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
            rationalFiniteAdeleVectorIntegralIndicator x) ∂μ) =
        starRingEnd ℂ G := by
    change (∫ x : Fin n → RationalFiniteAdele,
        ((((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x) ∂μ) =
      starRingEnd ℂ (∫ x : Fin n → RationalFiniteAdele,
        (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x ∂μ)
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards
    intro x
    by_cases hx : x ∈ integralFiniteAdeleVectors n
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
      simp only [mul_one]
      calc
        (V.rationalFiniteAdeleQuadraticPhase t x : ℂ)⁻¹ =
            (((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) := by
              rw [Circle.coe_inv]
        _ = starRingEnd ℂ (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) :=
          Circle.coe_inv_eq_conj _
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
      simp
  calc
    (∫ z : Fin n → RationalFiniteAdele,
        rationalFiniteAdeleVectorIntegralIndicator z *
          (∫ x : Fin n → RationalFiniteAdele,
            (((V.rationalFiniteAdeleQuadraticPhase t (x + z)) *
                (V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
              rationalFiniteAdeleVectorIntegralIndicator x ∂μ) ∂μ) =
      ∫ z : Fin n → RationalFiniteAdele,
        ∫ x : Fin n → RationalFiniteAdele, h z x ∂μ ∂μ := by
          apply integral_congr_ae
          filter_upwards
          intro z
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards
          intro x
          simp only [h]
          ring
    _ = ∫ x : Fin n → RationalFiniteAdele,
        ∫ z : Fin n → RationalFiniteAdele, h z x ∂μ ∂μ :=
      integral_integral_swap hint
    _ = ∫ x : Fin n → RationalFiniteAdele,
        G * (((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x ∂μ := by
            apply integral_congr_ae
            filter_upwards
            intro x
            exact hinner x
    _ = G * ∫ x : Fin n → RationalFiniteAdele,
          ((((V.rationalFiniteAdeleQuadraticPhase t x)⁻¹ : Circle) : ℂ) *
            rationalFiniteAdeleVectorIntegralIndicator x) ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards
          intro x
          ring
    _ = starRingEnd ℂ G * G := by rw [hinv]; ring
    _ = starRingEnd ℂ (V.rationalFiniteAdeleQuadraticGaussIntegral t) *
          V.rationalFiniteAdeleQuadraticGaussIntegral t := rfl

/-- Exact integral formula behind the finite quadratic Gauss norm-square
estimate. -/
theorem quadraticGauss_conj_mul_eq_integral_annihilatorPhase
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    starRingEnd ℂ (V.rationalFiniteAdeleQuadraticGaussIntegral t) *
        V.rationalFiniteAdeleQuadraticGaussIntegral t =
      ∫ z : Fin n → RationalFiniteAdele,
        rationalFiniteAdeleVectorIntegralIndicator z *
          ((V.rationalFiniteAdeleQuadraticPhase t z : ℂ) *
            rationalFiniteAdeleVectorIntegralIndicator
              (V.scaledFiniteAdelicPolarFrequency t z))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  rw [← V.integral_integral_quadraticPhase_translate_mul_inv t]
  apply integral_congr_ae
  filter_upwards
  intro z
  rw [V.integral_quadraticPhase_translate_mul_inv t z]

/-- The squared norm of the literal finite quadratic Gauss integral is
bounded by the normalized Haar mass of its exact annihilator locus. -/
theorem norm_quadraticGaussIntegral_sq_le_measure_annihilatorLocus
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    ‖V.rationalFiniteAdeleQuadraticGaussIntegral t‖ ^ 2 ≤
      (rationalFiniteAdeleCoordinateAddHaarMeasure n
        (V.finiteQuadraticGaussAnnihilatorLocus t)).toReal := by
  let G := V.rationalFiniteAdeleQuadraticGaussIntegral t
  let μ := rationalFiniteAdeleCoordinateAddHaarMeasure n
  let k : (Fin n → RationalFiniteAdele) → ℂ := fun z =>
    rationalFiniteAdeleVectorIntegralIndicator z *
      ((V.rationalFiniteAdeleQuadraticPhase t z : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator
          (V.scaledFiniteAdelicPolarFrequency t z))
  have hformula : starRingEnd ℂ G * G = ∫ z, k z ∂μ := by
    simpa [G, μ, k] using
      V.quadraticGauss_conj_mul_eq_integral_annihilatorPhase t
  have hnorm :
      (fun z => ‖k z‖) =
        (V.finiteQuadraticGaussAnnihilatorLocus t).indicator
          (fun _ => (1 : ℝ)) := by
    funext z
    dsimp [k]
    by_cases hz : z ∈ integralFiniteAdeleVectors n
    · by_cases hw : V.scaledFiniteAdelicPolarFrequency t z ∈
          integralFiniteAdeleVectors n
      · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hz,
          rationalFiniteAdeleVectorIntegralIndicator_of_mem hw]
        simp [finiteQuadraticGaussAnnihilatorLocus, hz, hw]
      · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hz,
          rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hw]
        simp [finiteQuadraticGaussAnnihilatorLocus, hz, hw]
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hz]
      simp [finiteQuadraticGaussAnnihilatorLocus, hz]
  calc
    ‖V.rationalFiniteAdeleQuadraticGaussIntegral t‖ ^ 2 =
        ‖starRingEnd ℂ G * G‖ := by
          simp [G, pow_two]
    _ = ‖∫ z, k z ∂μ‖ := by rw [hformula]
    _ ≤ ∫ z, ‖k z‖ ∂μ := norm_integral_le_integral_norm k
    _ = ∫ z,
        (V.finiteQuadraticGaussAnnihilatorLocus t).indicator
          (fun _ => (1 : ℝ)) z ∂μ := by rw [hnorm]
    _ = (μ (V.finiteQuadraticGaussAnnihilatorLocus t)).toReal := by
      rw [integral_indicator_const (1 : ℝ)
        (V.measurableSet_finiteQuadraticGaussAnnihilatorLocus t)]
      simp [measureReal_def]
    _ = (rationalFiniteAdeleCoordinateAddHaarMeasure n
        (V.finiteQuadraticGaussAnnihilatorLocus t)).toReal := rfl

end RationalQuadraticSpaceMatrix
