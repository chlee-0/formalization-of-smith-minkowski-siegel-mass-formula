import SMSFormula.RationalFiniteAdeleQuadraticGaussFourierRegularity

/-!
# The standard compact locally constant finite test family

The finite Fourier-output regularity already proved for the standard indicator
is here extended to the family the finite Bruhat generators actually produce.
A finite test `f` belongs to the family when it is

* Carried by the `c`-divided standard lattice, `c * x` not integral implies
  `f x = 0`, and
* Periodic modulo the `d`-dilated standard lattice, `f (x + d * u) = f x` for
  every standard-integral `u`.

Only the existing standard lattice and the existing rational-algebra structure
of the finite adeles are used.  No cutoff subgroup, conductor, dual lattice
normalization, residue representative or quotient section is chosen, and no
Haar measure is rescaled.

This file proves that the family is genuinely closed under the two finite
generators, with explicit scales, and that every member is continuous with
compact support hence L1.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance rationalFiniteAdeleStandardFamilyT2 : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

/-! ## Rational scaling of finite-adelic coordinates -/

/-- Coordinatewise multiplication by a rational scalar, using the existing
rational-algebra structure of the finite adeles. -/
def rationalFiniteAdeleCoordinateScale (q : ℚ)
    (x : Fin n → RationalFiniteAdele) : Fin n → RationalFiniteAdele :=
  fun i => algebraMap ℚ RationalFiniteAdele q * x i

theorem continuous_rationalFiniteAdeleCoordinateScale (q : ℚ) :
    Continuous (rationalFiniteAdeleCoordinateScale (n := n) q) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem rationalFiniteAdeleCoordinateScale_natCast (m : ℕ)
    (x : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale (m : ℚ) x = m • x := by
  funext i
  simp [rationalFiniteAdeleCoordinateScale, nsmul_eq_mul]

theorem rationalFiniteAdeleCoordinateScale_trans (q r : ℚ)
    (x : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale q
        (rationalFiniteAdeleCoordinateScale r x) =
      rationalFiniteAdeleCoordinateScale (q * r) x := by
  funext i
  simp [rationalFiniteAdeleCoordinateScale, map_mul, mul_assoc]

@[simp]
theorem rationalFiniteAdeleCoordinateScale_one (x : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale 1 x = x := by
  funext i
  simp [rationalFiniteAdeleCoordinateScale]

theorem rationalFiniteAdeleCoordinateScale_image_eq_preimage {q : ℚ} (hq : q ≠ 0)
    (s : Set (Fin n → RationalFiniteAdele)) :
    rationalFiniteAdeleCoordinateScale q '' s =
      rationalFiniteAdeleCoordinateScale q⁻¹ ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [rationalFiniteAdeleCoordinateScale_trans, inv_mul_cancel₀ hq] using hx
  · intro hy
    exact ⟨rationalFiniteAdeleCoordinateScale q⁻¹ y, hy, by
      rw [rationalFiniteAdeleCoordinateScale_trans, mul_inv_cancel₀ hq,
        rationalFiniteAdeleCoordinateScale_one]⟩

/-! ## Divided and dilated standard lattices -/

/-- The `c`-divided standard lattice, defined intrinsically as the vectors
whose `c`-multiple is standard-integral. -/
def standardDividedLattice (n c : ℕ) : Set (Fin n → RationalFiniteAdele) :=
  {x | c • x ∈ integralFiniteAdeleVectors n}

@[simp]
theorem mem_standardDividedLattice_iff (c : ℕ) (x : Fin n → RationalFiniteAdele) :
    x ∈ standardDividedLattice n c ↔ c • x ∈ integralFiniteAdeleVectors n :=
  Iff.rfl

theorem standardDividedLattice_eq_preimage (c : ℕ) :
    standardDividedLattice n c =
      rationalFiniteAdeleCoordinateScale (c : ℚ) ⁻¹' integralFiniteAdeleVectors n := by
  ext x
  simp [standardDividedLattice, rationalFiniteAdeleCoordinateScale_natCast]

theorem isOpen_standardDividedLattice (n c : ℕ) :
    IsOpen (standardDividedLattice n c) := by
  rw [standardDividedLattice_eq_preimage]
  exact (isOpen_integralFiniteAdeleVectors n).preimage
    (continuous_rationalFiniteAdeleCoordinateScale _)

theorem isCompact_standardDividedLattice {c : ℕ} (hc : c ≠ 0) :
    IsCompact (standardDividedLattice n c) := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hset : standardDividedLattice n c =
      rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ '' integralFiniteAdeleVectors n := by
    rw [rationalFiniteAdeleCoordinateScale_image_eq_preimage (inv_ne_zero hq), inv_inv,
      standardDividedLattice_eq_preimage]
  rw [hset]
  exact (isCompact_integralFiniteAdeleVectors n).image
    (continuous_rationalFiniteAdeleCoordinateScale _)

theorem integralFiniteAdeleVectors_subset_standardDividedLattice (c : ℕ) :
    integralFiniteAdeleVectors n ⊆ standardDividedLattice n c := fun _ hx =>
  nsmul_mem_integralFiniteAdeleVectors hx

theorem rationalFiniteAdeleQuadraticGaussFourierCarrier_eq (t : ℚ) :
    rationalFiniteAdeleQuadraticGaussFourierCarrier n t =
      standardDividedLattice n t.den := rfl

/-- The `d`-dilated standard lattice. -/
def standardDilatedLattice (n d : ℕ) : Set (Fin n → RationalFiniteAdele) :=
  (fun u : Fin n → RationalFiniteAdele => d • u) '' integralFiniteAdeleVectors n

theorem standardDilatedLattice_eq_preimage {d : ℕ} (hd : d ≠ 0) :
    standardDilatedLattice n d =
      rationalFiniteAdeleCoordinateScale ((d : ℚ))⁻¹ ⁻¹' integralFiniteAdeleVectors n := by
  have hq : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hfun : (fun u : Fin n → RationalFiniteAdele => d • u) =
      rationalFiniteAdeleCoordinateScale (d : ℚ) := by
    funext u
    rw [rationalFiniteAdeleCoordinateScale_natCast]
  rw [standardDilatedLattice, hfun,
    rationalFiniteAdeleCoordinateScale_image_eq_preimage hq]

theorem isOpen_standardDilatedLattice {d : ℕ} (hd : d ≠ 0) :
    IsOpen (standardDilatedLattice n d) := by
  rw [standardDilatedLattice_eq_preimage hd]
  exact (isOpen_integralFiniteAdeleVectors n).preimage
    (continuous_rationalFiniteAdeleCoordinateScale _)

/-! ## The standard compact locally constant family -/

/-- `f` is carried by the `c`-divided standard lattice. -/
def IsStandardCarried (c : ℕ) (f : (Fin n → RationalFiniteAdele) → ℂ) : Prop :=
  ∀ x, x ∉ standardDividedLattice n c → f x = 0

/-- `f` is periodic modulo the `d`-dilated standard lattice. -/
def IsStandardPeriodic (d : ℕ) (f : (Fin n → RationalFiniteAdele) → ℂ) : Prop :=
  ∀ x u, u ∈ integralFiniteAdeleVectors n → f (x + d • u) = f x

theorem IsStandardCarried.mono {c c' : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hf : IsStandardCarried c f) (hdvd : c ∣ c') : IsStandardCarried c' f := by
  obtain ⟨k, rfl⟩ := hdvd
  intro x hx
  refine hf x fun hmem => hx ?_
  show (c * k) • x ∈ integralFiniteAdeleVectors n
  rw [mul_nsmul]
  exact nsmul_mem_integralFiniteAdeleVectors hmem

theorem IsStandardPeriodic.mono {d d' : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hf : IsStandardPeriodic d f) (hdvd : d ∣ d') : IsStandardPeriodic d' f := by
  obtain ⟨k, rfl⟩ := hdvd
  intro x u hu
  rw [mul_nsmul']
  exact hf x (k • u) (nsmul_mem_integralFiniteAdeleVectors hu)

/-- The standard lattice indicator lies in the family at both scales one. -/
theorem isStandardCarried_integralIndicator :
    IsStandardCarried 1 (rationalFiniteAdeleVectorIntegralIndicator :
      (Fin n → RationalFiniteAdele) → ℂ) := by
  intro x hx
  apply rationalFiniteAdeleVectorIntegralIndicator_of_not_mem
  simpa using hx

theorem isStandardPeriodic_integralIndicator :
    IsStandardPeriodic 1 (rationalFiniteAdeleVectorIntegralIndicator :
      (Fin n → RationalFiniteAdele) → ℂ) := by
  intro x u hu
  rw [one_smul]
  exact rationalFiniteAdeleVectorIntegralIndicator_add_of_mem x hu

/-! ## Regularity of every member -/

theorem IsStandardPeriodic.isLocallyConstant {d : ℕ} (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f) :
    IsLocallyConstant f := by
  have hq : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => rationalFiniteAdeleCoordinateScale ((d : ℚ))⁻¹ (y - x)) ⁻¹'
      integralFiniteAdeleVectors n,
    (isOpen_integralFiniteAdeleVectors n).preimage
      ((continuous_rationalFiniteAdeleCoordinateScale _).comp (by fun_prop)), ?_, ?_⟩
  · show rationalFiniteAdeleCoordinateScale ((d : ℚ))⁻¹ (x - x) ∈
      integralFiniteAdeleVectors n
    rw [sub_self]
    intro i
    simp [rationalFiniteAdeleCoordinateScale]
  · intro y hy
    have hmem : rationalFiniteAdeleCoordinateScale ((d : ℚ))⁻¹ (y - x) ∈
        integralFiniteAdeleVectors n := hy
    have hsplit : y = x + d • rationalFiniteAdeleCoordinateScale ((d : ℚ))⁻¹ (y - x) := by
      rw [← rationalFiniteAdeleCoordinateScale_natCast,
        rationalFiniteAdeleCoordinateScale_trans, mul_inv_cancel₀ hq,
        rationalFiniteAdeleCoordinateScale_one]
      abel
    rw [hsplit]
    exact hf x _ hmem

theorem IsStandardPeriodic.continuous {d : ℕ} (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f) :
    Continuous f :=
  (hf.isLocallyConstant hd).continuous

theorem IsStandardCarried.hasCompactSupport {c : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_standardDividedLattice hc) hf

/-- Every member of the family is genuinely L1 for the existing finite
coordinate Haar measure. -/
theorem integrable_of_isStandardCarried_isStandardPeriodic
    {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    Integrable f (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  letI : IsFiniteMeasureOnCompacts rationalFiniteAdeleAddHaarMeasure := inferInstance
  letI : IsFiniteMeasureOnCompacts (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    show IsFiniteMeasureOnCompacts
      (Measure.pi fun _ : Fin n => rationalFiniteAdeleAddHaarMeasure) from inferInstance
  exact (hperiodic.continuous hd).integrable_of_hasCompactSupport
    (hcarried.hasCompactSupport hc)

/-! ## Arithmetic helpers on the standard lattice -/

theorem dotProduct_nsmul_comm (m : ℕ) (x y : Fin n → RationalFiniteAdele) :
    dotProduct x (m • y) = dotProduct (m • x) y := by
  simp only [dotProduct, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem nsmul_dotProduct_eq (m : ℕ) (x y : Fin n → RationalFiniteAdele) :
    dotProduct (m • x) y = (m : RationalFiniteAdele) * dotProduct x y := by
  simp only [dotProduct, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem standardFamily_quadraticFormValue_nsmul
    (V : RationalQuadraticSpaceMatrix n) (m : ℕ)
    (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (m • x) =
      (m : RationalFiniteAdele) ^ 2 * V.finiteAdelicQuadraticFormValue x := by
  simp only [finiteAdelicQuadraticFormValue, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  ring_nf

private theorem standardFamily_natCast_mem (m : ℕ) :
    (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := by
  exact_mod_cast integer_mem_integralFiniteAdeleSubring (m : ℤ)

private theorem standardFamily_den_coefficient_mem (t : ℚ) :
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

private theorem standardFamily_den_sq_coefficient_mem (t : ℚ) :
    algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ^ 2 ∈
      integralFiniteAdeleSubring := by
  rw [pow_two, ← mul_assoc]
  exact integralFiniteAdeleSubring.mul_mem (standardFamily_den_coefficient_mem t)
    (standardFamily_natCast_mem t.den)

private theorem standardFamily_polarPairing_mem (L : PositiveDefiniteIntegralLattice n)
    {x y : Fin n → RationalFiniteAdele}
    (hx : x ∈ integralFiniteAdeleVectors n)
    (hy : y ∈ integralFiniteAdeleVectors n) :
    dotProduct x
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y) ∈
      integralFiniteAdeleSubring := by
  rw [L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix_eq_two_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  exact integralFiniteAdeleSubring.mul_mem (by norm_num)
    (L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring x y hx hy)

private theorem standardFamily_quadraticValue_mem (L : PositiveDefiniteIntegralLattice n)
    {u : Fin n → RationalFiniteAdele} (hu : u ∈ integralFiniteAdeleVectors n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue u ∈
      integralFiniteAdeleSubring := by
  simpa [finiteAdelicQuadraticFormValue] using
    L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring u u hu hu

private theorem standardFamily_dotProduct_scaled_nsmul
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) (m : ℕ)
    (x y : Fin n → RationalFiniteAdele) :
    dotProduct x (V.scaledFiniteAdelicPolarFrequency t (m • y)) =
      (algebraMap ℚ RationalFiniteAdele t * (m : RationalFiniteAdele)) *
        dotProduct x (V.finiteAdelicPolarMatrix.mulVec y) := by
  simp only [scaledFiniteAdelicPolarFrequency, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Closure under the standard quadratic phase -/

theorem isStandardCarried_quadraticPhase_mul
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f) :
    IsStandardCarried c
      (fun x => (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x) := by
  intro x hx
  show (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x = 0
  rw [hf x hx, mul_zero]

/-- The standard quadratic phase at a rational parameter keeps the family,
multiplying the period scale by the denominator and the carrier scale. -/
theorem isStandardPeriodic_quadraticPhase_mul
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {c d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    IsStandardPeriodic (t.den * c * d)
      (fun x => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
        f x) := by
  set m : ℕ := t.den * c * d with hm
  intro x u hu
  have humem : m • u ∈ integralFiniteAdeleVectors n :=
    nsmul_mem_integralFiniteAdeleVectors hu
  have hfx : f (x + m • u) = f x :=
    (hperiodic.mono ⟨t.den * c, by rw [hm]; ring⟩) x u hu
  by_cases hx : x ∈ standardDividedLattice n c
  · have hcx : c • x ∈ integralFiniteAdeleVectors n := hx
    have hmcast : (m : RationalFiniteAdele) =
        (t.den : RationalFiniteAdele) *
          ((c : RationalFiniteAdele) * (d : RationalFiniteAdele)) := by
      rw [hm]
      push_cast
      ring
    have h1 : L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t (m • u) = 1 := by
      unfold rationalFiniteAdeleQuadraticPhase
      apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
      rw [standardFamily_quadraticFormValue_nsmul]
      have hrw : algebraMap ℚ RationalFiniteAdele t * ((m : RationalFiniteAdele) ^ 2 *
          L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue u) =
          (algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ^ 2) *
            (((c : RationalFiniteAdele) * (d : RationalFiniteAdele)) ^ 2 *
              L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue u) := by
        rw [hmcast]; ring
      rw [hrw]
      refine integralFiniteAdeleSubring.mul_mem
        (standardFamily_den_sq_coefficient_mem t) (integralFiniteAdeleSubring.mul_mem ?_ ?_)
      · exact integralFiniteAdeleSubring.pow_mem
          (integralFiniteAdeleSubring.mul_mem (standardFamily_natCast_mem c)
            (standardFamily_natCast_mem d)) 2
      · exact standardFamily_quadraticValue_mem L hu
    have h2 : rationalFiniteAdeleVectorPairingChar x
        (L.rationalQuadraticSpaceMatrix.scaledFiniteAdelicPolarFrequency t (m • u)) = 1 := by
      unfold rationalFiniteAdeleVectorPairingChar
      apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
      rw [standardFamily_dotProduct_scaled_nsmul]
      have hpair : (c : RationalFiniteAdele) *
          dotProduct x (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec u) ∈
          integralFiniteAdeleSubring := by
        rw [← nsmul_dotProduct_eq]
        exact standardFamily_polarPairing_mem L hcx hu
      have hrw : algebraMap ℚ RationalFiniteAdele t * (m : RationalFiniteAdele) *
          dotProduct x (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec u) =
          ((algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele)) *
              (d : RationalFiniteAdele)) *
            ((c : RationalFiniteAdele) *
              dotProduct x (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec u)) := by
        rw [hmcast]; ring
      rw [hrw]
      exact integralFiniteAdeleSubring.mul_mem
        (integralFiniteAdeleSubring.mul_mem (standardFamily_den_coefficient_mem t)
          (standardFamily_natCast_mem d)) hpair
    show (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t (x + m • u) : ℂ) *
      f (x + m • u) =
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x
    rw [hfx, rationalFiniteAdeleQuadraticPhase_add, h1, h2, mul_one, mul_one]
  · have hx' : x + m • u ∉ standardDividedLattice n c := by
      intro hmem
      refine hx ?_
      have hsplit : c • x = c • (x + m • u) - (c * m) • u := by
        rw [smul_add, ← mul_nsmul' u c m]
        abel
      show c • x ∈ integralFiniteAdeleVectors n
      rw [hsplit]
      intro i
      exact integralFiniteAdeleSubring.sub_mem (hmem i)
        (nsmul_mem_integralFiniteAdeleVectors (m := c * m) hu i)
    show (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t (x + m • u) : ℂ) *
      f (x + m • u) =
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x
    rw [hcarried x hx, hcarried _ hx', mul_zero, mul_zero]

/-! ## Closure under the actual finite Fourier transform -/

local instance rationalFiniteAdeleCoordinateAddHaarMeasure_isAddLeftInvariant''
    (e : ℕ) :
    Measure.IsAddLeftInvariant (rationalFiniteAdeleCoordinateAddHaarMeasure e) := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  refine ⟨fun z => ?_⟩
  change Measure.map (fun x => z + x)
      (Measure.pi fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure) =
    Measure.pi fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure
  exact (measurePreserving_pi
    (fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure)
    (fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure)
    (fun i => measurePreserving_add_left rationalFiniteAdeleAddHaarMeasure (z i))).map_eq

/-- The literal finite Fourier output, with the existing coordinate Haar and
the native negative kernel. -/
def standardFiniteFourier (f : (Fin n → RationalFiniteAdele) → ℂ)
    (w : Fin n → RationalFiniteAdele) : ℂ :=
  ∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f x
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

theorem standardFiniteFourier_eq_fourierIntegral
    (f : (Fin n → RationalFiniteAdele) → ℂ) (w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier f w =
      Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n) f w := by
  rw [Fourier.fourierIntegral_def, standardFiniteFourier]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hchar : rationalFiniteAdeleCoordinateFourierChar n (-(x * w)) =
      rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
    rw [show -(x * w) = x * (-w) by rw [mul_neg],
      rationalFiniteAdeleCoordinateFourierChar_mul_eq_dotProduct]
    unfold rationalFiniteAdeleVectorPairingChar
    rw [dotProduct_neg]
  rw [hchar, Circle.smul_def, smul_eq_mul]

/-- The standard-test output is this transform applied to the
phase-twisted standard indicator. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_eq_standardFiniteFourier
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) (w : Fin n → RationalFiniteAdele) :
    V.rationalFiniteAdeleQuadraticGaussFourier t w =
      standardFiniteFourier (fun x =>
        (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x) w := by
  rw [rationalFiniteAdeleQuadraticGaussFourier, standardFiniteFourier]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [rationalFiniteAdeleQuadraticGaussFourierIntegrand, mul_assoc]

/-- A carried test has a periodic transform, with the same scale. -/
theorem IsStandardCarried.isStandardPeriodic_standardFiniteFourier {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f) :
    IsStandardPeriodic c (standardFiniteFourier f) := by
  intro w u hu
  unfold standardFiniteFourier
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ standardDividedLattice n c
  · have hcx : c • x ∈ integralFiniteAdeleVectors n := hx
    have hint : dotProduct x (c • u) ∈ integralFiniteAdeleSubring := by
      rw [dotProduct_nsmul_comm, dotProduct]
      exact Subring.sum_mem integralFiniteAdeleSubring fun i _ =>
        integralFiniteAdeleSubring.mul_mem (hcx i) (hu i)
    have hone : rationalFiniteAdeleFourierChar (-(dotProduct x (c • u))) = 1 := by
      rw [AddChar.map_neg_eq_inv,
        rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hint, inv_one]
    have hsplit : rationalFiniteAdeleFourierChar (-(dotProduct x (w + c • u))) =
        rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
      rw [dotProduct_add, neg_add, AddChar.map_add_eq_mul, hone, mul_one]
    rw [hsplit]
  · rw [hf x hx, mul_zero, mul_zero]

/-- A periodic test has a carried transform, with the same scale. -/
theorem IsStandardPeriodic.isStandardCarried_standardFiniteFourier {d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f) :
    IsStandardCarried d (standardFiniteFourier f) := by
  intro w hw
  obtain ⟨z, hz, hzne⟩ : ∃ z ∈ integralFiniteAdeleVectors n,
      rationalFiniteAdeleVectorPairingChar z (d • w) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((rationalFiniteAdeleVector_integral_annihilator_iff (d • w)).mp hcon)
  have hcirc : rationalFiniteAdeleFourierChar (-(dotProduct (d • z) w)) ≠ 1 := by
    rw [← dotProduct_nsmul_comm, AddChar.map_neg_eq_inv]
    simpa [rationalFiniteAdeleVectorPairingChar] using hzne
  have hcne : ((rationalFiniteAdeleFourierChar (-(dotProduct (d • z) w)) : Circle) : ℂ) ≠ 1 :=
    fun h => hcirc (Subtype.ext h)
  have hshift := integral_add_right_eq_self
    (μ := rationalFiniteAdeleCoordinateAddHaarMeasure n)
    (fun x => (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f x) (d • z)
  have hfix : standardFiniteFourier f w =
      ((rationalFiniteAdeleFourierChar (-(dotProduct (d • z) w)) : Circle) : ℂ) *
        standardFiniteFourier f w := by
    calc standardFiniteFourier f w
        = ∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct (x + d • z) w)) : ℂ) *
            f (x + d • z) ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := hshift.symm
      _ = ∫ x, ((rationalFiniteAdeleFourierChar (-(dotProduct (d • z) w)) : Circle) : ℂ) *
            ((rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f x)
            ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [hf x z hz, add_dotProduct, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
          ring
      _ = ((rationalFiniteAdeleFourierChar (-(dotProduct (d • z) w)) : Circle) : ℂ) *
            standardFiniteFourier f w := integral_const_mul _ _
  have hzero : (1 - ((rationalFiniteAdeleFourierChar (-(dotProduct (d • z) w)) : Circle) : ℂ)) *
      standardFiniteFourier f w = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero_of_eq hfix
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h).symm hcne
  · exact h

/-! ## Closure under the actual finite generator -/

/-- Phase at a rational parameter followed by the actual finite Fourier
transform keeps the family, with explicit new scales. -/
theorem isStandardPeriodic_finiteWeylUnipotent
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hcarried : IsStandardCarried c f) :
    IsStandardPeriodic c (standardFiniteFourier
      (fun x => (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x)) :=
  (isStandardCarried_quadraticPhase_mul V t hcarried).isStandardPeriodic_standardFiniteFourier

theorem isStandardCarried_finiteWeylUnipotent
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {c d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    IsStandardCarried (t.den * c * d) (standardFiniteFourier
      (fun x => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
        f x)) :=
  (isStandardPeriodic_quadraticPhase_mul L t hcarried
    hperiodic).isStandardCarried_standardFiniteFourier

/-- The generator output is again genuinely L1 for the existing finite Haar. -/
theorem integrable_finiteWeylUnipotent
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    Integrable (standardFiniteFourier
      (fun x => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
        f x)) (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
  integrable_of_isStandardCarried_isStandardPeriodic
    (mul_ne_zero (mul_ne_zero t.den_nz hc) hd) hc
    (isStandardCarried_finiteWeylUnipotent L t hcarried hperiodic)
    (isStandardPeriodic_finiteWeylUnipotent L.rationalQuadraticSpaceMatrix t hcarried)

/-! ## The standard test as the base case -/

/-- The carrier statement for the standard test is the
`(1,1)` case of the general generator closure. -/
theorem isStandardCarried_rationalFiniteAdeleQuadraticGaussFourier
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    IsStandardCarried t.den
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t) := by
  have h := isStandardCarried_finiteWeylUnipotent L t
    isStandardCarried_integralIndicator isStandardPeriodic_integralIndicator
  rw [mul_one, mul_one] at h
  intro w hw
  rw [rationalFiniteAdeleQuadraticGaussFourier_eq_standardFiniteFourier]
  exact h w hw

/-- The frequency periodicity for the standard test is the
`(1,1)` case of the general generator closure. -/
theorem isStandardPeriodic_rationalFiniteAdeleQuadraticGaussFourier
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    IsStandardPeriodic 1 (V.rationalFiniteAdeleQuadraticGaussFourier t) := by
  have h := isStandardPeriodic_finiteWeylUnipotent V t isStandardCarried_integralIndicator
  intro w u hu
  rw [rationalFiniteAdeleQuadraticGaussFourier_eq_standardFiniteFourier,
    rationalFiniteAdeleQuadraticGaussFourier_eq_standardFiniteFourier]
  exact h w u hu

end RationalQuadraticSpaceMatrix
