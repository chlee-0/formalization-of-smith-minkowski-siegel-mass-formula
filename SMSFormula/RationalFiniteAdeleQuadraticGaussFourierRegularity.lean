import SMSFormula.RationalFiniteAdeleQuadraticGaussStandardQuotient

/-!
# Finite Fourier-output regularity of the standard quadratic Gauss test

The finite factor of the actual adelic Weyl-after-phase operator applied to the
standard integral-lattice test is the phase-twisted finite Fourier integral

```text
  F(w) = ∫ psi(-(x . w)) * psi(t * Q(x)) * 1_(Zhat^n)(x) dx.
```

This file proves that `F` lands back in the compact-open locally constant class,
using only the existing finite coordinate Haar measure, the existing standard
quadratic phase and the already certified self-annihilating property of the
standard lattice.  Three facts are established.

* `F` is invariant under every integral translation of the frequency, hence
  locally constant; the period lattice is the standard lattice itself.
* `F` vanishes unless `t.den * w` is integral, so `F` is supported in the
  compact set `t.den⁻¹ * Zhat^n`.
* On that support the integrand descends to the literal finite quotient
  `Zhat^n / t.den * Zhat^n`, so `F(w)` is an exact `t.den^n`-term average.

No Haar measure is rescaled, no cutoff subgroup is selected, no residue
representative or section is chosen, and no self-dual normalization, conductor,
Poisson summation, or inversion statement is asserted here.  The real factor,
the global product over the required operator orbit, and the common Theta/E
phase remain outside this file.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Standard lattice topology -/

theorem integralFiniteAdeleVectors_eq_univ_pi (d : ℕ) :
    integralFiniteAdeleVectors d =
      Set.univ.pi fun _ : Fin d =>
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  ext x
  simp [integralFiniteAdeleVectors]

theorem isOpen_integralFiniteAdeleVectors (d : ℕ) :
    IsOpen (integralFiniteAdeleVectors d) := by
  rw [integralFiniteAdeleVectors_eq_univ_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integralFiniteAdeleSubring

theorem isCompact_integralFiniteAdeleVectors (d : ℕ) :
    IsCompact (integralFiniteAdeleVectors d) := by
  rw [integralFiniteAdeleVectors_eq_univ_pi]
  exact isCompact_univ_pi fun _ => isCompact_integralFiniteAdeleSubring

theorem nsmul_mem_integralFiniteAdeleVectors {d m : ℕ}
    {z : Fin d → RationalFiniteAdele} (hz : z ∈ integralFiniteAdeleVectors d) :
    m • z ∈ integralFiniteAdeleVectors d := fun i =>
  integralFiniteAdeleSubring.nsmul_mem (hz i) m

theorem rationalFiniteAdeleVectorIntegralIndicator_add_of_mem
    (x : Fin n → RationalFiniteAdele) {z : Fin n → RationalFiniteAdele}
    (hz : z ∈ integralFiniteAdeleVectors n) :
    rationalFiniteAdeleVectorIntegralIndicator (x + z) =
      rationalFiniteAdeleVectorIntegralIndicator x := by
  unfold rationalFiniteAdeleVectorIntegralIndicator
  exact Finset.prod_congr rfl fun i _ =>
    rationalFiniteAdeleIntegralIndicator_add_of_mem (x i) (z i) (hz i)

local instance rationalFiniteAdeleCoordinateAddHaarMeasure_isAddLeftInvariant'
    (d : ℕ) :
    Measure.IsAddLeftInvariant
      (rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  refine ⟨fun z => ?_⟩
  change Measure.map (fun x => z + x)
      (Measure.pi fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure) =
    Measure.pi fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure
  exact (measurePreserving_pi
    (fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure)
    (fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure)
    (fun i => measurePreserving_add_left rationalFiniteAdeleAddHaarMeasure (z i))).map_eq

/-! ## The phase-twisted finite Fourier output -/

/-- The actual finite Fourier integrand of the phase-twisted standard-lattice
test.  The negative kernel and the existing standard phase are literal. -/
def rationalFiniteAdeleQuadraticGaussFourierIntegrand
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (w x : Fin n → RationalFiniteAdele) : ℂ :=
  (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) *
      (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
    rationalFiniteAdeleVectorIntegralIndicator x

/-- The phase-twisted finite Fourier output at a frequency `w`. -/
def rationalFiniteAdeleQuadraticGaussFourier
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (w : Fin n → RationalFiniteAdele) : ℂ :=
  ∫ x, V.rationalFiniteAdeleQuadraticGaussFourierIntegrand t w x
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

/-- The output is the actual existing finite Fourier integral of the
phase-twisted standard-lattice test; no new transform is introduced. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_eq_fourierIntegral
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (w : Fin n → RationalFiniteAdele) :
    V.rationalFiniteAdeleQuadraticGaussFourier t w =
      Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)
        (fun x => (V.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x) w := by
  rw [Fourier.fourierIntegral_def, rationalFiniteAdeleQuadraticGaussFourier]
  apply integral_congr_ae
  filter_upwards with x
  have hchar : rationalFiniteAdeleCoordinateFourierChar n (-(x * w)) =
      rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
    rw [show -(x * w) = x * (-w) by rw [mul_neg],
      rationalFiniteAdeleCoordinateFourierChar_mul_eq_dotProduct]
    unfold rationalFiniteAdeleVectorPairingChar
    rw [dotProduct_neg]
  simp only [rationalFiniteAdeleQuadraticGaussFourierIntegrand, hchar,
    Circle.smul_def, smul_eq_mul, mul_assoc]

/-- At the zero frequency the output is the existing standard finite quadratic
Gauss integral. -/
@[simp]
theorem rationalFiniteAdeleQuadraticGaussFourier_zero
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    V.rationalFiniteAdeleQuadraticGaussFourier t 0 =
      V.rationalFiniteAdeleQuadraticGaussIntegral t := by
  rw [rationalFiniteAdeleQuadraticGaussFourier,
    rationalFiniteAdeleQuadraticGaussIntegral]
  apply integral_congr_ae
  filter_upwards with x
  simp [rationalFiniteAdeleQuadraticGaussFourierIntegrand, dotProduct]

/-- The integrand is genuinely L1 at every frequency. -/
theorem integrable_rationalFiniteAdeleQuadraticGaussFourierIntegrand
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (w : Fin n → RationalFiniteAdele) :
    Integrable (V.rationalFiniteAdeleQuadraticGaussFourierIntegrand t w)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hkernel : Continuous fun x : Fin n → RationalFiniteAdele =>
      rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
    apply continuous_rationalFiniteAdeleFourierChar.comp
    fun_prop
  have hphase : Continuous (V.rationalFiniteAdeleQuadraticPhase t) := by
    unfold rationalFiniteAdeleQuadraticPhase finiteAdelicQuadraticFormValue
    apply continuous_rationalFiniteAdeleFourierChar.comp
    fun_prop
  apply (integrable_rationalFiniteAdeleVectorIntegralIndicator n).bdd_mul
  · exact (hkernel.subtype_val.mul hphase.subtype_val).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul]

/-! ## Integral periodicity of the frequency -/

/-- Translating the frequency by the standard lattice does not change the
integrand, because the integrand is carried by the standard lattice. -/
theorem rationalFiniteAdeleQuadraticGaussFourierIntegrand_frequency_add
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (w : Fin n → RationalFiniteAdele) {u : Fin n → RationalFiniteAdele}
    (hu : u ∈ integralFiniteAdeleVectors n)
    (x : Fin n → RationalFiniteAdele) :
    V.rationalFiniteAdeleQuadraticGaussFourierIntegrand t (w + u) x =
      V.rationalFiniteAdeleQuadraticGaussFourierIntegrand t w x := by
  unfold rationalFiniteAdeleQuadraticGaussFourierIntegrand
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · have hpair : rationalFiniteAdeleFourierChar (-(dotProduct x u)) = 1 := by
      rw [show -(dotProduct x u) = dotProduct x (-u) by rw [dotProduct_neg]]
      apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
      rw [dotProduct]
      exact Subring.sum_mem integralFiniteAdeleSubring fun i _ =>
        integralFiniteAdeleSubring.mul_mem (hx i)
          (integralFiniteAdeleSubring.neg_mem (hu i))
    have hsplit : rationalFiniteAdeleFourierChar (-(dotProduct x (w + u))) =
        rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
      rw [dotProduct_add, neg_add, AddChar.map_add_eq_mul, hpair, mul_one]
    rw [hsplit]
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
    ring

/-- The finite Fourier output is periodic under the standard lattice.  This is
the exact finite-place local constancy of the output. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_frequency_add
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ)
    (w : Fin n → RationalFiniteAdele) {u : Fin n → RationalFiniteAdele}
    (hu : u ∈ integralFiniteAdeleVectors n) :
    V.rationalFiniteAdeleQuadraticGaussFourier t (w + u) =
      V.rationalFiniteAdeleQuadraticGaussFourier t w := by
  unfold rationalFiniteAdeleQuadraticGaussFourier
  exact integral_congr_ae (by
    filter_upwards with x
    exact V.rationalFiniteAdeleQuadraticGaussFourierIntegrand_frequency_add t w hu x)

/-- The finite Fourier output is locally constant. -/
theorem isLocallyConstant_rationalFiniteAdeleQuadraticGaussFourier
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    IsLocallyConstant (V.rationalFiniteAdeleQuadraticGaussFourier t) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro w
  refine ⟨(fun y => y - w) ⁻¹' integralFiniteAdeleVectors n,
    (isOpen_integralFiniteAdeleVectors n).preimage (by fun_prop), ?_, ?_⟩
  · show w - w ∈ integralFiniteAdeleVectors n
    rw [sub_self]
    intro i
    simp
  · intro y hy
    have hmem : y - w ∈ integralFiniteAdeleVectors n := hy
    have := V.rationalFiniteAdeleQuadraticGaussFourier_frequency_add t w hmem
    rwa [add_sub_cancel] at this


/-! ## Denominator periodicity and the exact compact carrier -/

private theorem gaussFourier_quadraticFormValue_nsmul
    (V : RationalQuadraticSpaceMatrix n) (m : ℕ)
    (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (m • x) =
      (m : RationalFiniteAdele) ^ 2 * V.finiteAdelicQuadraticFormValue x := by
  simp only [finiteAdelicQuadraticFormValue, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  ring_nf

private theorem gaussFourier_den_coefficient_mem (t : ℚ) :
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

private theorem gaussFourier_den_sq_coefficient_mem (t : ℚ) :
    algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ^ 2 ∈
      integralFiniteAdeleSubring := by
  rw [pow_two, ← mul_assoc]
  exact integralFiniteAdeleSubring.mul_mem (gaussFourier_den_coefficient_mem t)
    (by exact_mod_cast integer_mem_integralFiniteAdeleSubring (t.den : ℤ))

private theorem gaussFourier_polarPairing_mem (L : PositiveDefiniteIntegralLattice n)
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

private theorem gaussFourier_dotProduct_scaled_nsmul
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

/-- Ambient denominator periodicity of the standard quadratic phase on the
standard lattice.  This is the existing subtype periodicity, stated for the
ambient finite-adelic vectors that the Fourier integrand actually uses. -/
theorem rationalFiniteAdeleQuadraticPhase_add_denDilation_of_mem
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    {x z : Fin n → RationalFiniteAdele}
    (hx : x ∈ integralFiniteAdeleVectors n)
    (hz : z ∈ integralFiniteAdeleVectors n) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
        (x + t.den • z) =
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x := by
  have hq : L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue z ∈
      integralFiniteAdeleSubring := by
    simpa [finiteAdelicQuadraticFormValue] using
      L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring z z hz hz
  have hphase :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
        (t.den • z) = 1 := by
    unfold rationalFiniteAdeleQuadraticPhase
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [gaussFourier_quadraticFormValue_nsmul]
    simpa [mul_assoc] using integralFiniteAdeleSubring.mul_mem
      (gaussFourier_den_sq_coefficient_mem t) hq
  have hpair :
      rationalFiniteAdeleVectorPairingChar x
        (L.rationalQuadraticSpaceMatrix.scaledFiniteAdelicPolarFrequency t
          (t.den • z)) = 1 := by
    unfold rationalFiniteAdeleVectorPairingChar
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [gaussFourier_dotProduct_scaled_nsmul]
    exact integralFiniteAdeleSubring.mul_mem (gaussFourier_den_coefficient_mem t)
      (gaussFourier_polarPairing_mem L hx hz)
  rw [rationalFiniteAdeleQuadraticPhase_add, hphase, hpair, mul_one, mul_one]

/-- Translating the integration variable by the denominator dilation of the
standard lattice multiplies the integrand by the exact residual character. -/
theorem rationalFiniteAdeleQuadraticGaussFourierIntegrand_add_denDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (w : Fin n → RationalFiniteAdele)
    {z : Fin n → RationalFiniteAdele} (hz : z ∈ integralFiniteAdeleVectors n)
    (x : Fin n → RationalFiniteAdele) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand
        t w (x + t.den • z) =
      (rationalFiniteAdeleFourierChar (-(dotProduct (t.den • z) w)) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand
          t w x := by
  have hu : t.den • z ∈ integralFiniteAdeleVectors n :=
    nsmul_mem_integralFiniteAdeleVectors hz
  unfold rationalFiniteAdeleQuadraticGaussFourierIntegrand
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [rationalFiniteAdeleVectorIntegralIndicator_add_of_mem x hu,
      rationalFiniteAdeleQuadraticPhase_add_denDilation_of_mem L t hx hz,
      add_dotProduct, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · have hxu : x + t.den • z ∉ integralFiniteAdeleVectors n := by
      intro h
      exact hx fun i => by
        simpa using integralFiniteAdeleSubring.sub_mem (h i) (hu i)
    rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hxu,
      rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
    ring

/-- The finite Fourier output is unchanged by the residual character of every
denominator-dilated standard lattice vector. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_denDilation_character
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (w : Fin n → RationalFiniteAdele)
    {z : Fin n → RationalFiniteAdele} (hz : z ∈ integralFiniteAdeleVectors n) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w =
      (rationalFiniteAdeleFourierChar (-(dotProduct (t.den • z) w)) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w := by
  have hshift :
      (∫ x, L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand
            t w (x + t.den • z)
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
        ∫ x, L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand
            t w x ∂rationalFiniteAdeleCoordinateAddHaarMeasure n :=
    integral_add_right_eq_self _ _
  calc
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w =
        ∫ x, L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand
          t w (x + t.den • z) ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := hshift.symm
    _ = ∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct (t.den • z) w)) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand
            t w x ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact rationalFiniteAdeleQuadraticGaussFourierIntegrand_add_denDilation L t w hz x
    _ = (rationalFiniteAdeleFourierChar (-(dotProduct (t.den • z) w)) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w :=
        integral_const_mul _ _

/-- The exact carrier of the finite Fourier output: the frequencies whose
denominator dilate is standard-integral. -/
def rationalFiniteAdeleQuadraticGaussFourierCarrier (n : ℕ) (t : ℚ) :
    Set (Fin n → RationalFiniteAdele) :=
  {w | t.den • w ∈ integralFiniteAdeleVectors n}

private theorem gaussFourier_dotProduct_nsmul_comm (m : ℕ)
    (z w : Fin n → RationalFiniteAdele) :
    dotProduct (m • z) w = dotProduct z (m • w) := by
  simp only [dotProduct, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The finite Fourier output vanishes off its exact carrier. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_eq_zero_of_not_mem_carrier
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {w : Fin n → RationalFiniteAdele}
    (hw : w ∉ rationalFiniteAdeleQuadraticGaussFourierCarrier n t) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w = 0 := by
  obtain ⟨z, hz, hzne⟩ : ∃ z ∈ integralFiniteAdeleVectors n,
      rationalFiniteAdeleVectorPairingChar z (t.den • w) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((rationalFiniteAdeleVector_integral_annihilator_iff (t.den • w)).mp hcon)
  have hcirc : rationalFiniteAdeleFourierChar (-(dotProduct (t.den • z) w)) ≠ 1 := by
    rw [gaussFourier_dotProduct_nsmul_comm, AddChar.map_neg_eq_inv]
    simpa [rationalFiniteAdeleVectorPairingChar] using hzne
  have hcne : ((rationalFiniteAdeleFourierChar (-(dotProduct (t.den • z) w)) : Circle) : ℂ) ≠ 1 :=
    fun h => hcirc (Subtype.ext h)
  have hfix := rationalFiniteAdeleQuadraticGaussFourier_denDilation_character L t w hz
  have hzero : (1 - ((rationalFiniteAdeleFourierChar
        (-(dotProduct (t.den • z) w)) : Circle) : ℂ)) *
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero_of_eq hfix
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h).symm hcne
  · exact h

/-- The support of the finite Fourier output is contained in its exact
carrier. -/
theorem support_rationalFiniteAdeleQuadraticGaussFourier_subset
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    Function.support
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t) ⊆
      rationalFiniteAdeleQuadraticGaussFourierCarrier n t := by
  intro w hw
  by_contra hcon
  exact hw (rationalFiniteAdeleQuadraticGaussFourier_eq_zero_of_not_mem_carrier L t hcon)

/-- The carrier is compact: it is the denominator contraction of the standard
lattice.  No Haar measure is rescaled and no cutoff subgroup is chosen. -/
theorem isCompact_rationalFiniteAdeleQuadraticGaussFourierCarrier (d : ℕ) (t : ℚ) :
    IsCompact (rationalFiniteAdeleQuadraticGaussFourierCarrier d t) := by
  have hden : ((t.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr t.den_nz
  set c : RationalFiniteAdele := algebraMap ℚ RationalFiniteAdele ((t.den : ℚ))⁻¹ with hcdef
  have hcast : (t.den : RationalFiniteAdele) =
      algebraMap ℚ RationalFiniteAdele ((t.den : ℚ)) := by norm_num
  have hcd : (t.den : RationalFiniteAdele) * c = 1 := by
    rw [hcdef, hcast, ← map_mul, mul_inv_cancel₀ hden, map_one]
  have himage : rationalFiniteAdeleQuadraticGaussFourierCarrier d t =
      (fun y : Fin d → RationalFiniteAdele => fun i => c * y i) ''
        integralFiniteAdeleVectors d := by
    ext w
    constructor
    · intro hw
      refine ⟨t.den • w, hw, ?_⟩
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [← mul_assoc, mul_comm c, hcd, one_mul]
    · rintro ⟨y, hy, rfl⟩
      intro i
      have : (t.den : RationalFiniteAdele) * (c * y i) = y i := by
        rw [← mul_assoc, hcd, one_mul]
      simpa [nsmul_eq_mul, this] using hy i
  rw [himage]
  refine (isCompact_integralFiniteAdeleVectors d).image ?_
  exact continuous_pi fun i => continuous_const.mul (continuous_apply i)

/-! ## Exact finite-quotient evaluation on the carrier -/

/-- The finite Fourier integrand restricted to the standard lattice, as a
function on the integral finite-adelic coordinate subtype. -/
def rationalFiniteAdeleQuadraticGaussFourierIntegralPhase
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (w : Fin n → RationalFiniteAdele)
    (x : Fin n → IntegralFiniteAdele) : ℂ :=
  (rationalFiniteAdeleFourierChar
      (-(dotProduct (fun i => (x i : RationalFiniteAdele)) w)) : ℂ) *
    (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
      (fun i => (x i : RationalFiniteAdele)) : ℂ)

/-- The ambient finite Fourier output is the subtype integral of the restricted
integrand.  The existing measure-preserving inclusion is used; no Haar measure
is rescaled. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_eq_integralPhaseIntegral
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (w : Fin n → RationalFiniteAdele) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w =
      ∫ x : Fin n → IntegralFiniteAdele,
        rationalFiniteAdeleQuadraticGaussFourierIntegralPhase L t w x
        ∂integralFiniteAdeleCoordinateAddHaarMeasure n := by
  have hcont : Continuous (fun x : Fin n → RationalFiniteAdele =>
      (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) *
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ)) := by
    have hkernel : Continuous fun x : Fin n → RationalFiniteAdele =>
        rationalFiniteAdeleFourierChar (-(dotProduct x w)) := by
      apply continuous_rationalFiniteAdeleFourierChar.comp
      fun_prop
    have hphase : Continuous
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t) := by
      unfold rationalFiniteAdeleQuadraticPhase finiteAdelicQuadraticFormValue
      apply continuous_rationalFiniteAdeleFourierChar.comp
      fun_prop
    exact hkernel.subtype_val.mul hphase.subtype_val
  have hind :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourierIntegrand t w =
        (integralFiniteAdeleVectors n).indicator (fun x =>
          (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) *
            (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ)) := by
    funext x
    unfold rationalFiniteAdeleQuadraticGaussFourierIntegrand
    by_cases hx : x ∈ integralFiniteAdeleVectors n
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx]
      simp [hx]
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx]
      simp [hx]
  rw [rationalFiniteAdeleQuadraticGaussFourier, hind,
    integral_indicator (measurableSet_integralFiniteAdeleVectors n),
    ← (measurePreserving_integralFiniteAdeleCoordinateCoe n).map_eq,
    integral_map (measurePreserving_integralFiniteAdeleCoordinateCoe n).aemeasurable
      hcont.aestronglyMeasurable]
  rfl

/-- On the carrier the restricted integrand is genuinely periodic modulo the
denominator dilation of the standard lattice. -/
theorem rationalFiniteAdeleQuadraticGaussFourierIntegralPhase_add_denDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {w : Fin n → RationalFiniteAdele}
    (hw : w ∈ rationalFiniteAdeleQuadraticGaussFourierCarrier n t)
    (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈ (integralFiniteAdeleCoordinateNatDilation n t.den).range) :
    rationalFiniteAdeleQuadraticGaussFourierIntegralPhase L t w (x + z) =
      rationalFiniteAdeleQuadraticGaussFourierIntegralPhase L t w x := by
  obtain ⟨y, rfl⟩ := hz
  let xa : Fin n → RationalFiniteAdele := fun i => (x i : RationalFiniteAdele)
  let ya : Fin n → RationalFiniteAdele := fun i => (y i : RationalFiniteAdele)
  have hxa : xa ∈ integralFiniteAdeleVectors n := fun i => (x i).property
  have hya : ya ∈ integralFiniteAdeleVectors n := fun i => (y i).property
  have harg :
      (fun i => (((x + integralFiniteAdeleCoordinateNatDilation n t.den y) i :
        IntegralFiniteAdele) : RationalFiniteAdele)) = xa + t.den • ya := rfl
  have hchar : rationalFiniteAdeleFourierChar (-(dotProduct (t.den • ya) w)) = 1 := by
    rw [gaussFourier_dotProduct_nsmul_comm,
      show -(dotProduct ya (t.den • w)) = dotProduct ya (-(t.den • w)) by
        rw [dotProduct_neg]]
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [dotProduct]
    exact Subring.sum_mem integralFiniteAdeleSubring fun i _ =>
      integralFiniteAdeleSubring.mul_mem (hya i)
        (integralFiniteAdeleSubring.neg_mem (hw i))
  have hcharEq :
      rationalFiniteAdeleFourierChar (-(dotProduct (xa + t.den • ya) w)) =
        rationalFiniteAdeleFourierChar (-(dotProduct xa w)) := by
    rw [add_dotProduct, neg_add, AddChar.map_add_eq_mul, hchar, mul_one]
  unfold rationalFiniteAdeleQuadraticGaussFourierIntegralPhase
  rw [harg, rationalFiniteAdeleQuadraticPhase_add_denDilation_of_mem L t hxa hya,
    hcharEq]

private instance rationalFiniteAdeleQuadraticGaussFourierDenNeZero (t : ℚ) :
    NeZero t.den := ⟨t.den_nz⟩

/-- Exact finite-quotient evaluation of the phase-twisted finite Fourier output
at every frequency of its carrier.  The quotient is literal and no residue
representative or section is chosen. -/
theorem rationalFiniteAdeleQuadraticGaussFourier_eq_denQuotientSum
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {w : Fin n → RationalFiniteAdele}
    (hw : w ∈ rationalFiniteAdeleQuadraticGaussFourierCarrier n t) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussFourier t w =
      (((t.den : ℝ) ^ n : ℂ)⁻¹) *
        ∑ q, addQuotientPeriodicLift
          (integralFiniteAdeleCoordinateNatDilation n t.den).range
          (rationalFiniteAdeleQuadraticGaussFourierIntegralPhase L t w)
          (rationalFiniteAdeleQuadraticGaussFourierIntegralPhase_add_denDilation L t hw) q := by
  rw [rationalFiniteAdeleQuadraticGaussFourier_eq_integralPhaseIntegral L t w]
  exact integralFiniteAdeleCoordinate_integral_periodic_eq_inv_pow_sum
    n t.den (rationalFiniteAdeleQuadraticGaussFourierIntegralPhase L t w)
    (rationalFiniteAdeleQuadraticGaussFourierIntegralPhase_add_denDilation L t hw)

end RationalQuadraticSpaceMatrix
