import SMSFormula.ValueDensityPositiveFunctional
import SMSFormula.AdelicL1Composition

/-!
# The adelic value density of a product test is a real density times a finite one

The value density `d_Phi = F_A(B_A(Phi))` is the adelic Fourier transform of the existing
adelic Bruhat coefficient.  For a product test `Phi_inf(x_inf) Phi_fin(x_fin)`, the existing
product-test factorization writes `B_A(Phi)(u)` as the real local coefficient at the literal
real scalar of `u` times the finite local coefficient at `u_f`.  The existing global character
is the archimedean factor times the finite one and the existing adelic Haar is the product of the
fixed infinite and finite Haars, so

```text
d_Phi(w) = d_inf(Phi_inf)(w_inf) * d_fin(Phi_fin)(w_f),
```

with `d_inf` the real Fourier integral on `ℝ` of the real coefficient and `d_fin` the
finite-adelic Fourier integral of the finite coefficient.  Neither factor is evaluated.  In
particular no Euler product over the finite places, no Fourier inversion and no normalization of
either local factor is asserted; only the product is intrinsic, and the split of a constant
between the two factors is fixed by these literal definitions, not by any chosen measure.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The real local Bruhat coefficient at a real scalar `s`. -/
def realLocalBruhatCoefficient (V : RationalQuadraticSpaceMatrix n)
    (PhiInf : (Fin n → ℝ) → ℂ) (s : ℝ) : ℂ :=
  ∫ x : Fin n → ℝ,
    ((Real.fourierChar (s * V.realQuadraticFormValue x) : Circle) : ℂ) * PhiInf x
    ∂(volume : Measure (Fin n → ℝ))

/-- The finite local Bruhat coefficient at a finite-adelic scalar `y`. -/
def finiteLocalBruhatCoefficient (V : RationalQuadraticSpaceMatrix n)
    (PhiFin : (Fin n → RationalFiniteAdele) → ℂ) (y : RationalFiniteAdele) : ℂ :=
  ∫ x : Fin n → RationalFiniteAdele,
    ((V.rationalFiniteAdeleQuadraticPhaseAt y x : Circle) : ℂ) * PhiFin x
    ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)

/-- The real local value density: the real Fourier integral of the real coefficient. -/
def realLocalValueDensity (V : RationalQuadraticSpaceMatrix n)
    (PhiInf : (Fin n → ℝ) → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ, ((Real.fourierChar (-(s * t)) : Circle) : ℂ) *
    V.realLocalBruhatCoefficient PhiInf s

/-- The finite local value density: the finite-adelic Fourier integral of the finite
coefficient against the existing finite character and finite Haar. -/
def finiteLocalValueDensity (V : RationalQuadraticSpaceMatrix n)
    (PhiFin : (Fin n → RationalFiniteAdele) → ℂ) (z : RationalFiniteAdele) : ℂ :=
  ∫ y : RationalFiniteAdele, ((rationalFiniteAdeleFourierChar (-(y * z)) : Circle) : ℂ) *
    V.finiteLocalBruhatCoefficient PhiFin y ∂rationalFiniteAdeleAddHaarMeasure

/-- The literal real scalar of a product is the product of the real scalars. -/
theorem rationalAdeleRealScalar_mul (u w : RationalAdele) :
    rationalAdeleRealScalar (u * w) =
      rationalAdeleRealScalar u * rationalAdeleRealScalar w := by
  change rationalInfiniteAdeleRingEquivReal (u.1 * w.1) =
    rationalInfiniteAdeleRingEquivReal u.1 * rationalInfiniteAdeleRingEquivReal w.1
  exact map_mul _ _ _

/-- The existing global character at `-(u*w)` is the real character at the product of the real
scalars times the finite character at `-(u_f*w_f)`. -/
theorem rationalAdeleFourierChar_neg_mul_eq_real_mul_finite (u w : RationalAdele) :
    ((rationalAdeleFourierChar (-(u * w)) : Circle) : ℂ) =
      ((Real.fourierChar (-(rationalAdeleRealScalar u * rationalAdeleRealScalar w)) :
          Circle) : ℂ) *
        ((rationalFiniteAdeleFourierChar (-(u.2 * w.2)) : Circle) : ℂ) := by
  rw [rationalAdeleFourierChar_apply, rationalAdeleArchimedeanFourierChar_apply,
    Circle.coe_mul]
  congr 3
  · change rationalAdeleRealScalar (-(u * w)) = _
    rw [show rationalAdeleRealScalar (-(u * w)) = -rationalAdeleRealScalar (u * w) from
      map_neg rationalInfiniteAdeleContinuousAddEquivReal (u * w).1,
      rationalAdeleRealScalar_mul]

set_option maxHeartbeats 1000000 in
/-- The value density of a product test is a local product: the adelic Fourier density of
`Phi_inf(x_inf) Phi_fin(x_fin)` at `w` is the real local density at the literal real scalar of
`w` times the finite local density at `w_f`.  No integrability hypothesis is needed, since
`integral_prod_mul` carries none. -/
theorem complexValueFourierDensity_productTest (V : RationalQuadraticSpaceMatrix n)
    (PhiInf : (Fin n → ℝ) → ℂ) (PhiFin : (Fin n → RationalFiniteAdele) → ℂ)
    (w : RationalAdele) :
    V.complexValueFourierDensity
        (fun x ↦ PhiInf (rationalAdeleVectorRealPart n x) *
          PhiFin (rationalAdeleVectorFinitePart n x)) w =
      V.realLocalValueDensity PhiInf (rationalAdeleRealScalar w) *
        V.finiteLocalValueDensity PhiFin w.2 := by
  let gr : RationalInfiniteAdele → ℂ := fun v ↦
    ((Real.fourierChar (-(rationalInfiniteAdeleContinuousAddEquivReal v *
        rationalAdeleRealScalar w)) : Circle) : ℂ) *
      V.realLocalBruhatCoefficient PhiInf (rationalInfiniteAdeleContinuousAddEquivReal v)
  let gf : RationalFiniteAdele → ℂ := fun y ↦
    ((rationalFiniteAdeleFourierChar (-(y * w.2)) : Circle) : ℂ) *
      V.finiteLocalBruhatCoefficient PhiFin y
  have hpoint : ∀ u : RationalAdele,
      rationalAdeleFourierChar (-(u * w)) •
          V.rationalAdeleRankOneAdelicBruhatCoefficient
            (fun x ↦ PhiInf (rationalAdeleVectorRealPart n x) *
              PhiFin (rationalAdeleVectorFinitePart n x)) u =
        gr u.1 * gf u.2 := by
    intro u
    rw [Circle.smul_def, smul_eq_mul, rationalAdeleFourierChar_neg_mul_eq_real_mul_finite,
      rationalAdeleRankOneAdelicBruhatCoefficient_productTest V u PhiInf PhiFin]
    simp only [gr, gf, realLocalBruhatCoefficient, finiteLocalBruhatCoefficient,
      rationalAdeleRealScalar]
    ring
  rw [complexValueFourierDensity, Fourier.fourierIntegral_def,
    integral_congr_ae (Filter.Eventually.of_forall hpoint),
    rationalAdeleAddHaarMeasure_eq_prod]
  change (∫ z : RationalInfiniteAdele × RationalFiniteAdele, gr z.1 * gf z.2
    ∂rationalInfiniteAdeleAddHaarMeasure.prod rationalFiniteAdeleAddHaarMeasure) = _
  rw [integral_prod_mul gr gf, integral_infiniteAdele_eq_integral_real]
  simp only [gr, ContinuousAddEquiv.apply_symm_apply]
  rfl

/-- The finite local coefficient of the standard integral indicator is the existing finite
quadratic Gauss integral. -/
@[simp]
theorem finiteLocalBruhatCoefficient_integralIndicator (V : RationalQuadraticSpaceMatrix n)
    (y : RationalFiniteAdele) :
    V.finiteLocalBruhatCoefficient rationalFiniteAdeleVectorIntegralIndicator y =
      V.rationalFiniteAdeleQuadraticGaussIntegralAt y :=
  rfl

/-- The concrete polar Gaussian--lattice test: its value density is the real local density of
the polar Gaussian at the literal real scalar times the finite Fourier integral of the existing
finite quadratic Gauss integral. -/
theorem complexValueFourierDensity_polarGaussianLattice (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (w : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L b) w =
      L.rationalQuadraticSpaceMatrix.realLocalValueDensity (polarRealGaussian L b)
          (rationalAdeleRealScalar w) *
        L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          rationalFiniteAdeleVectorIntegralIndicator w.2 :=
  complexValueFourierDensity_productTest _ _ _ w

end RationalQuadraticSpaceMatrix

end
