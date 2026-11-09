import SMSFormula.RationalAdeleCongruenceClassPoisson
import SMSFormula.RationalAdelePolarGaussianScaledLatticeSummability
import SMSFormula.RationalAdeleVectorComplexGaussianTheta

/-!
# Finite linearity of the congruence-class Poisson identity

The goal is adelic Poisson summation at a Gaussian times the indicator of a compact open additive
subgroup `K` of the finite adele vectors, since that is the carrier of the translated test.

`tsum_polarGaussian_standardCoset_poisson` proves the rational-diagonal Poisson identity for the
polar Gaussian times the indicator of one class of `N` times the integral finite adele vectors,
with the real and finite Fourier transforms and no representative function.

A compact open `K` sandwiched between `N` times the integral vectors and the integral vectors is a
finite union of such classes, so its indicator is a finite sum of class indicators.  This file
proves the resulting finite linearity step and the summability inputs it needs.  The sandwich
itself is not proved here, and no compact open subgroup is decomposed.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The finite class group at level `N`: the quotient of the integral finite adele vectors by
their `N`-th dilation.  This is the existing quotient the coset indicators are indexed by. -/
abbrev StandardClass (n N : ℕ) :=
  (Fin n → IntegralFiniteAdele) ⧸ (integralFiniteAdeleCoordinateNatDilation n N).range

/-- Finite linearity in the weak form, which needs no summability hypothesis at all: a finite
combination of the per-class identities. -/
theorem sum_tsum_polarGaussian_finiteCosetCombination_poisson
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0)
    (S : Finset (StandardClass n N)) (c : StandardClass n N → ℂ) :
    (∑ α ∈ S, c α * ∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        standardCosetIndicator n N α (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑ α ∈ S, c α * ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
            (rationalRealVector n q) *
          standardFiniteFourier (standardCosetIndicator n N α)
            (rationalFiniteAdeleVectorDiagonal n q) :=
  Finset.sum_congr rfl fun α _ ↦ by
    rw [tsum_polarGaussian_standardCoset_poisson L hb hN α]

/-- The left summability input is discharged: the coset indicator is standard carried at `1` and
standard periodic at `N`, and the polar Gaussian is absolutely summable along the integer lattice. -/
theorem summable_polarGaussian_standardCosetIndicator
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0)
    (α : StandardClass n N) :
    Summable fun q : Fin n → ℚ =>
      polarRealGaussian L b (rationalRealVector n q) *
        standardCosetIndicator n N α (rationalFiniteAdeleVectorDiagonal n q) :=
  summable_rationalDiagonal_mul one_ne_zero hN
    (isStandardCarried_standardCosetIndicator n N α)
    (isStandardPeriodic_standardCosetIndicator n hN α)
    (summable_norm_polarRealGaussian_rationalScaledIntegerVector L hb one_ne_zero)

/-- The dual real factor -- the actual real Fourier integral of the polar Gaussian -- is
absolutely summable along the `c`-divided integer lattice.  The inverse polar matrix is positive
definite and the inverse width has positive real part, so the existing complex centered matrix
Gaussian summability applies at width `b * c^2`. -/
theorem summable_norm_fourierIntegral_polarRealGaussian_rationalScaledIntegerVector
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {c : ℕ} (hc : c ≠ 0) :
    Summable fun m : Fin n → ℤ =>
      ‖Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
        (rationalRealVector n (rationalScaledIntegerVector c m))‖ := by
  have hS : L.rationalQuadraticSpaceMatrix.realPolarMatrix.PosDef :=
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef
  have hcne : ((c : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  set r : ℝ := ((c : ℝ)) ^ 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hb2 : 0 < (b * (r : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos hb hrpos
  have hmain := (summable_complexCenteredMatrixGaussianSummand_inv
    L.rationalQuadraticSpaceMatrix.realPolarMatrix hS hb2 (0 : Fin n → ℝ)).norm
  refine (hmain.mul_left ‖((L.polarRealDeterminantScale : ℂ))⁻¹ *
    realGaussianFourierCoefficient n b‖).congr ?_
  intro m
  rw [fourierIntegral_polarGaussian_eq_inverseMatrix_exp L hb, norm_mul]
  rw [norm_mul, norm_mul]
  congr 1
  rw [complexCenteredMatrixGaussianSummand]
  congr 1
  have hx : (fun i => ((m i : ℝ)) - (0 : Fin n → ℝ) i) = integerVectorReal m := by
    funext i
    simp [integerVectorReal]
  have hw : rationalRealVector n (rationalScaledIntegerVector c m) =
      ((c : ℝ))⁻¹ • integerVectorReal m := by
    funext i
    simp [rationalRealVector, rationalScaledIntegerVector, integerVectorReal,
      div_eq_inv_mul]
  have hquad : (rationalRealVector n (rationalScaledIntegerVector c m) ⬝ᵥ
        L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.mulVec
          (rationalRealVector n (rationalScaledIntegerVector c m))) =
      (integerVectorReal m ⬝ᵥ
        L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.mulVec (integerVectorReal m)) / r := by
    rw [hw, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, hrdef]
    field_simp
  rw [hx, hquad]
  push_cast
  have hrne : ((r : ℂ)) ≠ 0 := by
    simpa [hrdef] using (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos))
  field_simp

/-- The right summability input is discharged: the transform of the coset indicator is standard
carried at `N` and standard periodic at `1`, and the dual real factor is summable there. -/
theorem summable_fourierIntegral_polarGaussian_standardFiniteFourier_standardCoset
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0)
    (α : StandardClass n N) :
    Summable fun q : Fin n → ℚ =>
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
          (rationalRealVector n q) *
        standardFiniteFourier (standardCosetIndicator n N α)
          (rationalFiniteAdeleVectorDiagonal n q) :=
  summable_rationalDiagonal_mul hN one_ne_zero
    ((isStandardPeriodic_standardCosetIndicator n hN α).isStandardCarried_standardFiniteFourier)
    ((isStandardCarried_standardCosetIndicator n N α).isStandardPeriodic_standardFiniteFourier)
    (summable_norm_fourierIntegral_polarRealGaussian_rationalScaledIntegerVector L hb hN)

/-- Finite linearity of the class Poisson identity, with the two summability inputs explicit. -/
theorem tsum_polarGaussian_finiteCosetCombination_poisson
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0)
    (S : Finset (StandardClass n N)) (c : StandardClass n N → ℂ)
    (hL : ∀ α ∈ S, Summable fun q : Fin n → ℚ =>
      polarRealGaussian L b (rationalRealVector n q) *
        standardCosetIndicator n N α (rationalFiniteAdeleVectorDiagonal n q))
    (hR : ∀ α ∈ S, Summable fun q : Fin n → ℚ =>
      Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
          (rationalRealVector n q) *
        standardFiniteFourier (standardCosetIndicator n N α)
          (rationalFiniteAdeleVectorDiagonal n q)) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        ∑ α ∈ S, c α * standardCosetIndicator n N α
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
            (rationalRealVector n q) *
          ∑ α ∈ S, c α * standardFiniteFourier (standardCosetIndicator n N α)
            (rationalFiniteAdeleVectorDiagonal n q) := by
  have key : ∀ (R : (Fin n → ℚ) → ℂ) (F : StandardClass n N → (Fin n → ℚ) → ℂ),
      (∀ α ∈ S, Summable fun q ↦ R q * F α q) →
      (∑' q : Fin n → ℚ, R q * ∑ α ∈ S, c α * F α q) =
        ∑ α ∈ S, c α * ∑' q : Fin n → ℚ, R q * F α q := by
    intro R F h
    have hpoint : ∀ q : Fin n → ℚ,
        R q * ∑ α ∈ S, c α * F α q = ∑ α ∈ S, c α * (R q * F α q) := by
      intro q
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ ↦ by ring
    simp only [hpoint]
    rw [Summable.tsum_finsetSum fun α hα ↦ (h α hα).mul_left (c α)]
    exact Finset.sum_congr rfl fun α _ ↦ tsum_mul_left
  rw [key _ _ hL, key _ _ hR]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [tsum_polarGaussian_standardCoset_poisson L hb hN α]

/-- The headline, with no hypothesis beyond positive width and a nonzero level: rational-diagonal
Poisson summation holds for the polar Gaussian times any finite complex combination of level-`N`
class indicators, with the actual real and finite Fourier transforms.  A compact open carrier
sandwiched between `N` times the integral vectors and the integral vectors is such a combination,
so this is the required bridge -- reached by finite linearity, not by a new Jacobi
theorem. -/
theorem tsum_polarGaussian_cosetCombination_poisson
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0)
    (S : Finset (StandardClass n N)) (c : StandardClass n N → ℂ) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        ∑ α ∈ S, c α * standardCosetIndicator n N α
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
            (rationalRealVector n q) *
          ∑ α ∈ S, c α * standardFiniteFourier (standardCosetIndicator n N α)
            (rationalFiniteAdeleVectorDiagonal n q) :=
  tsum_polarGaussian_finiteCosetCombination_poisson L hb hN S c
    (fun α _ ↦ summable_polarGaussian_standardCosetIndicator L hb hN α)
    (fun α _ ↦ summable_fourierIntegral_polarGaussian_standardFiniteFourier_standardCoset
      L hb hN α)

end RationalQuadraticSpaceMatrix

end
