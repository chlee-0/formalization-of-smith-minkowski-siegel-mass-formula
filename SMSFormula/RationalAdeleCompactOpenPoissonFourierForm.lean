import SMSFormula.RationalAdeleDilationTransportPoisson
import SMSFormula.RationalFiniteAdeleStandardFamilyCosetFourier

/-!
# The Gaussian--Compact-OPEN Poisson identity, in genuine Fourier form

The previous files proved Poisson for the polar Gaussian times a subgroup-carrier indicator with
the dual side written as a sum of class-indicator transforms.  That sum is exactly what the
existing `standardFiniteFourier_eq_sum_cosetFourier` evaluates: for a function standard carried at
one and standard periodic at `N`, the finite Fourier transform is that sum.  Running it backwards
collapses the dual side to the actual finite Fourier transform of the carrier indicator.

The result, in the repository's own terms:
`sum_q R(q) 1_K(q_f) = sum_q F_real(R)(q) F_fin(1_K)(q_f)`,
with no class decomposition visible and no hypothesis beyond a positive width and a nonzero level --
both for a carrier inside the integral vectors and, after the dilation transport, for the wider
sandwich the translated test actually has.

Negative scope: the dual side is the coordinate finite transform, not the polar Weyl operator, and
the wide form is at the transported width `b / N^2` with the scaled carrier.  Converting to
`Theta_Phi(g) = Theta_(W Phi)(g)` still needs the polar/coordinate comparison and the width undone.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Poisson in Fourier form for a carrier inside the integral vectors. -/
theorem tsum_polarGaussian_subgroupIndicator_poisson_fourier
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) [NeZero N]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hK : K ⊆ integralFiniteAdeleVectors n)
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hNK : ∀ u ∈ integralFiniteAdeleVectors n, (N • u : Fin n → RationalFiniteAdele) ∈ K) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
            (rationalRealVector n q) *
          standardFiniteFourier (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
            (rationalFiniteAdeleVectorDiagonal n q) := by
  rw [tsum_polarGaussian_subgroupIndicator_poisson L hb hN hK hadd hneg hNK]
  refine tsum_congr fun q ↦ ?_
  rw [standardFiniteFourier_eq_sum_cosetFourier (isStandardCarried_one_indicator hK)
    (isStandardPeriodic_indicator hadd hneg hNK)]

/-- Poisson in Fourier form at the wider sandwich -- the shape the translated test has.  The width
is the transported `b / N^2` and the carrier is the scaled one; both are explicit. -/
theorem tsum_polarGaussian_wideSandwichCarrier_poisson_fourier
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) [NeZero (N * N)]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hlow : ∀ u ∈ integralFiniteAdeleVectors n,
      (fun i ↦ (N : RationalFiniteAdele) * u i) ∈ K)
    (hhigh : ∀ y ∈ K, (fun i ↦ (N : RationalFiniteAdele) * y i) ∈
      integralFiniteAdeleVectors n) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' p : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume
            (polarRealGaussian L (b / ((N : ℝ) : ℂ) ^ 2)) (rationalRealVector n p) *
          standardFiniteFourier
            ((scaledCarrier N K).indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
            (rationalFiniteAdeleVectorDiagonal n p) := by
  rw [tsum_polarGaussian_wideSandwichCarrier_poisson L hb hN hadd hneg hlow hhigh]
  refine tsum_congr fun p ↦ ?_
  rw [standardFiniteFourier_eq_sum_cosetFourier
    (isStandardCarried_one_indicator (scaledCarrier_subset hhigh))
    (isStandardPeriodic_indicator (add_mem_scaledCarrier hadd) (neg_mem_scaledCarrier hneg)
      (nsmul_mem_scaledCarrier hlow))]

end RationalQuadraticSpaceMatrix

end
