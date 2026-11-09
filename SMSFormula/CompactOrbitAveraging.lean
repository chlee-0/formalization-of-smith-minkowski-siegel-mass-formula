import SMSFormula.CompactOrbitComparison
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging identity for the compact-orbit comparison

The comparison has three parts. Positivity of the local masses and propagation from one open set
to the whole space are proved elsewhere. This file supplies the third, the averaging identity.
It is the only place any analysis happens, and the reason the argument avoids a quotient-measure
development entirely.

The two steps, and why the inverse is kept. Write `A_f = int_K f(k^-1 . x_0) dk` against the
probability Haar measure of the compact group.  (1) The average is constant on the orbit: at
`k_0 . x_0` the substitution `k = k_0 l` returns it to `A_f`.  Keeping the inverse is what makes this
a left translation, so only left invariance is used and no right-invariance or modular character is
needed.  (2) The mass identity: for a finite invariant measure the
integral of `f` is its total mass times the average.  Invariance makes the inner integral independent
of `k`, the Haar measure being a probability turns the outer integral into an identity, and one
Fubini exchange on a product of finite measures does the rest.

Why this closes the comparison.  Applied to the restrictions of two invariant measures to the same
compact open orbit, the average `A_f` is the same number for both, so the two integrals differ
exactly by the two masses -- which is the proportionality the propagation step then spreads over the
whole shell.  The scalar is never normalised away: it appears as the two masses and stays there.

Scope: the compact group here is auxiliary, not the acting group, and
normalising its Haar measure is not normalising the unknown Spin volume.  Nothing is adelic, no
compact open subgroup is constructed, and the identity
`Lambda(1_U) = mu_nat(U)` is not proved here -- an average is not an evaluation.
-/

namespace SMSFormula.CompactOrbit

open MeasureTheory Set
open scoped ENNReal

variable {K X : Type*} [Group K] [MeasurableSpace K] [MeasurableMul K] [MeasurableSpace X]
  [MulAction K X] [MeasurableConstSMul K X]

/-! ## The average is constant on the orbit -/

omit [MeasurableSpace X] [MeasurableConstSMul K X] in
/-- The orbit-constancy of the answer's (3.2).  The inverse in the integrand is what turns the change
of variables into a left translation, so only left invariance of the Haar measure is consumed -- no
right invariance and no modular character. -/
theorem average_const_on_orbit (haar : Measure K) [haar.IsMulLeftInvariant] (f : X → ℝ) (x₀ : X)
    (k₀ : K) : ∫ k, f (k⁻¹ • (k₀ • x₀)) ∂haar = ∫ k, f (k⁻¹ • x₀) ∂haar := by
  have hpt : ∀ l : K, f ((k₀ * l)⁻¹ • (k₀ • x₀)) = f (l⁻¹ • x₀) := by
    intro l
    congr 1
    rw [mul_inv_rev, mul_smul, inv_smul_smul]
  calc ∫ k, f (k⁻¹ • (k₀ • x₀)) ∂haar
      = ∫ l, f ((k₀ * l)⁻¹ • (k₀ • x₀)) ∂haar :=
        (integral_mul_left_eq_self (fun k ↦ f (k⁻¹ • (k₀ • x₀))) k₀).symm
    _ = ∫ l, f (l⁻¹ • x₀) ∂haar := by simp only [hpt]

/-! ## Restricting to a stable set preserves invariance -/

omit [MeasurableSpace K] [MeasurableMul K] [MeasurableConstSMul K X] in
/-- The restriction of an invariant measure to a stable measurable set is invariant.  This is what
lets the averaging identity be applied to `mu.restrict U` without constructing a measure on the orbit
as a subtype. -/
theorem smulInvariantMeasure_restrict (μ : Measure X) [SMulInvariantMeasure K X μ] {U : Set X}
    (hUm : MeasurableSet U) (hU : ∀ k : K, (fun x : X ↦ k • x) ⁻¹' U = U) :
    SMulInvariantMeasure K X (μ.restrict U) := by
  refine ⟨fun k s _ ↦ ?_⟩
  rw [Measure.restrict_apply' hUm, Measure.restrict_apply' hUm]
  have hset : (fun x : X ↦ k • x) ⁻¹' s ∩ U = (fun x : X ↦ k • x) ⁻¹' (s ∩ U) := by
    rw [Set.preimage_inter, hU k]
  rw [hset]
  exact measure_preimage_smul μ k (s ∩ U)

/-! ## The mass identity -/

omit [MeasurableMul K] in
/-- The averaging identity of the answer's (3.3): against a finite invariant measure, the integral of
`f` is the total mass times the average `A_f`.  Invariance makes the inner integral independent of
`k`; the Haar measure being a probability collapses the outer one; and one Fubini exchange on a
product of finite measures supplies the swap.  The mass is never divided out. -/
theorem integral_eq_mass_mul_average (haar : Measure K) [IsProbabilityMeasure haar]
    (eta : Measure X) [IsFiniteMeasure eta] [SMulInvariantMeasure K X eta] {f : X → ℝ} {c : ℝ}
    (hjoint : Measurable fun p : K × X ↦ f (p.1⁻¹ • p.2)) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hconst : ∀ᵐ x ∂eta, (∫ k, f (k⁻¹ • x) ∂haar) = c) :
    ∫ x, f x ∂eta = eta.real Set.univ * c := by
  have hint : Integrable (Function.uncurry fun k x ↦ f (k⁻¹ • x)) (haar.prod eta) := by
    refine (integrable_const C).mono' hjoint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p ↦ ?_)
    simpa [Function.uncurry, Real.norm_eq_abs] using hC (p.1⁻¹ • p.2)
  have hswap : ∫ k, (∫ x, f (k⁻¹ • x) ∂eta) ∂haar = ∫ x, (∫ k, f (k⁻¹ • x) ∂haar) ∂eta :=
    integral_integral_swap hint
  have hinner : ∀ k : K, ∫ x, f (k⁻¹ • x) ∂eta = ∫ x, f x ∂eta := fun k ↦
    integral_smul_eq_self f
  have hleft : ∫ k, (∫ x, f (k⁻¹ • x) ∂eta) ∂haar = ∫ x, f x ∂eta := by
    simp only [hinner]
    simp
  have hright : ∫ x, (∫ k, f (k⁻¹ • x) ∂haar) ∂eta = eta.real Set.univ * c := by
    rw [integral_congr_ae hconst, integral_const, smul_eq_mul]
  rw [← hleft, hswap, hright]

/-! ## The comparison on the orbit -/

omit [MeasurableMul K] in
/-- The comparison on one compact open orbit, in the cross-multiplied form the answer boxes.  The two
measures are integrated against the same `f` and produce the same average, so the two integrals
differ exactly by the two masses.  No division, no normalisation. -/
theorem measure_mul_integral_eq (haar : Measure K) [IsProbabilityMeasure haar]
    (eta theta : Measure X) [IsFiniteMeasure eta] [IsFiniteMeasure theta]
    [SMulInvariantMeasure K X eta] [SMulInvariantMeasure K X theta] {f : X → ℝ} {c : ℝ}
    (hjoint : Measurable fun p : K × X ↦ f (p.1⁻¹ • p.2)) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (heta : ∀ᵐ x ∂eta, (∫ k, f (k⁻¹ • x) ∂haar) = c)
    (htheta : ∀ᵐ x ∂theta, (∫ k, f (k⁻¹ • x) ∂haar) = c) :
    theta.real Set.univ * (∫ x, f x ∂eta) = eta.real Set.univ * (∫ x, f x ∂theta) := by
  rw [integral_eq_mass_mul_average haar eta hjoint hC heta,
    integral_eq_mass_mul_average haar theta hjoint hC htheta]
  ring

end SMSFormula.CompactOrbit
