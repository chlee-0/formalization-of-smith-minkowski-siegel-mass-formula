import SMSFormula.RationalFiniteAdeleStandardFamilyCosetFourier
import SMSFormula.RationalFiniteAdeleStandardFamilyRationalDiagonal
import SMSFormula.RationalAdelePolarGaussianScaledLatticeSummability

/-!
# The transform of a family member on the `N`-divided rational diagonal

Poisson for the family reduces to a comparison of two rational-diagonal
lattice sums.  This file settles the dual side of that comparison.

The transform of a scale-one family member has scales `(N, 1)`, so the diagonal
collapse applies to it on the literal `N`-divided lattice.  On
that lattice the support condition of every piece transform is automatically
satisfied, because `N` times the `N`-divided diagonal is the integer diagonal.
The transform therefore becomes a pure character sum: exactly `N^-n` times the
discrete Fourier transform of the descent over the literal finite quotient.

The dual character descends to that quotient by the quotient eliminator, so no
residue representative or section is chosen.  No Poisson identity or theta
transformation is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Scales of the transform -/

/-- The transform of a scale-one family member has scales `(N, 1)`: it is
carried by the `N`-divided lattice and periodic modulo the standard one. -/
theorem standardFiniteFourier_scales {N : ℕ}
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic N g) :
    IsStandardCarried N (standardFiniteFourier g) ∧
      IsStandardPeriodic 1 (standardFiniteFourier g) :=
  ⟨hperiodic.isStandardCarried_standardFiniteFourier,
    hcarried.isStandardPeriodic_standardFiniteFourier⟩

/-! ## The divided diagonal -/

theorem nsmul_rationalScaledIntegerVector_diagonal {N : ℕ} (hN : N ≠ 0)
    (k : Fin n → ℤ) :
    N • rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector N k) =
      rationalFiniteAdeleVectorDiagonal n (fun i => ((k i : ℤ) : ℚ)) := by
  have hq : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  funext i
  show (N : ℕ) • algebraMap ℚ RationalFiniteAdele (((k i : ℤ) : ℚ) / ((N : ℚ))) =
    algebraMap ℚ RationalFiniteAdele (((k i : ℤ) : ℚ))
  rw [nsmul_eq_mul, show (N : RationalFiniteAdele) =
    algebraMap ℚ RationalFiniteAdele ((N : ℚ)) by norm_num, ← map_mul]
  congr 1
  field_simp

theorem integerDiagonal_mem_integralFiniteAdeleVectors (k : Fin n → ℤ) :
    rationalFiniteAdeleVectorDiagonal n (fun i => ((k i : ℤ) : ℚ)) ∈
      integralFiniteAdeleVectors n := fun i =>
  (rational_mem_integralFiniteAdeleSubring_iff (((k i : ℤ) : ℚ))).mpr ⟨k i, rfl⟩

/-! ## The dual character on the literal quotient -/

private theorem standardDualChar_periodic (n : ℕ) {N : ℕ} (hN : N ≠ 0)
    (k : Fin n → ℤ)
    (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈ (integralFiniteAdeleCoordinateNatDilation n N).range) :
    (rationalFiniteAdeleFourierChar
        (-(dotProduct (fun i => (((x + z) i : IntegralFiniteAdele) : RationalFiniteAdele))
          (rationalFiniteAdeleVectorDiagonal n
            (rationalScaledIntegerVector N k)))) : ℂ) =
      (rationalFiniteAdeleFourierChar
        (-(dotProduct (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele))
          (rationalFiniteAdeleVectorDiagonal n
            (rationalScaledIntegerVector N k)))) : ℂ) := by
  obtain ⟨w, rfl⟩ := hz
  have harg :
      (fun i => (((x + integralFiniteAdeleCoordinateNatDilation n N w) i :
        IntegralFiniteAdele) : RationalFiniteAdele)) =
      (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele)) +
        N • (fun i => ((w i : IntegralFiniteAdele) : RationalFiniteAdele)) := rfl
  have hone : rationalFiniteAdeleFourierChar
      (-(dotProduct (N • (fun i => ((w i : IntegralFiniteAdele) : RationalFiniteAdele)))
        (rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector N k)))) = 1 := by
    rw [← dotProduct_nsmul_comm, nsmul_rationalScaledIntegerVector_diagonal hN,
      AddChar.map_neg_eq_inv]
    have hmem : dotProduct (fun i => ((w i : IntegralFiniteAdele) : RationalFiniteAdele))
        (rationalFiniteAdeleVectorDiagonal n (fun i => ((k i : ℤ) : ℚ))) ∈
        integralFiniteAdeleSubring := by
      rw [dotProduct]
      exact Subring.sum_mem integralFiniteAdeleSubring fun i _ =>
        integralFiniteAdeleSubring.mul_mem (w i).property
          (integerDiagonal_mem_integralFiniteAdeleVectors k i)
    rw [rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hmem, inv_one]
  rw [harg, add_dotProduct, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hone]
  simp

/-- The dual character at an `N`-divided integer frequency, descended to the
literal quotient by the quotient eliminator.  No representative is stored. -/
def standardQuotientDualChar (n : ℕ) {N : ℕ} (hN : N ≠ 0) (k : Fin n → ℤ) :
    ((Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) → ℂ :=
  addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n N).range
    (fun y => (rationalFiniteAdeleFourierChar
      (-(dotProduct (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele))
        (rationalFiniteAdeleVectorDiagonal n
          (rationalScaledIntegerVector N k)))) : ℂ))
    (standardDualChar_periodic n hN k)

@[simp]
theorem standardQuotientDualChar_coe (n : ℕ) {N : ℕ} (hN : N ≠ 0) (k : Fin n → ℤ)
    (y : Fin n → IntegralFiniteAdele) :
    standardQuotientDualChar n hN k
        (y : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range) =
      (rationalFiniteAdeleFourierChar
        (-(dotProduct (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele))
          (rationalFiniteAdeleVectorDiagonal n
            (rationalScaledIntegerVector N k)))) : ℂ) := rfl

/-! ## The transform on the divided diagonal is a pure character sum -/

/-- On the literal `N`-divided rational diagonal the actual finite Fourier
transform of a scale-one family member is exactly `N^-n` times the discrete
Fourier transform of its descent over the literal finite quotient.  Every
support condition is automatically satisfied there. -/
theorem standardFiniteFourier_rationalScaledIntegerDiagonal (n : ℕ) {N : ℕ}
    [NeZero N] (hq : ((N : ℚ))⁻¹ ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic N g)
    (k : Fin n → ℤ) :
    standardFiniteFourier g
        (rationalFiniteAdeleVectorDiagonal n (rationalScaledIntegerVector N k)) =
      ((N : ℂ))⁻¹ ^ n *
        ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
          standardQuotientDualChar n (NeZero.ne N) k alpha := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [standardFiniteFourier_eq_sum_cosetFourier hcarried hperiodic, Finset.mul_sum]
  refine Finset.sum_congr rfl fun alpha _ => ?_
  induction alpha using Quotient.inductionOn' with
  | _ y =>
    rw [standardFiniteFourier_standardCosetIndicator n hN hq y,
      nsmul_rationalScaledIntegerVector_diagonal hN,
      rationalFiniteAdeleVectorIntegralIndicator_of_mem
        (integerDiagonal_mem_integralFiniteAdeleVectors k),
      standardQuotientDualChar_coe]
    ring

/-! ## Reduction of the diagonal sum to the coset pieces -/

/-- The rational-diagonal sum of a family member against any supplied real
factor is the finite combination of the corresponding coset sums.  Only
linearity of the unordered sum is used. -/
theorem tsum_rationalDiagonal_eq_sum_coset {N : ℕ} [NeZero N]
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic N g)
    (G : (Fin n → ℚ) → ℂ)
    (hsum : ∀ alpha, Summable fun q : Fin n → ℚ =>
      G q * standardCosetIndicator n N alpha (rationalFiniteAdeleVectorDiagonal n q)) :
    (∑' q : Fin n → ℚ, G q * g (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        ∑' q : Fin n → ℚ, G q *
          standardCosetIndicator n N alpha (rationalFiniteAdeleVectorDiagonal n q) := by
  have hpoint : ∀ q : Fin n → ℚ,
      G q * g (rationalFiniteAdeleVectorDiagonal n q) =
      ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        (G q * standardCosetIndicator n N alpha
          (rationalFiniteAdeleVectorDiagonal n q)) := by
    intro q
    conv_lhs => rw [standardScaleOne_eq_sum_cosetIndicator hcarried hperiodic]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun alpha _ => by ring
  rw [tsum_congr hpoint,
    Summable.tsum_finsetSum fun alpha _ => (hsum alpha).mul_left _]
  exact Finset.sum_congr rfl fun alpha _ => tsum_mul_left

/-- For the polar Gaussian real factor the summability hypothesis holds,
so the reduction needs no extra hypothesis. -/
theorem tsum_polarGaussian_rationalDiagonal_eq_sum_coset
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} [NeZero N]
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic N g) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        g (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
        ∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
          standardCosetIndicator n N alpha
            (rationalFiniteAdeleVectorDiagonal n q) := by
  have hN : N ≠ 0 := NeZero.ne N
  refine tsum_rationalDiagonal_eq_sum_coset hcarried hperiodic _ fun alpha => ?_
  have hsum := summable_rationalAdeleVectorDiagonal_polarGaussianTensor L hb
    one_ne_zero hN (isStandardCarried_standardCosetIndicator n N alpha)
    (isStandardPeriodic_standardCosetIndicator n hN alpha)
  simpa only [rationalAdeleVectorRealPart_rationalDiagonal,
    rationalAdeleVectorFinitePart_diagonal] using hsum

end RationalQuadraticSpaceMatrix
