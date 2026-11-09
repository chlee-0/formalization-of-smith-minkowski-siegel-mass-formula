import SMSFormula.RationalFiniteAdeleStandardFamilyIntegerCongruence
import SMSFormula.RationalAdeleVectorComplexGaussianTheta

/-!
# The integer congruence-class sum as a centered matrix theta sum

The Poisson summation step that remains is a statement about `Z^n` alone: the
shifted Euclidean theta identity for one integer congruence class.  This file
puts its left side into the input format of the existing shifted theta
results.

Two steps, both elementary.  The congruence class is the range of the
injection `k |-> m' + N * k`, so the class sum reindexes to a full `Z^n` sum of
shifted values.  The shifted polar Gaussian value is then the existing complex
centered matrix-Gaussian summand for the real polar matrix, at width
`b * N^2` and center `-m'/N`, by the width-change identity.

No theta identity is proved here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The congruence class is a literal shifted lattice -/

/-- The injection whose range is the congruence class of `m'` modulo `N`. -/
def integerCongruenceShift (N : ℕ) (m' : Fin n → ℤ) (k : Fin n → ℤ) : Fin n → ℤ :=
  fun i => m' i + (N : ℤ) * k i

theorem injective_integerCongruenceShift {N : ℕ} (hN : N ≠ 0) (m' : Fin n → ℤ) :
    Function.Injective (integerCongruenceShift (n := n) N m') := by
  intro k k' h
  funext i
  have hi : m' i + (N : ℤ) * k i = m' i + (N : ℤ) * k' i := congrFun h i
  have hN' : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hN
  exact mul_left_cancel₀ hN' (by linarith)

theorem integerCongruenceIndicator_shift {N : ℕ} (m' k : Fin n → ℤ) :
    integerCongruenceIndicator n N m' (integerCongruenceShift N m' k) = 1 := by
  rw [integerCongruenceIndicator, if_pos]
  intro i
  exact ⟨k i, by simp [integerCongruenceShift]⟩

theorem support_integerCongruenceIndicator_subset {N : ℕ} (m' : Fin n → ℤ)
    (G : (Fin n → ℤ) → ℂ) :
    Function.support (fun m : Fin n → ℤ => G m * integerCongruenceIndicator n N m' m) ⊆
      Set.range (integerCongruenceShift (n := n) N m') := by
  classical
  intro m hm
  by_contra hcon
  refine hm ?_
  have hdvd : ¬ ∀ i, (N : ℤ) ∣ (m i - m' i) := by
    intro hdvd
    refine hcon ⟨fun i => (hdvd i).choose, ?_⟩
    funext i
    have hi := (hdvd i).choose_spec
    show m' i + (N : ℤ) * (hdvd i).choose = m i
    omega
  show G m * integerCongruenceIndicator n N m' m = 0
  rw [integerCongruenceIndicator, if_neg hdvd, mul_zero]

/-- The congruence-class sum is the literal shifted lattice sum. -/
theorem tsum_integerCongruenceIndicator {N : ℕ} (hN : N ≠ 0) (m' : Fin n → ℤ)
    (G : (Fin n → ℤ) → ℂ) :
    (∑' m : Fin n → ℤ, G m * integerCongruenceIndicator n N m' m) =
      ∑' k : Fin n → ℤ, G (integerCongruenceShift N m' k) := by
  rw [← (injective_integerCongruenceShift hN m').tsum_eq
    (support_integerCongruenceIndicator_subset m' G)]
  exact tsum_congr fun k => by
    rw [integerCongruenceIndicator_shift, mul_one]

/-! ## The shifted polar Gaussian is a centered matrix summand -/

theorem polarRealGaussian_eq_exp_polar (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (x : Fin n → ℝ) :
    polarRealGaussian L b x =
      Complex.exp (-Real.pi * b *
        ((x ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec x : ℝ) : ℂ)) := by
  rw [polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct,
    L.dotProduct_polarRealSqrtMatrix_mulVec]

/-- Scaling the argument by `N` is the width change `b |-> b * N^2`. -/
theorem polarRealGaussian_nsmul (L : PositiveDefiniteIntegralLattice n) (b : ℂ) {N : ℕ} (hN : N ≠ 0)
    (y : Fin n → ℝ) :
    polarRealGaussian L b (fun i => (N : ℝ) * y i) =
      polarRealGaussian L (b * ((N : ℂ)) ^ 2) y := by
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNC : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdiv := polarRealGaussian_div L (b * ((N : ℂ)) ^ 2) hNR (fun i => (N : ℝ) * y i)
  have harg : (fun i => ((N : ℝ) * y i) / (N : ℝ)) = y := by
    funext i
    field_simp
  rw [harg] at hdiv
  rw [hdiv]
  congr 1
  push_cast
  field_simp

/-- The shifted polar Gaussian value is the existing complex centered
matrix-Gaussian summand, at width `b * N^2` and center `-m'/N`.  This is exactly
the input format of the repository's shifted theta machinery. -/
theorem polarRealGaussian_integerCongruenceShift (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    {N : ℕ} (hN : N ≠ 0) (m' k : Fin n → ℤ) :
    polarRealGaussian L b
        (rationalRealVector n (fun i => ((integerCongruenceShift N m' k i : ℤ) : ℚ))) =
      complexCenteredMatrixGaussianSummand
        L.rationalQuadraticSpaceMatrix.realPolarMatrix (b * ((N : ℂ)) ^ 2)
        (fun i => -((m' i : ℝ) / (N : ℝ))) k := by
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have harg : rationalRealVector n
      (fun i => ((integerCongruenceShift N m' k i : ℤ) : ℚ)) =
      fun i => (N : ℝ) * (((m' i : ℝ) / (N : ℝ)) + (k i : ℝ)) := by
    funext i
    show (((m' i + (N : ℤ) * k i : ℤ) : ℚ) : ℝ) = _
    push_cast
    field_simp
  have hvec : (fun i => ((m' i : ℝ) / (N : ℝ)) + (k i : ℝ)) =
      (fun i => (k i : ℝ) - -((m' i : ℝ) / (N : ℝ))) := by
    funext i
    ring
  rw [harg, polarRealGaussian_nsmul L b hN, polarRealGaussian_eq_exp_polar, hvec]
  simp [complexCenteredMatrixGaussianSummand]

/-- The integer congruence-class sum of the polar Gaussian is a centered matrix
theta sum.  The remaining Poisson summation step is therefore a statement
about that theta sum. -/
theorem tsum_integerCongruence_polarGaussian (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    {N : ℕ} (hN : N ≠ 0) (m' : Fin n → ℤ) :
    (∑' m : Fin n → ℤ,
        polarRealGaussian L b (rationalRealVector n (fun i => ((m i : ℤ) : ℚ))) *
          integerCongruenceIndicator n N m' m) =
      ∑' k : Fin n → ℤ,
        complexCenteredMatrixGaussianSummand
          L.rationalQuadraticSpaceMatrix.realPolarMatrix (b * ((N : ℂ)) ^ 2)
          (fun i => -((m' i : ℝ) / (N : ℝ))) k := by
  rw [tsum_integerCongruenceIndicator hN m'
    (fun m => polarRealGaussian L b (rationalRealVector n (fun i => ((m i : ℤ) : ℚ))))]
  exact tsum_congr fun k => polarRealGaussian_integerCongruenceShift L b hN m' k

end RationalQuadraticSpaceMatrix
