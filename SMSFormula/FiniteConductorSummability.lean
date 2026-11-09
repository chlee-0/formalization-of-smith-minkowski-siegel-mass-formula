import SMSFormula.FiniteQuadraticSumModulusBound
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Totient

/-!
# Finite-conductor summability

`FiniteQuadraticSumModulusBound` bounds the character sum at one conductor.  Here the sum over all
conductors of the conductor-`q` contribution is shown to converge, summed by conductor, not by
primes, so no Euler product, no multiplicativity
and no prime-indexed restricted product appears anywhere below.

Two pieces.  First the normalisation: the one-conductor bound is for the raw sum `sum_w psi(Q w)`,
and the quantity that actually occurs is that sum divided by `q^n`; the squared bound transports to
`‖G_q‖^2 <= (q^n)^-1 |det H|^n`, with the conductor now in the denominator.

Then the summability: for a family indexed by the conductor with that squared bound and a
multiplicity at most `phi(q)`, the series converges as soon as the rank exceeds four.  The
comparison is with the `p`-series at exponent `n/2 - 1`, using only `phi(q) <= q`.  This is where
the square root is finally taken -- the one-conductor bound is stated squared on purpose, and the
root is taken once, here, against a nonnegative bound.

Negative scope: the rank hypothesis is sharp for this comparison and nothing more -- at rank four
the majorant is the harmonic series, which diverges, so this comparison gives nothing there; no
divergence of the actual series is claimed at rank four.  Nothing here evaluates a Gauss sum, forms
an Euler product, or touches the archimedean factor (`ArchimedeanShiftedGaussianBound`).
-/

namespace SMSFormula.FiniteQuadraticSum

open Matrix Finset

variable {q : ℕ} {m : Type*}

/-- The normalisation: the conductor-`q` sum divided by `q^n` satisfies the same bound with the
conductor moved into the denominator. -/
theorem norm_sq_normalized_sum_char_affineQuadratic_le [Fintype m] [DecidableEq m] [NeZero q]
    {psi : AddChar (ZMod q) ℂ} (hpsi : Function.Injective psi)
    {B : Matrix m m (ZMod q)} (hB : B.IsSymm) (l : m → ZMod q) (c : ZMod q)
    {H : Matrix m m ℤ} (hdet : H.det ≠ 0) (hH : B + B = H.map (Int.cast : ℤ → ZMod q)) :
    ‖((q : ℂ) ^ Fintype.card m)⁻¹ * ∑ w : m → ZMod q, psi (affineQuadratic B l c w)‖ ^ 2 ≤
      ((q : ℝ) ^ Fintype.card m)⁻¹ * (H.det.natAbs : ℝ) ^ Fintype.card m := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hbase := norm_sq_sum_char_affineQuadratic_le_det_pow hpsi hB l c hdet hH
  rw [norm_mul, mul_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have h1 : (((q : ℝ) ^ Fintype.card m)⁻¹) ^ 2 *
        ‖∑ w : m → ZMod q, psi (affineQuadratic B l c w)‖ ^ 2 ≤
      (((q : ℝ) ^ Fintype.card m)⁻¹) ^ 2 *
        ((q : ℝ) ^ Fintype.card m * (H.det.natAbs : ℝ) ^ Fintype.card m) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  refine h1.trans (le_of_eq ?_)
  have hne : ((q : ℝ) ^ Fintype.card m) ≠ 0 := by positivity
  field_simp

/-- The conductor sum converges above rank four.  Only `phi(q) <= q` and the squared bound are used:
the series is compared with the `p`-series at exponent `n/2 - 1`, by conductor, with no prime
indexing anywhere. -/
theorem summable_totient_mul_norm {n : ℕ} (hn : 4 < n) {D : ℝ} (G : ℕ → ℂ)
    (hG : ∀ q : ℕ, q ≠ 0 → ‖G q‖ ^ 2 ≤ ((q : ℝ) ^ n)⁻¹ * D) :
    Summable (fun q : ℕ ↦ (Nat.totient q : ℝ) * ‖G q‖) := by
  have hp : (1 : ℝ) < (n : ℝ) / 2 - 1 := by
    have h4 : (4 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  refine Summable.of_nonneg_of_le (fun q ↦ by positivity) (fun q ↦ ?_)
    (((Real.summable_one_div_nat_rpow (p := (n : ℝ) / 2 - 1)).2 hp).mul_left (Real.sqrt D))
  have hne0 : ((n : ℝ) / 2 - 1) ≠ 0 := ne_of_gt (by linarith)
  rcases eq_or_ne q 0 with rfl | hq
  · simp [Nat.totient_zero, Real.zero_rpow hne0]
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hsqrt : Real.sqrt ((q : ℝ) ^ n) = (q : ℝ) ^ ((n : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (q : ℝ) n, ← Real.rpow_mul hq0.le]
      congr 1
      ring
    have hnorm : ‖G q‖ ≤ Real.sqrt D * ((q : ℝ) ^ ((n : ℝ) / 2))⁻¹ := by
      have h1 : ‖G q‖ ≤ Real.sqrt (((q : ℝ) ^ n)⁻¹ * D) := by
        rw [show ‖G q‖ = Real.sqrt (‖G q‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
        exact Real.sqrt_le_sqrt (hG q hq)
      refine h1.trans (le_of_eq ?_)
      rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, hsqrt]
      ring
    calc (Nat.totient q : ℝ) * ‖G q‖
        ≤ (q : ℝ) * (Real.sqrt D * ((q : ℝ) ^ ((n : ℝ) / 2))⁻¹) := by
          gcongr
          exact_mod_cast Nat.totient_le q
      _ = Real.sqrt D * (1 / (q : ℝ) ^ ((n : ℝ) / 2 - 1)) := by
          rw [Real.rpow_sub hq0, Real.rpow_one]
          field_simp

/-- The two pieces combined: a family of normalised conductor-`q` sums, each bounded through the
one-conductor estimate by an integral matrix with nonzero determinant, is summable against the
totient multiplicity above rank four. -/
theorem summable_totient_mul_norm_of_det_bound {n : ℕ} (hn : 4 < n) (d : ℕ) (G : ℕ → ℂ)
    (hG : ∀ q : ℕ, q ≠ 0 → ‖G q‖ ^ 2 ≤ ((q : ℝ) ^ n)⁻¹ * (d : ℝ) ^ n) :
    Summable (fun q : ℕ ↦ (Nat.totient q : ℝ) * ‖G q‖) :=
  summable_totient_mul_norm hn G hG

end SMSFormula.FiniteQuadraticSum
