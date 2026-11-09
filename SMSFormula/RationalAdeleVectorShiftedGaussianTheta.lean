import SMSFormula.Finiteness
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Shifted Gaussian theta induction step

The one-dimensional Gaussian theta formula must be used with a linear term
when a positive-definite matrix is split as `Unit ⊕ m`.  Indeed, after the
tail coordinates are fixed, the off-diagonal block contributes a shift to the
distinguished integer coordinate.  This file records the exact scalar slice
identity, with the constant tail factor kept, which is the analytic
induction step for the Euclidean polar theta theorem.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Exact shifted rank-one Gaussian theta identity after extracting a
constant factor. -/
theorem tsum_exp_neg_quadratic_add_const
    {a : ℂ} (ha : 0 < a.re) (linear constant : ℂ) :
    (∑' k : ℤ, Complex.exp
        (constant + (-Real.pi * a * (k : ℂ) ^ 2 +
          2 * Real.pi * linear * (k : ℂ)))) =
      Complex.exp constant *
        (1 / a ^ (1 / 2 : ℂ) *
          ∑' l : ℤ, Complex.exp
            (-Real.pi / a * ((l : ℂ) + Complex.I * linear) ^ 2)) := by
  calc
    _ = Complex.exp constant *
        (∑' k : ℤ, Complex.exp
          (-Real.pi * a * (k : ℂ) ^ 2 +
            2 * Real.pi * linear * (k : ℂ))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [← Complex.exp_add]
    _ = _ := by rw [Complex.tsum_exp_neg_quadratic ha linear]

/-- The exact one-coordinate summation formula for a block quadratic
polynomial

`s * k² + 2 * cross * k + tailQuadratic`

and linear phase `headLinear * k + tailLinear`.  The transformed scalar shift
is `headLinear - b * cross`; this dependence on the fixed tail is why the
unshifted theta theorem is not stable under Schur-complement induction. -/
theorem tsum_exp_neg_block_quadratic
    {b : ℂ} (hb : 0 < b.re) {s : ℝ} (hs : 0 < s)
    (cross tailQuadratic : ℝ) (headLinear tailLinear : ℂ) :
    (∑' k : ℤ, Complex.exp
      (-Real.pi * b *
          ((s : ℂ) * (k : ℂ) ^ 2 +
            2 * (cross : ℂ) * (k : ℂ) + (tailQuadratic : ℂ)) +
        2 * Real.pi *
          (headLinear * (k : ℂ) + tailLinear))) =
      Complex.exp
          (-Real.pi * b * (tailQuadratic : ℂ) +
            2 * Real.pi * tailLinear) *
        (1 / (b * (s : ℂ)) ^ (1 / 2 : ℂ) *
          ∑' l : ℤ, Complex.exp
            (-Real.pi / (b * (s : ℂ)) *
              ((l : ℂ) + Complex.I *
                (headLinear - b * (cross : ℂ))) ^ 2)) := by
  have hbs : 0 < (b * (s : ℂ)).re := by
    simpa using mul_pos hb hs
  convert tsum_exp_neg_quadratic_add_const hbs
    (headLinear - b * (cross : ℂ))
    (-Real.pi * b * (tailQuadratic : ℂ) +
      2 * Real.pi * tailLinear) using 1
  · apply tsum_congr
    intro k
    congr 1
    ring

/-! ## Matrix block interface -/

/-- A lattice integer vector viewed in real coordinates. -/
def integerVectorReal {ι : Type*} (z : ι → ℤ) : ι → ℝ :=
  fun i => (z i : ℝ)

/-- The shifted matrix-Gaussian summand used by the finite-dimensional theta
induction. -/
noncomputable def shiftedMatrixGaussianSummand
    {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (b : ℂ)
    (linear : ι → ℂ) (z : ι → ℤ) : ℂ :=
  Complex.exp
    (-Real.pi * b *
        ((integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z) : ℝ) : ℂ) +
      2 * Real.pi * ∑ i, linear i * (z i : ℂ))

private theorem posDef_head_pos {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef) :
    0 < S (Sum.inl ()) (Sum.inl ()) := by
  let e : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ : m => 0)
  have he : e ≠ 0 := by
    intro he
    have h : e (Sum.inl ()) = 0 := congr_fun he (Sum.inl ())
    norm_num [e] at h
  have hpos := hS.dotProduct_mulVec_pos (x := e) he
  simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos

/-- Exact `Unit ⊕ m` slice formula for the shifted matrix Gaussian.  This is
the rank-one analytic step in a Schur-complement induction.  Crucially, its
dual scalar theta has the tail-dependent shift

`linear (inl ()) - b * ∑ j, S (inl ()) (inr j) * u j`.

The theorem deliberately stops before claiming that the remaining family of
shifted lower-rank theta sums has been reassembled. -/
theorem tsum_shiftedMatrixGaussianSummand_sum
    {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) (linear : Unit ⊕ m → ℂ) (u : m → ℤ) :
    let s : ℝ := S (Sum.inl ()) (Sum.inl ())
    let cross : ℝ :=
      ∑ j, S (Sum.inl ()) (Sum.inr j) * (u j : ℝ)
    let tailQuadratic : ℝ :=
      integerVectorReal u ⬝ᵥ
        (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u)
    let tailLinear : ℂ := ∑ j, linear (Sum.inr j) * (u j : ℂ)
    (∑' k : ℤ, shiftedMatrixGaussianSummand S b linear
      (Sum.elim (fun _ : Unit => k) u)) =
      Complex.exp
          (-Real.pi * b * (tailQuadratic : ℂ) +
            2 * Real.pi * tailLinear) *
        (1 / (b * (s : ℂ)) ^ (1 / 2 : ℂ) *
          ∑' l : ℤ, Complex.exp
            (-Real.pi / (b * (s : ℂ)) *
              ((l : ℂ) + Complex.I *
                (linear (Sum.inl ()) - b * (cross : ℂ))) ^ 2)) := by
  dsimp only
  have hs := posDef_head_pos S hS
  convert tsum_exp_neg_block_quadratic hb hs
    (∑ j, S (Sum.inl ()) (Sum.inr j) * (u j : ℝ))
    (integerVectorReal u ⬝ᵥ
      (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u))
    (linear (Sum.inl ()))
    (∑ j, linear (Sum.inr j) * (u j : ℂ)) using 1
  apply tsum_congr
  intro k
  have hsymm : ∀ j : m,
      S (Sum.inr j) (Sum.inl ()) = S (Sum.inl ()) (Sum.inr j) := by
    intro j
    simpa using (hS.isHermitian.apply (Sum.inr j) (Sum.inl ())).symm
  have hsum :
      (∑ x : m,
          (u x : ℂ) *
            ((S (Sum.inl ()) (Sum.inr x) : ℂ) * (k : ℂ) +
              ∑ x₁ : m,
                (S (Sum.inr x) (Sum.inr x₁) : ℂ) * (u x₁ : ℂ))) =
        (k : ℂ) *
            (∑ x : m, (S (Sum.inl ()) (Sum.inr x) : ℂ) * (u x : ℂ)) +
          ∑ x : m, (u x : ℂ) * ∑ x₁ : m,
            (S (Sum.inr x) (Sum.inr x₁) : ℂ) * (u x₁ : ℂ) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  simp [shiftedMatrixGaussianSummand, integerVectorReal, dotProduct,
    Matrix.mulVec, Fintype.sum_sum_type, Finset.univ_unique, hsymm]
  rw [hsum]
  ring_nf

end PositiveDefiniteIntegralLattice
