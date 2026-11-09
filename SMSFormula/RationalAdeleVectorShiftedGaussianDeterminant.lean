import SMSFormula.RationalAdeleVectorShiftedGaussianInverse

/-!
# Square-root determinant normalization for shifted matrix theta recursion

This file isolates the branch-sensitive scalar factor in the Schur induction.
All complex half-powers are first identified with positive real square roots.
The rank-one scalar factor and the lower Schur determinant normalization then
multiply to the full determinant normalization by the exact Schur determinant
formula.  No theta sum, Fourier transform, or shell statement is introduced.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Positive-real determinant normalization for a matrix Gaussian on a finite
coordinate type. -/
def shiftedMatrixThetaNormalization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (a : ℝ) : ℂ :=
  1 / (Real.sqrt (a ^ Fintype.card ι * S.det) : ℂ)

/-- On a positive real argument, the complex half-power in the scalar theta
formula is the cast of the positive real square root. -/
theorem cpow_half_ofReal_mul_eq_sqrt
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ((a : ℂ) * (s : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (a * s) : ℂ) := by
  have h := Complex.ofReal_cpow (mul_nonneg ha.le hs.le) (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow] at h
  simpa using h.symm

/-- Exact determinant recursion for the named Schur complement. -/
theorem det_eq_head_mul_sumInrSchurComplement_det
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) :
    S.det = S (Sum.inl ()) (Sum.inl ()) *
      (sumInrSchurComplement S).det := by
  simpa [sumInrSchurComplement] using
    Matrix.det_sum_schurComplement_inr S
      (posDef_sumInl_entry_pos S hS).ne'

/-- The real square-root determinant in the full dimension splits into the
rank-one scalar square root and the lower Schur normalization. -/
theorem sqrt_scale_mul_det_eq_head_mul_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a) :
    Real.sqrt
        (a ^ Fintype.card (Unit ⊕ Fin n) * S.det) =
      Real.sqrt (a * S (Sum.inl ()) (Sum.inl ())) *
        Real.sqrt
          (a ^ Fintype.card (Fin n) *
            (sumInrSchurComplement S).det) := by
  have hs : 0 < S (Sum.inl ()) (Sum.inl ()) :=
    posDef_sumInl_entry_pos S hS
  have harg :
      a ^ Fintype.card (Unit ⊕ Fin n) * S.det =
        (a * S (Sum.inl ()) (Sum.inl ())) *
          (a ^ Fintype.card (Fin n) *
            (sumInrSchurComplement S).det) := by
    rw [det_eq_head_mul_sumInrSchurComplement_det S hS]
    simp [Fintype.card_sum]
    ring
  rw [harg, Real.sqrt_mul (mul_nonneg ha.le hs.le)]

/-- Literal complex normalization recursion used by the shifted matrix theta
induction. The principal complex half-power is harmless because its argument
is certified positive real. -/
theorem scalar_mul_shiftedMatrixThetaNormalization_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a) :
    1 / ((a : ℂ) *
        (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        shiftedMatrixThetaNormalization (sumInrSchurComplement S) a =
      shiftedMatrixThetaNormalization S a := by
  have hs : 0 < S (Sum.inl ()) (Sum.inl ()) :=
    posDef_sumInl_entry_pos S hS
  rw [cpow_half_ofReal_mul_eq_sqrt ha hs]
  rw [shiftedMatrixThetaNormalization, shiftedMatrixThetaNormalization]
  rw [sqrt_scale_mul_det_eq_head_mul_schur S hS ha]
  push_cast
  ring

end PositiveDefiniteIntegralLattice
