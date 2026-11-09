import SMSFormula.RationalAdeleVectorShiftedGaussianRecursion

/-!
# Inverse quadratic form under the distinguished Schur split

This file identifies the quadratic expression produced by the complete Schur
theta recursion with the quadratic form of the inverse matrix.  The proof
constructs the block solution to `S x = y` directly and verifies it on the
native `Unit ⊕ Fin n` carrier.  It does not combine determinant or complex
square-root factors and does not state the finite-dimensional theta theorem.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- The lower residual after eliminating the distinguished coordinate. -/
def sumInrDualResidual {n : ℕ}
    (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (y : Unit ⊕ Fin n → ℝ) : Fin n → ℝ :=
  fun j => y (Sum.inr j) -
    y (Sum.inl ()) / S (Sum.inl ()) (Sum.inl ()) *
      S (Sum.inl ()) (Sum.inr j)

/-- The tail of the explicit solution to `S x = y`, obtained from the inverse
Schur complement. -/
def sumInrInverseTail {n : ℕ}
    (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (y : Unit ⊕ Fin n → ℝ) : Fin n → ℝ :=
  (sumInrSchurComplement S)⁻¹.mulVec (sumInrDualResidual S y)

/-- The distinguished coordinate of the explicit solution to `S x = y`. -/
def sumInrInverseHead {n : ℕ}
    (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (y : Unit ⊕ Fin n → ℝ) : ℝ :=
  y (Sum.inl ()) / S (Sum.inl ()) (Sum.inl ()) -
    (∑ j, S (Sum.inl ()) (Sum.inr j) * sumInrInverseTail S y j) /
      S (Sum.inl ()) (Sum.inl ())

/-- Explicit block solution to `S x = y`. -/
def sumInrInverseVector {n : ℕ}
    (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (y : Unit ⊕ Fin n → ℝ) : Unit ⊕ Fin n → ℝ :=
  Sum.elim (fun _ => sumInrInverseHead S y) (sumInrInverseTail S y)

theorem sumInrSchurComplement_apply {m : Type*}
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (i j : m) :
    sumInrSchurComplement S i j =
      S (Sum.inr i) (Sum.inr j) -
        S (Sum.inr i) (Sum.inl ()) *
          (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            S (Sum.inl ()) (Sum.inr j) := by
  simpa [sumInrSchurComplement] using
    (Matrix.schurComplement_sum_inr_apply S i j)

/-- The inverse Schur complement sends the lower residual back to that
residual. -/
theorem sumInrSchurComplement_mulVec_inverseTail
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) (y : Unit ⊕ Fin n → ℝ) :
    (sumInrSchurComplement S).mulVec (sumInrInverseTail S y) =
      sumInrDualResidual S y := by
  have hWdet : 0 < (sumInrSchurComplement S).det :=
    (sumInrSchurComplement_posDef S hS).det_pos
  have hWunit : IsUnit (sumInrSchurComplement S).det :=
    isUnit_iff_ne_zero.mpr hWdet.ne'
  rw [sumInrInverseTail, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hWunit, Matrix.one_mulVec]

/-- The explicit Schur block vector solves the full linear system. -/
theorem mulVec_sumInrInverseVector
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) (y : Unit ⊕ Fin n → ℝ) :
    S.mulVec (sumInrInverseVector S y) = y := by
  classical
  have hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0 :=
    (posDef_sumInl_entry_pos S hS).ne'
  have hsymm : S.IsSymm := by
    simpa [Matrix.IsSymm] using hS.isHermitian
  have htail := sumInrSchurComplement_mulVec_inverseTail S hS y
  funext i
  rcases i with i | i
  · cases i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      sumInrInverseVector, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton]
    rw [sumInrInverseHead]
    field_simp [hs]
    ring
  · have hentry : ∀ j,
        S (Sum.inr i) (Sum.inr j) =
          sumInrSchurComplement S i j +
            S (Sum.inr i) (Sum.inl ()) *
              (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
                S (Sum.inl ()) (Sum.inr j) := by
      intro j
      rw [sumInrSchurComplement_apply]
      ring
    have hsymm_i :
        S (Sum.inr i) (Sum.inl ()) =
          S (Sum.inl ()) (Sum.inr i) := by
      simpa using hsymm.apply (Sum.inl ()) (Sum.inr i)
    have htail_i := congr_fun htail i
    change
      ∑ j, sumInrSchurComplement S i j * sumInrInverseTail S y j =
        sumInrDualResidual S y i at htail_i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      sumInrInverseVector, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton]
    simp_rw [hentry]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    rw [htail_i]
    have hfactor :
        (∑ x,
            (S (Sum.inr i) (Sum.inl ()) *
                (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
              S (Sum.inl ()) (Sum.inr x)) * sumInrInverseTail S y x) =
          S (Sum.inr i) (Sum.inl ()) *
              (S (Sum.inl ()) (Sum.inl ()))⁻¹ *
            ∑ x, S (Sum.inl ()) (Sum.inr x) *
              sumInrInverseTail S y x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    rw [hfactor]
    rw [sumInrInverseHead]
    simp [sumInrDualResidual]
    field_simp [hs]
    rw [hsymm_i]
    ring

/-- The explicit block solution is the matrix-inverse solution. -/
theorem inv_mulVec_eq_sumInrInverseVector
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) (y : Unit ⊕ Fin n → ℝ) :
    S⁻¹.mulVec y = sumInrInverseVector S y := by
  have hSunit : IsUnit S.det :=
    isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  calc
    S⁻¹.mulVec y =
        S⁻¹.mulVec (S.mulVec (sumInrInverseVector S y)) := by
      rw [mulVec_sumInrInverseVector S hS y]
    _ = (S⁻¹ * S).mulVec (sumInrInverseVector S y) :=
      Matrix.mulVec_mulVec _ _ _
    _ = sumInrInverseVector S y := by
      rw [Matrix.nonsing_inv_mul _ hSunit, Matrix.one_mulVec]

/-- Quadratic form of the inverse matrix in exact Schur coordinates. -/
theorem dotProduct_inv_mulVec_eq_sumInrSchur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) (y : Unit ⊕ Fin n → ℝ) :
    y ⬝ᵥ S⁻¹.mulVec y =
      y (Sum.inl ()) ^ 2 / S (Sum.inl ()) (Sum.inl ()) +
        sumInrDualResidual S y ⬝ᵥ
          (sumInrSchurComplement S)⁻¹.mulVec
            (sumInrDualResidual S y) := by
  classical
  have hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0 :=
    (posDef_sumInl_entry_pos S hS).ne'
  rw [inv_mulVec_eq_sumInrInverseVector S hS]
  simp [dotProduct, Fintype.sum_sum_type, sumInrInverseVector,
    sumInrInverseHead, sumInrInverseTail, sumInrDualResidual]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ x,
          y (Sum.inl ()) / S (Sum.inl ()) (Sum.inl ()) *
            S (Sum.inl ()) (Sum.inr x) *
              ((sumInrSchurComplement S)⁻¹ *ᵥ
                sumInrDualResidual S y) x) =
        y (Sum.inl ()) / S (Sum.inl ()) (Sum.inl ()) *
          ∑ x, S (Sum.inl ()) (Sum.inr x) *
            ((sumInrSchurComplement S)⁻¹ *ᵥ
              sumInrDualResidual S y) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hfactor]
  field_simp [hs]
  ring

/-- The inverse quadratic form needed by shifted theta induction: the head
dual Gaussian and the lower transformed Schur Gaussian are literally the
full inverse-matrix Gaussian. -/
theorem shiftedInverseQuadratic_eq_sumInrSchur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) (r : Unit ⊕ Fin n → ℝ)
    (l : ℤ) (v : Fin n → ℤ) :
    let y : Unit ⊕ Fin n → ℝ :=
      Sum.elim (fun _ => (l : ℝ) - r (Sum.inl ()))
        (fun j => (v j : ℝ) - r (Sum.inr j))
    y ⬝ᵥ S⁻¹.mulVec y =
      ((l : ℝ) - r (Sum.inl ())) ^ 2 /
          S (Sum.inl ()) (Sum.inl ()) +
        (fun j => (v j : ℝ) - sumInrTransformedRealLinear S r l j) ⬝ᵥ
          (sumInrSchurComplement S)⁻¹.mulVec
            (fun j => (v j : ℝ) -
              sumInrTransformedRealLinear S r l j) := by
  dsimp only
  rw [dotProduct_inv_mulVec_eq_sumInrSchur S hS]
  have hres :
      sumInrDualResidual S
          (Sum.elim (fun _ => (l : ℝ) - r (Sum.inl ()))
            (fun j => (v j : ℝ) - r (Sum.inr j))) =
        fun j => (v j : ℝ) - sumInrTransformedRealLinear S r l j := by
    funext j
    simp [sumInrDualResidual, sumInrTransformedRealLinear]
    ring
  rw [hres]
  simp

end PositiveDefiniteIntegralLattice
