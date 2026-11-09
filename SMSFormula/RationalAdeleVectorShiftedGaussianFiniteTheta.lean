import SMSFormula.RationalAdeleVectorCenteredGaussianSummability

/-!
# Finite-dimensional shifted Gaussian theta transformation

This file assembles the rank-one theta slice, Schur
recursion, inverse-quadratic identity, determinant normalization, and centered
dual summability into the finite-dimensional shifted theta theorem.  The scale
is positive real and the linear term is purely imaginary, exactly the class
preserved by the recursion.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- The centered full inverse Gaussian is pointwise the head dual Gaussian
times the centered inverse-Schur Gaussian. -/
theorem centeredMatrixGaussianSummand_inv_eq_head_mul_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a)
    (r : Unit ⊕ Fin n → ℝ) (l : ℤ) (v : Fin n → ℤ) :
    centeredMatrixGaussianSummand S⁻¹ (1 / a) r
        (Sum.elim (fun _ => l) v) =
      Complex.exp
          (-Real.pi / ((a : ℂ) *
              (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
            ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2) *
        centeredMatrixGaussianSummand
          (sumInrSchurComplement S)⁻¹ (1 / a)
          (sumInrTransformedRealLinear S r l) v := by
  have hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0 :=
    (posDef_sumInl_entry_pos S hS).ne'
  have hquad := shiftedInverseQuadratic_eq_sumInrSchur S hS r l v
  rw [centeredMatrixGaussianSummand, centeredMatrixGaussianSummand]
  have hy :
      (fun i => ((Sum.elim (fun _ : Unit => l) v i : ℤ) : ℝ) - r i) =
        Sum.elim (fun _ => (l : ℝ) - r (Sum.inl ()))
          (fun j => (v j : ℝ) - r (Sum.inr j)) := by
    funext i
    rcases i with i | i
    · cases i
      rfl
    · rfl
  rw [hy]
  rw [hquad]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ha.ne', hs]
  ring

/-- The complete shifted theta theorem on the native `Unit ⊕ Fin n` carrier,
assuming the theorem in the lower `Fin n` dimension. -/
private theorem tsum_shiftedMatrixGaussianSummand_sum_eq_centered_inv_of_lower
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a)
    (r : Unit ⊕ Fin n → ℝ)
    (hlower :
      ∀ (W : Matrix (Fin n) (Fin n) ℝ), W.PosDef →
        ∀ rW : Fin n → ℝ,
          (∑' u : Fin n → ℤ,
              shiftedMatrixGaussianSummand W (a : ℂ)
                (pureImaginaryLinear rW) u) =
            shiftedMatrixThetaNormalization W a *
              ∑' v : Fin n → ℤ,
                centeredMatrixGaussianSummand W⁻¹ (1 / a) rW v) :
    (∑' z : Unit ⊕ Fin n → ℤ,
        shiftedMatrixGaussianSummand S (a : ℂ)
          (pureImaginaryLinear r) z) =
      shiftedMatrixThetaNormalization S a *
        ∑' y : Unit ⊕ Fin n → ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) r y := by
  let W : Matrix (Fin n) (Fin n) ℝ := sumInrSchurComplement S
  let head : ℤ → ℂ := fun l =>
    Complex.exp
      (-Real.pi / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
        ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)
  let lower : ℤ → ℂ := fun l =>
    ∑' v : Fin n → ℤ,
      centeredMatrixGaussianSummand W⁻¹ (1 / a)
        (sumInrTransformedRealLinear S r l) v
  have hW : W.PosDef := sumInrSchurComplement_posDef S hS
  have hrec :=
    tsum_shiftedMatrixGaussianSummand_pureImaginaryLinear_eq_schur
      S hS ha r
  rw [hrec]
  have hlower' : ∀ l : ℤ,
      (∑' u : Fin n → ℤ,
          shiftedMatrixGaussianSummand W (a : ℂ)
            (pureImaginaryLinear
              (sumInrTransformedRealLinear S r l)) u) =
        shiftedMatrixThetaNormalization W a * lower l := by
    intro l
    exact hlower W hW (sumInrTransformedRealLinear S r l)
  change
    1 / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        (∑' l : ℤ, head l *
          ∑' u : Fin n → ℤ,
            shiftedMatrixGaussianSummand W (a : ℂ)
              (pureImaginaryLinear
                (sumInrTransformedRealLinear S r l)) u) = _
  simp_rw [hlower']
  have hfactor :
      (∑' l : ℤ,
          head l * (shiftedMatrixThetaNormalization W a * lower l)) =
        shiftedMatrixThetaNormalization W a *
          ∑' l : ℤ, head l * lower l := by
    calc
      _ = ∑' l : ℤ,
          shiftedMatrixThetaNormalization W a * (head l * lower l) := by
        apply tsum_congr
        intro l
        ring
      _ = _ := tsum_mul_left
  rw [hfactor, ← mul_assoc,
    scalar_mul_shiftedMatrixThetaNormalization_schur S hS ha]
  congr 1
  let E : ((Fin n → ℤ) × ℤ) ≃ (Unit ⊕ Fin n → ℤ) :=
    sumInrIntegerVectorEquiv
  have hfull : Summable
      (centeredMatrixGaussianSummand S⁻¹ (1 / a) r) :=
    summable_centeredMatrixGaussianSummand_inv S hS ha r
  have hpair : Summable (fun p : (Fin n → ℤ) × ℤ =>
      centeredMatrixGaussianSummand S⁻¹ (1 / a) r (E p)) :=
    E.summable_iff.mpr hfull
  calc
    (∑' l : ℤ, head l * lower l) =
        ∑' l : ℤ, ∑' v : Fin n → ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) r (E (v, l)) := by
      apply tsum_congr
      intro l
      rw [← tsum_mul_left]
      apply tsum_congr
      intro v
      exact
        (centeredMatrixGaussianSummand_inv_eq_head_mul_schur
          S hS ha r l v).symm
    _ = ∑' v : Fin n → ℤ, ∑' l : ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) r (E (v, l)) :=
      hpair.tsum_comm
    _ = ∑' p : (Fin n → ℤ) × ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) r (E p) :=
      hpair.tsum_prod.symm
    _ = ∑' y : Unit ⊕ Fin n → ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) r y :=
      E.tsum_eq _

/-- Reindexing both matrix coordinates transports the shifted summand
pointwise. -/
private theorem shiftedMatrixGaussianSummand_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (a : ℝ)
    (r : α → ℝ) (z : β → ℤ) :
    shiftedMatrixGaussianSummand (S.submatrix e e) (a : ℂ)
        (pureImaginaryLinear (fun i => r (e i))) z =
      shiftedMatrixGaussianSummand S (a : ℂ)
        (pureImaginaryLinear r) (fun i => z (e.symm i)) := by
  rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand]
  have hquad := Matrix.dotProduct_mulVec_submatrix_equiv S e
    (integerVectorReal z)
  rw [hquad]
  congr 1
  have hsum :
      (∑ i : β,
          pureImaginaryLinear (fun j => r (e j)) i * (z i : ℂ)) =
        ∑ i : α,
          pureImaginaryLinear r i * (z (e.symm i) : ℂ) := by
    rw [← Equiv.sum_comp e]
    simp [pureImaginaryLinear]
  rw [hsum]
  have hreal :
      (fun i : α => integerVectorReal z (e.symm i)) =
        integerVectorReal (fun i : α => z (e.symm i)) := by
    rfl
  rw [hreal]

/-- Reindexing both matrix coordinates transports the centered summand
pointwise. -/
private theorem centeredMatrixGaussianSummand_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (a : ℝ)
    (r : α → ℝ) (z : β → ℤ) :
    centeredMatrixGaussianSummand (S.submatrix e e) a
        (fun i => r (e i)) z =
      centeredMatrixGaussianSummand S a r (fun i => z (e.symm i)) := by
  rw [centeredMatrixGaussianSummand, centeredMatrixGaussianSummand]
  have hquad := Matrix.dotProduct_mulVec_submatrix_equiv S e
    (fun i => (z i : ℝ) - r (e i))
  have hvector :
      (fun i : α => (z (e.symm i) : ℝ) - r i) =
        fun i => (z (e.symm i) : ℝ) - r (e (e.symm i)) := by
    funext i
    simp
  rw [hvector]
  simpa using congrArg
    (fun q : ℝ => Complex.exp (-Real.pi * (a : ℂ) * (q : ℂ))) hquad

/-- The determinant normalization is invariant under finite coordinate
reindexing. -/
private theorem shiftedMatrixThetaNormalization_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S : Matrix α α ℝ) (e : β ≃ α) (a : ℝ) :
    shiftedMatrixThetaNormalization (S.submatrix e e) a =
      shiftedMatrixThetaNormalization S a := by
  have hcard : Fintype.card β = Fintype.card α := Fintype.card_congr e
  simp [shiftedMatrixThetaNormalization, Matrix.det_submatrix_equiv_self,
    hcard]

/-- Finite-dimensional shifted Gaussian theta transformation.  A positive-
real matrix Gaussian with purely imaginary linear term transforms to the
determinant-normalized centered Gaussian for the inverse matrix. -/
theorem tsum_shiftedMatrixGaussianSummand_pureImaginaryLinear_eq_centered_inv
    (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (r : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S (a : ℂ)
          (pureImaginaryLinear r) z) =
      shiftedMatrixThetaNormalization S a *
        ∑' y : Fin n → ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) r y := by
  induction n with
  | zero =>
      simp [shiftedMatrixGaussianSummand, centeredMatrixGaussianSummand,
        shiftedMatrixThetaNormalization, pureImaginaryLinear,
        integerVectorReal, dotProduct, Matrix.mulVec]
  | succ n ih =>
      let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
        ((Equiv.sumCongr finOneEquiv.symm (Equiv.refl (Fin n))).trans
          finSumFinEquiv).trans (finCongr (by omega))
      let T : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
        S.submatrix e e
      let rT : Unit ⊕ Fin n → ℝ := fun i => r (e i)
      have hT : T.PosDef := Matrix.PosDef.submatrix_equiv S e hS
      have hnative :
          (∑' z : Unit ⊕ Fin n → ℤ,
              shiftedMatrixGaussianSummand T (a : ℂ)
                (pureImaginaryLinear rT) z) =
            shiftedMatrixThetaNormalization T a *
              ∑' y : Unit ⊕ Fin n → ℤ,
                centeredMatrixGaussianSummand T⁻¹ (1 / a) rT y := by
        apply tsum_shiftedMatrixGaussianSummand_sum_eq_centered_inv_of_lower
          T hT ha rT
        intro W hW rW
        exact ih W hW rW
      let E : (Unit ⊕ Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
        { toFun := fun z i => z (e.symm i)
          invFun := fun z i => z (e i)
          left_inv := by intro z; ext i; simp
          right_inv := by intro z; ext i; simp }
      have hleft :
          (∑' z : Unit ⊕ Fin n → ℤ,
              shiftedMatrixGaussianSummand T (a : ℂ)
                (pureImaginaryLinear rT) z) =
            ∑' z : Fin (n + 1) → ℤ,
              shiftedMatrixGaussianSummand S (a : ℂ)
                (pureImaginaryLinear r) z := by
        calc
          _ = ∑' z : Unit ⊕ Fin n → ℤ,
                shiftedMatrixGaussianSummand S (a : ℂ)
                  (pureImaginaryLinear r) (E z) := by
              apply tsum_congr
              intro z
              exact shiftedMatrixGaussianSummand_submatrix_equiv
                S e a r z
          _ = _ := E.tsum_eq _
      have hnormalization :
          shiftedMatrixThetaNormalization T a =
            shiftedMatrixThetaNormalization S a :=
        shiftedMatrixThetaNormalization_submatrix_equiv S e a
      have hinv : T⁻¹ = S⁻¹.submatrix e e := by
        change (S.submatrix e e)⁻¹ = S⁻¹.submatrix e e
        exact Matrix.inv_submatrix_equiv S e e
      have hright :
          (∑' y : Unit ⊕ Fin n → ℤ,
              centeredMatrixGaussianSummand T⁻¹ (1 / a) rT y) =
            ∑' y : Fin (n + 1) → ℤ,
              centeredMatrixGaussianSummand S⁻¹ (1 / a) r y := by
        rw [hinv]
        calc
          _ = ∑' y : Unit ⊕ Fin n → ℤ,
                centeredMatrixGaussianSummand S⁻¹ (1 / a) r (E y) := by
              apply tsum_congr
              intro y
              exact centeredMatrixGaussianSummand_submatrix_equiv
                S⁻¹ e (1 / a) r y
          _ = _ := E.tsum_eq _
      rw [hleft, hnormalization, hright] at hnative
      exact hnative

/-- Zero-shift specialization of the finite-dimensional matrix theta
transformation. -/
theorem tsum_shiftedMatrixGaussianSummand_zero_eq_centered_inv
    (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S (a : ℂ) 0 z) =
      shiftedMatrixThetaNormalization S a *
        ∑' y : Fin n → ℤ,
          centeredMatrixGaussianSummand S⁻¹ (1 / a) 0 y := by
  have hzero : pureImaginaryLinear (0 : Fin n → ℝ) = 0 := by
    funext i
    simp [pureImaginaryLinear]
  rw [← hzero]
  exact tsum_shiftedMatrixGaussianSummand_pureImaginaryLinear_eq_centered_inv
    n S hS ha (0 : Fin n → ℝ)

end PositiveDefiniteIntegralLattice
