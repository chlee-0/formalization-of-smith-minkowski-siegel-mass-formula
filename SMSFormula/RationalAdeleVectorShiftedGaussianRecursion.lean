import SMSFormula.RationalAdeleVectorGaussianSummability

/-!
# Finite-dimensional shifted Gaussian theta recursion

This file upgrades the certified fixed-tail Schur formula to an identity for
the complete integer-vector theta sum.  The scale is a positive real number
and the linear term is purely imaginary, the class preserved by the Schur
step.  Absolute summability is established before the outer coordinate sum is
split or the tail and dual-integer sums are exchanged.

The result is the exact recursive theta identity.  It does not identify
the recursively transformed quadratic expression with the inverse matrix or
combine the scalar factor with the determinant recursion.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Reindex a finite family by the canonical equivalence with `Fin card`. -/
private def fintypeIntegerVectorEquiv (ι : Type*) [Fintype ι] :
    (Fin (Fintype.card ι) → ℤ) ≃ (ι → ℤ) where
  toFun z i := z (Fintype.equivFin ι i)
  invFun z i := z ((Fintype.equivFin ι).symm i)
  left_inv z := by ext i; simp
  right_inv z := by ext i; simp

/-- Unshifted positive-definite matrix Gaussians are summable on every finite
coordinate type. -/
theorem summable_shiftedMatrixGaussianSummand_zero_fintype
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) {a : ℝ} (ha : 0 < a) :
    Summable (shiftedMatrixGaussianSummand S (a : ℂ) 0) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    S.submatrix e e
  have hT : T.PosDef := Matrix.PosDef.submatrix_equiv S e hS
  have hfin : Summable (shiftedMatrixGaussianSummand T (a : ℂ) 0) :=
    summable_shiftedMatrixGaussianSummand_zero T hT ha
  let E : (Fin (Fintype.card ι) → ℤ) ≃ (ι → ℤ) :=
    fintypeIntegerVectorEquiv ι
  apply E.summable_iff.mp
  refine hfin.congr ?_
  intro z
  change shiftedMatrixGaussianSummand T (a : ℂ) 0 z =
    shiftedMatrixGaussianSummand S (a : ℂ) 0 (E z)
  rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand]
  have hquad := Matrix.dotProduct_mulVec_submatrix_equiv S e
    (integerVectorReal z)
  have hEz : integerVectorReal (E z) =
      fun i => integerVectorReal z (e.symm i) := by
    funext i
    simp [integerVectorReal, E, fintypeIntegerVectorEquiv, e]
  have hquad' :
      integerVectorReal z ⬝ᵥ T.mulVec (integerVectorReal z) =
        integerVectorReal (E z) ⬝ᵥ S.mulVec (integerVectorReal (E z)) := by
    rw [hEz]
    simpa [T] using hquad
  rw [hquad']
  simp

/-- A purely imaginary linear term changes only the phase, not the norm, of
the positive-real matrix Gaussian. -/
theorem norm_shiftedMatrixGaussianSummand_pureImaginaryLinear
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (a : ℝ) (r : ι → ℝ) (z : ι → ℤ) :
    ‖shiftedMatrixGaussianSummand S (a : ℂ) (pureImaginaryLinear r) z‖ =
      ‖shiftedMatrixGaussianSummand S (a : ℂ) 0 z‖ := by
  rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand,
    Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [pureImaginaryLinear, Complex.mul_re]

/-- Positive-real matrix Gaussians with purely imaginary linear term are
summable on every finite coordinate type. -/
theorem summable_shiftedMatrixGaussianSummand_pureImaginaryLinear
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) {a : ℝ} (ha : 0 < a)
    (r : ι → ℝ) :
    Summable
      (shiftedMatrixGaussianSummand S (a : ℂ) (pureImaginaryLinear r)) := by
  apply Summable.of_norm_bounded
    (summable_shiftedMatrixGaussianSummand_zero_fintype S hS ha).norm
  intro z
  exact le_of_eq
    (norm_shiftedMatrixGaussianSummand_pureImaginaryLinear S a r z)

/-- Canonical splitting of an integer vector into its tail coordinates and
its distinguished `Unit` coordinate. -/
def sumInrIntegerVectorEquiv {n : ℕ} :
    ((Fin n → ℤ) × ℤ) ≃ (Unit ⊕ Fin n → ℤ) where
  toFun p := Sum.elim (fun _ => p.2) p.1
  invFun z := (fun j => z (Sum.inr j), z (Sum.inl ()))
  left_inv p := by
    ext j
    · rfl
    · rfl
  right_inv z := by
    funext i
    rcases i with i | i
    · cases i
      rfl
    · rfl

@[simp]
theorem sumInrIntegerVectorEquiv_apply
    {n : ℕ} (u : Fin n → ℤ) (k : ℤ) :
    sumInrIntegerVectorEquiv (u, k) = Sum.elim (fun _ => k) u :=
  rfl

/-- Exact Schur recursion for the complete shifted matrix theta sum.  Every
rearrangement in this identity is backed by the corresponding absolute
summability theorem. -/
theorem tsum_shiftedMatrixGaussianSummand_pureImaginaryLinear_eq_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a)
    (r : Unit ⊕ Fin n → ℝ) :
    (∑' z : Unit ⊕ Fin n → ℤ,
      shiftedMatrixGaussianSummand S (a : ℂ)
        (pureImaginaryLinear r) z) =
      1 / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        ∑' l : ℤ,
          Complex.exp
              (-Real.pi / ((a : ℂ) *
                  (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
                ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2) *
            ∑' u : Fin n → ℤ,
              shiftedMatrixGaussianSummand (sumInrSchurComplement S)
                (a : ℂ)
                (pureImaginaryLinear
                  (sumInrTransformedRealLinear S r l)) u := by
  let f : (Unit ⊕ Fin n → ℤ) → ℂ :=
    shiftedMatrixGaussianSummand S (a : ℂ) (pureImaginaryLinear r)
  let e : ((Fin n → ℤ) × ℤ) ≃ (Unit ⊕ Fin n → ℤ) :=
    sumInrIntegerVectorEquiv
  have hf : Summable f :=
    summable_shiftedMatrixGaussianSummand_pureImaginaryLinear S hS ha r
  have hpair : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  have hs : 0 < S (Sum.inl ()) (Sum.inl ()) :=
    posDef_sumInl_entry_pos S hS
  have hslice : ∀ u : Fin n → ℤ,
      (∑' k : ℤ, f (e (u, k))) =
        1 / ((a : ℂ) *
            (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
          ∑' l : ℤ, schurDualGaussianFamilyOfRealLinear S a r u l := by
    intro u
    simpa [f, e, schurDualGaussianFamilyOfRealLinear,
      pureImaginaryLinear] using
        (tsum_shiftedMatrixGaussianSummand_sum_eq_schur S hS
          (by simpa using ha) (pureImaginaryLinear r) u)
  calc
    (∑' z : Unit ⊕ Fin n → ℤ,
        shiftedMatrixGaussianSummand S (a : ℂ)
          (pureImaginaryLinear r) z) =
        ∑' p : (Fin n → ℤ) × ℤ, f (e p) := by
      simpa [f] using (e.tsum_eq f).symm
    _ = ∑' u : Fin n → ℤ, ∑' k : ℤ, f (e (u, k)) :=
      hpair.tsum_prod
    _ = ∑' u : Fin n → ℤ,
        1 / ((a : ℂ) *
            (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
          ∑' l : ℤ, schurDualGaussianFamilyOfRealLinear S a r u l := by
      apply tsum_congr
      exact hslice
    _ = 1 / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        ∑' u : Fin n → ℤ, ∑' l : ℤ,
          schurDualGaussianFamilyOfRealLinear S a r u l := by
      rw [tsum_mul_left]
    _ = 1 / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        ∑' l : ℤ, ∑' u : Fin n → ℤ,
          schurDualGaussianFamilyOfRealLinear S a r u l := by
      rw [tsum_schurDualGaussianFamilyOfRealLinear_comm S hS ha r]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro l
      rw [← tsum_mul_left]
      apply tsum_congr
      intro u
      rw [schurDualGaussianFamilyOfRealLinear,
        sumInrTransformedLinear_pureImaginaryLinear S hs.ne' r l]
      have hhead :
          (l : ℂ) + Complex.I * pureImaginaryLinear r (Sum.inl ()) =
            (l : ℂ) - (r (Sum.inl ()) : ℂ) := by
        rw [pureImaginaryLinear]
        rw [← mul_assoc, ← pow_two Complex.I, Complex.I_sq]
        ring
      rw [hhead]

end PositiveDefiniteIntegralLattice
