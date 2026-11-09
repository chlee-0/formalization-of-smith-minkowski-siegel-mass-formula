import SMSFormula.RationalAdeleVectorShiftedGaussianDeterminant

/-!
# Summability of centered positive-definite matrix Gaussians

The shifted theta induction transforms a purely imaginary linear term into a
real center in the inverse quadratic form.  Before that transformed sum can be
reindexed or assembled, its absolute summability must be certified.  This file
supplies exactly that certificate on the existing integer coordinate carrier.

No theta identity, determinant formula, Fourier transform, or lattice chart is
introduced here.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- A positive-definite matrix Gaussian centered at an arbitrary real vector. -/
def centeredMatrixGaussianSummand
    {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (a : ℝ)
    (r : ι → ℝ) (z : ι → ℤ) : ℂ :=
  let x : ι → ℝ := fun i => (z i : ℝ) - r i
  Complex.exp
    (-Real.pi * (a : ℂ) * ((x ⬝ᵥ S.mulVec x : ℝ) : ℂ))

/-- Finite products remain summable when each coordinate has its own
summable family. -/
private theorem summable_fin_coordinate_product_family
    {α : Type*} {n : ℕ} (f : Fin n → α → ℂ)
    (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin n → α => ∏ i, f i (x i)) := by
  induction n with
  | zero =>
      apply summable_of_finite_support
      exact Set.toFinite _
  | succ n ih =>
      let e : (Fin (n + 1) → α) ≃ α × (Fin n → α) :=
        (Fin.insertNthEquiv (fun _ => α) 0).symm
      apply e.symm.summable_iff.mp
      have hhead : Summable (f 0) := hf 0
      have htail : Summable (fun x : Fin n → α => ∏ i, f i.succ (x i)) :=
        ih (fun i => f i.succ) (fun i => hf i.succ)
      refine (summable_mul_of_summable_norm hhead.norm htail.norm).congr ?_
      intro x
      simp [e, Fin.prod_univ_succ]

/-- A centered positive-definite matrix Gaussian is summable on `ℤⁿ`. -/
theorem summable_centeredMatrixGaussianSummand
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (r : Fin n → ℝ) :
    Summable (centeredMatrixGaussianSummand S a r) := by
  obtain ⟨c, hc_pos, hc⟩ := hS.exists_pos_mul_sum_sq_le
  have hac : 0 < a * c := mul_pos ha hc_pos
  let scalar : Fin n → ℤ → ℂ := fun i z =>
    Complex.exp
      (-Real.pi * ((a * c : ℝ) : ℂ) *
        ((z : ℂ) - (r i : ℂ)) ^ 2)
  have hscalar : ∀ i, Summable (scalar i) := fun i =>
    summable_int_centeredGaussian_of_posReal hac (r i)
  have hproduct : Summable (fun z : Fin n → ℤ => ∏ i, scalar i (z i)) :=
    summable_fin_coordinate_product_family scalar hscalar
  apply Summable.of_norm_bounded hproduct.norm
  intro z
  let x : Fin n → ℝ := fun i => (z i : ℝ) - r i
  have hq := hc x
  have hineq :
      -Real.pi * a * (x ⬝ᵥ S.mulVec x) ≤
        -Real.pi * (a * c) * ∑ i, x i ^ 2 := by
    calc
      -Real.pi * a * (x ⬝ᵥ S.mulVec x) =
          (-Real.pi * a) * (x ⬝ᵥ S.mulVec x) := by ring
      _ ≤ (-Real.pi * a) * (c * ∑ i, x i ^ 2) :=
        mul_le_mul_of_nonpos_left hq
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) ha.le)
      _ = -Real.pi * (a * c) * ∑ i, x i ^ 2 := by ring
  calc
    ‖centeredMatrixGaussianSummand S a r z‖ =
        Real.exp (-Real.pi * a * (x ⬝ᵥ S.mulVec x)) := by
      rw [centeredMatrixGaussianSummand, Complex.norm_exp]
      simp [x, Complex.mul_re]
    _ ≤ Real.exp (-Real.pi * (a * c) * ∑ i, x i ^ 2) :=
      Real.exp_le_exp.mpr hineq
    _ = ‖∏ i, scalar i (z i)‖ := by
      simp [scalar, x, Complex.norm_exp, ← Real.exp_sum, pow_two,
        Complex.mul_re, Finset.mul_sum]

/-- Centered matrix-Gaussian summability on an arbitrary finite coordinate
type, obtained only by reindexing the certified `Fin` theorem. -/
theorem summable_centeredMatrixGaussianSummand_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (r : ι → ℝ) :
    Summable (centeredMatrixGaussianSummand S a r) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    S.submatrix e e
  let rFin : Fin (Fintype.card ι) → ℝ := fun i => r (e i)
  have hT : T.PosDef := Matrix.PosDef.submatrix_equiv S e hS
  have hfin : Summable (centeredMatrixGaussianSummand T a rFin) :=
    summable_centeredMatrixGaussianSummand T hT ha rFin
  let E : (Fin (Fintype.card ι) → ℤ) ≃ (ι → ℤ) :=
    { toFun := fun z i => z (e.symm i)
      invFun := fun z i => z (e i)
      left_inv := by intro z; ext i; simp
      right_inv := by intro z; ext i; simp }
  apply E.summable_iff.mp
  refine hfin.congr ?_
  intro z
  change centeredMatrixGaussianSummand T a rFin z =
    centeredMatrixGaussianSummand S a r (E z)
  rw [centeredMatrixGaussianSummand, centeredMatrixGaussianSummand]
  have hquad := Matrix.dotProduct_mulVec_submatrix_equiv S e
    (fun i => (z i : ℝ) - rFin i)
  have hvector :
      (fun i : ι => ((E z i : ℤ) : ℝ) - r i) =
        fun i => ((z (e.symm i) : ℤ) : ℝ) - rFin (e.symm i) := by
    funext i
    simp [E, rFin]
  rw [hvector]
  simpa [T] using congrArg
    (fun q : ℝ => Complex.exp (-Real.pi * (a : ℂ) * (q : ℂ))) hquad

/-- The centered inverse-quadratic Gaussian occurring on the Fourier side of
the shifted theta theorem is summable at reciprocal positive scale. -/
theorem summable_centeredMatrixGaussianSummand_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (r : ι → ℝ) :
    Summable (centeredMatrixGaussianSummand S⁻¹ (1 / a) r) :=
  summable_centeredMatrixGaussianSummand_fintype S⁻¹ hS.inv
    (one_div_pos.mpr ha) r

end PositiveDefiniteIntegralLattice
