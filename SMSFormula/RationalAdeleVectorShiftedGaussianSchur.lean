import SMSFormula.RationalAdeleVectorShiftedGaussianTheta

/-!
# Schur-complement form of the shifted Gaussian theta slice

After applying the scalar linear-term theta identity in the distinguished
coordinate of a `Unit ⊕ m` matrix, the transformed exponent must be rewritten
as a Gaussian for the positive Schur complement.  The new lower-rank linear
term depends on the dual integer `l`:

`tailLinear + ((I * l - headLinear) / s) * crossRow`.

This file proves that exact phase identity and its matrix specialization.  It
does not interchange the remaining two infinite sums or assert a complete
finite-dimensional theta transformation.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- The lower-right Schur complement of the distinguished `Unit` block. -/
def sumInrSchurComplement {m : Type*}
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) : Matrix m m ℝ :=
  let A : Matrix Unit Unit ℝ := S.submatrix Sum.inl Sum.inl
  let B : Matrix Unit m ℝ := S.submatrix Sum.inl Sum.inr
  let C : Matrix m Unit ℝ := S.submatrix Sum.inr Sum.inl
  let D : Matrix m m ℝ := S.submatrix Sum.inr Sum.inr
  D - C * A⁻¹ * B

/-- The off-diagonal row paired with a tail vector. -/
def sumInrCross {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (u : m → ℤ) : ℝ :=
  ∑ j, S (Sum.inl ()) (Sum.inr j) * (u j : ℝ)

/-- The lower-rank shift after scalar theta transformation in the head
coordinate. -/
def sumInrTransformedLinear {m : Type*}
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ)
    (linear : Unit ⊕ m → ℂ) (l : ℤ) : m → ℂ :=
  fun j => linear (Sum.inr j) +
    ((Complex.I * (l : ℂ) - linear (Sum.inl ())) /
      (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
        (S (Sum.inl ()) (Sum.inr j) : ℂ)

/-- Pure scalar phase algebra underlying the Schur-complement rewrite. -/
theorem exp_block_dual_factor_eq_schur
    {b : ℂ} (hb : 0 < b.re) {s : ℝ} (hs : 0 < s)
    (cross tailQuadratic schurQuadratic : ℝ)
    (headLinear tailLinear : ℂ) (l : ℤ)
    (hquadratic : tailQuadratic = cross ^ 2 / s + schurQuadratic) :
    Complex.exp
        (-Real.pi * b * (tailQuadratic : ℂ) +
          2 * Real.pi * tailLinear) *
      Complex.exp
        (-Real.pi / (b * (s : ℂ)) *
          ((l : ℂ) + Complex.I *
            (headLinear - b * (cross : ℂ))) ^ 2) =
      Complex.exp
          (-Real.pi / (b * (s : ℂ)) *
            ((l : ℂ) + Complex.I * headLinear) ^ 2) *
        Complex.exp
          (-Real.pi * b * (schurQuadratic : ℂ) +
            2 * Real.pi *
              (tailLinear +
                ((Complex.I * (l : ℂ) - headLinear) / (s : ℂ)) *
                  (cross : ℂ))) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hquadratic]
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  push_cast
  field_simp [hb0, hs0]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem sumInrSchurComplement_posDef {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef) :
    (sumInrSchurComplement S).PosDef := by
  simpa [sumInrSchurComplement] using hS.schurComplement_sum_inr S

/-- The lower-block quadratic form is the Schur quadratic plus the exact
rank-one correction `cross(u)^2 / s`. -/
theorem tailQuadratic_eq_cross_sq_div_add_schur {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef)
    (u : m → ℤ) :
    integerVectorReal u ⬝ᵥ
        (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u) =
      (sumInrCross S u) ^ 2 /
          S (Sum.inl ()) (Sum.inl ()) +
        integerVectorReal u ⬝ᵥ
          (sumInrSchurComplement S).mulVec (integerVectorReal u) := by
  have hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0 := by
    exact ne_of_gt (by
      let e : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ : m => 0)
      have he : e ≠ 0 := by
        intro he
        have h : e (Sum.inl ()) = 0 := congr_fun he (Sum.inl ())
        norm_num [e] at h
      have hpos := hS.dotProduct_mulVec_pos (x := e) he
      simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos)
  have h := Matrix.dotProduct_mulVec_sum_schurComplement_inr
    S (by simpa [Matrix.IsSymm] using hS.isHermitian) hs 0 (integerVectorReal u)
  dsimp only at h
  have hleft :
      (Sum.elim (fun _ : Unit => 0) (integerVectorReal u)) ⬝ᵥ
          S.mulVec (Sum.elim (fun _ : Unit => 0) (integerVectorReal u)) =
        integerVectorReal u ⬝ᵥ
          (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u) := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  rw [hleft] at h
  calc
    integerVectorReal u ⬝ᵥ
          (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u) =
        S (Sum.inl ()) (Sum.inl ()) *
            ((S (Sum.inl ()) (Sum.inl ()))⁻¹ * sumInrCross S u) ^ 2 +
          integerVectorReal u ⬝ᵥ
            (sumInrSchurComplement S).mulVec (integerVectorReal u) := by
      simpa [sumInrSchurComplement, sumInrCross, integerVectorReal] using h
    _ = (sumInrCross S u) ^ 2 /
          S (Sum.inl ()) (Sum.inl ()) +
        integerVectorReal u ⬝ᵥ
          (sumInrSchurComplement S).mulVec (integerVectorReal u) := by
      field_simp [hs]

/-- Exact pointwise Schur-complement factorization of the transformed scalar
theta summand. The dual integer remains explicit in the lower-rank shift. -/
theorem exp_fixedTail_dual_eq_schurSummand
    {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) (linear : Unit ⊕ m → ℂ)
    (u : m → ℤ) (l : ℤ) :
    let s : ℝ := S (Sum.inl ()) (Sum.inl ())
    let tailQuadratic : ℝ :=
      integerVectorReal u ⬝ᵥ
        (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u)
    let tailLinear : ℂ := ∑ j, linear (Sum.inr j) * (u j : ℂ)
    Complex.exp
        (-Real.pi * b * (tailQuadratic : ℂ) +
          2 * Real.pi * tailLinear) *
      Complex.exp
        (-Real.pi / (b * (s : ℂ)) *
          ((l : ℂ) + Complex.I *
            (linear (Sum.inl ()) - b * (sumInrCross S u : ℂ))) ^ 2) =
      Complex.exp
          (-Real.pi / (b * (s : ℂ)) *
            ((l : ℂ) + Complex.I * linear (Sum.inl ())) ^ 2) *
        shiftedMatrixGaussianSummand (sumInrSchurComplement S) b
          (sumInrTransformedLinear S linear l) u := by
  dsimp only
  rw [shiftedMatrixGaussianSummand]
  let alpha : ℂ :=
    (Complex.I * (l : ℂ) - linear (Sum.inl ())) /
      (S (Sum.inl ()) (Sum.inl ()) : ℂ)
  have htailLinear :
      (∑ j, sumInrTransformedLinear S linear l j * (u j : ℂ)) =
        (∑ j, linear (Sum.inr j) * (u j : ℂ)) +
          alpha * (sumInrCross S u : ℂ) := by
    change (∑ j,
      (linear (Sum.inr j) + alpha *
        (S (Sum.inl ()) (Sum.inr j) : ℂ)) * (u j : ℂ)) = _
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [sumInrCross]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [htailLinear]
  change _ = Complex.exp _ * Complex.exp
    (-Real.pi * b *
        ((integerVectorReal u ⬝ᵥ
          (sumInrSchurComplement S).mulVec (integerVectorReal u) : ℝ) : ℂ) +
      2 * Real.pi *
        ((∑ j, linear (Sum.inr j) * (u j : ℂ)) +
          ((Complex.I * (l : ℂ) - linear (Sum.inl ())) /
            (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
              (sumInrCross S u : ℂ)))
  exact exp_block_dual_factor_eq_schur hb
    (by
      let e : Unit ⊕ m → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ : m => 0)
      have he : e ≠ 0 := by
        intro he
        have h : e (Sum.inl ()) = 0 := congr_fun he (Sum.inl ())
        norm_num [e] at h
      have hpos := hS.dotProduct_mulVec_pos (x := e) he
      simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos)
    (sumInrCross S u)
    (integerVectorReal u ⬝ᵥ
      (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u))
    (integerVectorReal u ⬝ᵥ
      (sumInrSchurComplement S).mulVec (integerVectorReal u))
    (linear (Sum.inl ()))
    (∑ j, linear (Sum.inr j) * (u j : ℂ)) l
    (tailQuadratic_eq_cross_sq_div_add_schur S hS u)

/-- The complete fixed-tail scalar sum in Schur-complement form.  The
lower-rank theta summand has an `l`-dependent shift, but no interchange with
the outer sum over tail vectors is performed. -/
theorem tsum_shiftedMatrixGaussianSummand_sum_eq_schur
    {m : Type*} [Fintype m]
    (S : Matrix (Unit ⊕ m) (Unit ⊕ m) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) (linear : Unit ⊕ m → ℂ) (u : m → ℤ) :
    let s : ℝ := S (Sum.inl ()) (Sum.inl ())
    (∑' k : ℤ, shiftedMatrixGaussianSummand S b linear
      (Sum.elim (fun _ : Unit => k) u)) =
      1 / (b * (s : ℂ)) ^ (1 / 2 : ℂ) *
        ∑' l : ℤ,
          Complex.exp
              (-Real.pi / (b * (s : ℂ)) *
                ((l : ℂ) + Complex.I * linear (Sum.inl ())) ^ 2) *
            shiftedMatrixGaussianSummand (sumInrSchurComplement S) b
              (sumInrTransformedLinear S linear l) u := by
  dsimp only
  rw [tsum_shiftedMatrixGaussianSummand_sum S hS hb linear u]
  let tailFactor : ℂ :=
    Complex.exp
      (-Real.pi * b *
          ((integerVectorReal u ⬝ᵥ
            (S.submatrix Sum.inr Sum.inr).mulVec (integerVectorReal u) : ℝ) : ℂ) +
        2 * Real.pi * ∑ j, linear (Sum.inr j) * (u j : ℂ))
  let scalarDual : ℤ → ℂ := fun l =>
    Complex.exp
      (-Real.pi / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
        ((l : ℂ) + Complex.I *
          (linear (Sum.inl ()) - b * (sumInrCross S u : ℂ))) ^ 2)
  calc
    tailFactor *
        (1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
          ∑' l : ℤ, scalarDual l) =
      1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        (tailFactor * ∑' l : ℤ, scalarDual l) := by ring
    _ = 1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        ∑' l : ℤ, tailFactor * scalarDual l := by
      rw [← tsum_mul_left]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro l
      exact exp_fixedTail_dual_eq_schurSummand S hS hb linear u l

end PositiveDefiniteIntegralLattice
