import SMSFormula.RationalAdeleVectorShiftedGaussianFiniteTheta

/-!
# Right-half-plane matrix Gaussian theta transformation

Mathlib's scalar Gaussian Poisson theorem is valid for every complex scale
with positive real part.  This file assembles that scalar result by a
Schur-complement argument into the corresponding finite-dimensional
matrix identity.

The proof establishes absolute summability before each reindexing.  The
principal complex square root is used directly, and its compatibility with a
positive real Schur pivot is proved directly from the principal logarithm.

No generic adelic Poisson theorem, Weil representation, Weil index, finite
Gauss reciprocity value, or boundary limit is asserted.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

noncomputable def complexShiftedMatrixThetaNormalization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (b : ℂ) : ℂ :=
  1 / ((b ^ (1 / 2 : ℂ)) ^ Fintype.card ι *
    (Real.sqrt S.det : ℂ))

theorem cpow_half_mul_posReal
    (b : ℂ) (hb : 0 < b.re) (s : ℝ) (hs : 0 < s) :
    (b * (s : ℂ)) ^ (1 / 2 : ℂ) =
      b ^ (1 / 2 : ℂ) * (Real.sqrt s : ℂ) := by
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hb0 hs0),
    Complex.cpow_def_of_ne_zero hb0,
    Complex.log_mul_ofReal s hs b hb0, add_mul, Complex.exp_add]
  calc
    Complex.exp (↑(Real.log s) * (1 / 2)) *
          Complex.exp (Complex.log b * (1 / 2)) =
        Complex.exp (Complex.log b * (1 / 2)) *
          Complex.exp (↑(Real.log s) * (1 / 2)) := mul_comm _ _
    _ = Complex.exp (Complex.log b * (1 / 2)) *
          (Real.sqrt s : ℂ) := by
      congr 1
      simp [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hs]

theorem sqrt_det_eq_head_mul_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) :
    Real.sqrt S.det =
      Real.sqrt (S (Sum.inl ()) (Sum.inl ())) *
        Real.sqrt (sumInrSchurComplement S).det := by
  rw [det_eq_head_mul_sumInrSchurComplement_det S hS,
    Real.sqrt_mul]
  exact (posDef_sumInl_entry_pos S hS).le

theorem scalar_mul_complexNormalization_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re) :
    1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        complexShiftedMatrixThetaNormalization
          (sumInrSchurComplement S) b =
      complexShiftedMatrixThetaNormalization S b := by
  have hs : 0 < S (Sum.inl ()) (Sum.inl ()) :=
    posDef_sumInl_entry_pos S hS
  rw [cpow_half_mul_posReal b hb _ hs]
  rw [complexShiftedMatrixThetaNormalization,
    complexShiftedMatrixThetaNormalization]
  rw [sqrt_det_eq_head_mul_schur S hS]
  simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
  push_cast
  ring

noncomputable def complexCenteredMatrixGaussianSummand
    {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (b : ℂ)
    (r : ι → ℝ) (z : ι → ℤ) : ℂ :=
  let x : ι → ℝ := fun i => (z i : ℝ) - r i
  Complex.exp
    (-Real.pi * b * ((x ⬝ᵥ S.mulVec x : ℝ) : ℂ))

theorem norm_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (b : ℂ) (r : ι → ℝ) (z : ι → ℤ) :
    ‖shiftedMatrixGaussianSummand S b (pureImaginaryLinear r) z‖ =
      ‖shiftedMatrixGaussianSummand S (b.re : ℂ) 0 z‖ := by
  rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand,
    Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [pureImaginaryLinear, Complex.mul_re]

theorem summable_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : ι → ℝ) :
    Summable (shiftedMatrixGaussianSummand S b (pureImaginaryLinear r)) := by
  apply Summable.of_norm_bounded
    (summable_shiftedMatrixGaussianSummand_zero_fintype S hS hb).norm
  intro z
  exact le_of_eq
    (norm_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear S b r z)

theorem norm_complexCenteredMatrixGaussianSummand
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (b : ℂ) (r : ι → ℝ) (z : ι → ℤ) :
    ‖complexCenteredMatrixGaussianSummand S b r z‖ =
      ‖centeredMatrixGaussianSummand S b.re r z‖ := by
  rw [complexCenteredMatrixGaussianSummand,
    centeredMatrixGaussianSummand, Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem summable_complexCenteredMatrixGaussianSummand_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : ι → ℝ) :
    Summable (complexCenteredMatrixGaussianSummand S b r) := by
  apply Summable.of_norm_bounded
    (summable_centeredMatrixGaussianSummand_fintype S hS hb r).norm
  intro z
  exact le_of_eq (norm_complexCenteredMatrixGaussianSummand S b r z)

theorem inv_re_pos {b : ℂ} (hb : 0 < b.re) : 0 < b⁻¹.re := by
  rw [Complex.inv_re]
  exact div_pos hb (Complex.normSq_pos.mpr fun h => by simp [h] at hb)

theorem summable_complexCenteredMatrixGaussianSummand_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : ι → ℝ) :
    Summable (complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r) :=
  summable_complexCenteredMatrixGaussianSummand_fintype
    S⁻¹ hS.inv (inv_re_pos hb) r

noncomputable def complexSchurDualGaussianFamilyOfRealLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (b : ℂ) (r : Unit ⊕ Fin n → ℝ)
    (u : Fin n → ℤ) (l : ℤ) : ℂ :=
  Complex.exp
      (-Real.pi / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
        ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2) *
    shiftedMatrixGaussianSummand (sumInrSchurComplement S) b
      (pureImaginaryLinear (sumInrTransformedRealLinear S r l)) u

theorem summable_complexSchurDualGaussianFamilyOfRealLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : Unit ⊕ Fin n → ℝ) :
    Summable (fun p : (Fin n → ℤ) × ℤ =>
      complexSchurDualGaussianFamilyOfRealLinear S b r p.1 p.2) := by
  let s : ℝ := S (Sum.inl ()) (Sum.inl ())
  have hs : 0 < s := posDef_sumInl_entry_pos S hS
  have hbs : 0 < (b * (s : ℂ)).re := by
    simpa [s] using mul_pos hb hs
  let c : ℂ := (b * (s : ℂ))⁻¹
  have hinv : 0 < c.re := inv_re_pos hbs
  let head : ℤ → ℂ := fun l =>
    Complex.exp
      (-Real.pi * ((c.re : ℝ) : ℂ) *
        ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)
  let lower : (Fin n → ℤ) → ℂ :=
    shiftedMatrixGaussianSummand (sumInrSchurComplement S) (b.re : ℂ) 0
  have hhead : Summable head :=
    summable_int_centeredGaussian_of_posReal hinv (r (Sum.inl ()))
  have hlower : Summable lower :=
    summable_shiftedMatrixGaussianSummand_zero_fintype
      (sumInrSchurComplement S) (sumInrSchurComplement_posDef S hS) hb
  have hproduct : Summable (fun p : (Fin n → ℤ) × ℤ =>
      lower p.1 * head p.2) :=
    summable_mul_of_summable_norm hlower.norm hhead.norm
  apply Summable.of_norm_bounded hproduct.norm
  rintro ⟨u, l⟩
  have hheadNorm :
      ‖Complex.exp
          (-Real.pi / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
            ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)‖ =
        ‖head l‖ := by
    change
      ‖Complex.exp (-Real.pi * c *
          ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)‖ =
        ‖Complex.exp (-Real.pi * (c.re : ℂ) *
          ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)‖
    have himag :
        (((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2).im = 0 := by
      simp [pow_two, Complex.mul_im]
    rw [Complex.norm_exp, Complex.norm_exp]
    apply congrArg Real.exp
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [himag]
    simp
  have hlowerNorm :
      ‖shiftedMatrixGaussianSummand (sumInrSchurComplement S) b
          (pureImaginaryLinear (sumInrTransformedRealLinear S r l)) u‖ =
        ‖lower u‖ :=
    norm_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear
      (sumInrSchurComplement S) b
      (sumInrTransformedRealLinear S r l) u
  rw [complexSchurDualGaussianFamilyOfRealLinear, norm_mul,
    hheadNorm, hlowerNorm, mul_comm, norm_mul]

theorem tsum_complexSchurDualGaussianFamilyOfRealLinear_comm
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : Unit ⊕ Fin n → ℝ) :
    (∑' l : ℤ, ∑' u : Fin n → ℤ,
        complexSchurDualGaussianFamilyOfRealLinear S b r u l) =
      ∑' u : Fin n → ℤ, ∑' l : ℤ,
        complexSchurDualGaussianFamilyOfRealLinear S b r u l := by
  exact (summable_complexSchurDualGaussianFamilyOfRealLinear
    S hS hb r).tsum_comm

theorem tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : Unit ⊕ Fin n → ℝ) :
    (∑' z : Unit ⊕ Fin n → ℤ,
      shiftedMatrixGaussianSummand S b (pureImaginaryLinear r) z) =
      1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        ∑' l : ℤ,
          Complex.exp
              (-Real.pi / (b *
                  (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
                ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2) *
            ∑' u : Fin n → ℤ,
              shiftedMatrixGaussianSummand (sumInrSchurComplement S) b
                (pureImaginaryLinear
                  (sumInrTransformedRealLinear S r l)) u := by
  let f : (Unit ⊕ Fin n → ℤ) → ℂ :=
    shiftedMatrixGaussianSummand S b (pureImaginaryLinear r)
  let e : ((Fin n → ℤ) × ℤ) ≃ (Unit ⊕ Fin n → ℤ) :=
    sumInrIntegerVectorEquiv
  have hf : Summable f :=
    summable_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear
      S hS hb r
  have hpair : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  have hs : 0 < S (Sum.inl ()) (Sum.inl ()) :=
    posDef_sumInl_entry_pos S hS
  have hslice : ∀ u : Fin n → ℤ,
      (∑' k : ℤ, f (e (u, k))) =
        1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^
            (1 / 2 : ℂ) *
          ∑' l : ℤ,
            complexSchurDualGaussianFamilyOfRealLinear S b r u l := by
    intro u
    simpa [f, e, complexSchurDualGaussianFamilyOfRealLinear,
      pureImaginaryLinear, ← mul_assoc, ← pow_two, Complex.I_sq,
      sumInrTransformedLinear_pureImaginaryLinear S hs.ne' r] using
        (tsum_shiftedMatrixGaussianSummand_sum_eq_schur
          S hS hb (pureImaginaryLinear r) u)
  calc
    (∑' z : Unit ⊕ Fin n → ℤ,
        shiftedMatrixGaussianSummand S b (pureImaginaryLinear r) z) =
        ∑' p : (Fin n → ℤ) × ℤ, f (e p) := by
      simpa [f] using (e.tsum_eq f).symm
    _ = ∑' u : Fin n → ℤ, ∑' k : ℤ, f (e (u, k)) :=
      hpair.tsum_prod
    _ = ∑' u : Fin n → ℤ,
        1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^
            (1 / 2 : ℂ) *
          ∑' l : ℤ,
            complexSchurDualGaussianFamilyOfRealLinear S b r u l := by
      apply tsum_congr
      exact hslice
    _ = 1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^
          (1 / 2 : ℂ) *
        ∑' u : Fin n → ℤ, ∑' l : ℤ,
          complexSchurDualGaussianFamilyOfRealLinear S b r u l := by
      rw [tsum_mul_left]
    _ = 1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^
          (1 / 2 : ℂ) *
        ∑' l : ℤ, ∑' u : Fin n → ℤ,
          complexSchurDualGaussianFamilyOfRealLinear S b r u l := by
      rw [← tsum_complexSchurDualGaussianFamilyOfRealLinear_comm
        S hS hb r]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro l
      rw [← tsum_mul_left]
      rfl

theorem complexCenteredMatrixGaussianSummand_inv_eq_head_mul_schur
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : Unit ⊕ Fin n → ℝ) (l : ℤ) (v : Fin n → ℤ) :
    complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r
        (Sum.elim (fun _ => l) v) =
      Complex.exp
          (-Real.pi / (b *
              (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
            ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2) *
        complexCenteredMatrixGaussianSummand
          (sumInrSchurComplement S)⁻¹ b⁻¹
          (sumInrTransformedRealLinear S r l) v := by
  have hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0 :=
    (posDef_sumInl_entry_pos S hS).ne'
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  have hquad := shiftedInverseQuadratic_eq_sumInrSchur S hS r l v
  rw [complexCenteredMatrixGaussianSummand,
    complexCenteredMatrixGaussianSummand]
  have hy :
      (fun i => ((Sum.elim (fun _ : Unit => l) v i : ℤ) : ℝ) - r i) =
        Sum.elim (fun _ => (l : ℝ) - r (Sum.inl ()))
          (fun j => (v j : ℝ) - r (Sum.inr j)) := by
    funext i
    rcases i with i | i
    · cases i
      rfl
    · rfl
  rw [hy, hquad, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [hb0, hs]
  ring

private theorem tsum_shiftedMatrixGaussianSummand_complex_sum_eq_centered_inv_of_lower
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {b : ℂ} (hb : 0 < b.re)
    (r : Unit ⊕ Fin n → ℝ)
    (hlower :
      ∀ (W : Matrix (Fin n) (Fin n) ℝ), W.PosDef →
        ∀ rW : Fin n → ℝ,
          (∑' u : Fin n → ℤ,
              shiftedMatrixGaussianSummand W b
                (pureImaginaryLinear rW) u) =
            complexShiftedMatrixThetaNormalization W b *
              ∑' v : Fin n → ℤ,
                complexCenteredMatrixGaussianSummand W⁻¹ b⁻¹ rW v) :
    (∑' z : Unit ⊕ Fin n → ℤ,
        shiftedMatrixGaussianSummand S b
          (pureImaginaryLinear r) z) =
      complexShiftedMatrixThetaNormalization S b *
        ∑' y : Unit ⊕ Fin n → ℤ,
          complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r y := by
  let W : Matrix (Fin n) (Fin n) ℝ := sumInrSchurComplement S
  let head : ℤ → ℂ := fun l =>
    Complex.exp
      (-Real.pi / (b *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
        ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)
  let lower : ℤ → ℂ := fun l =>
    ∑' v : Fin n → ℤ,
      complexCenteredMatrixGaussianSummand W⁻¹ b⁻¹
        (sumInrTransformedRealLinear S r l) v
  have hW : W.PosDef := sumInrSchurComplement_posDef S hS
  have hrec :=
    tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_schur
      S hS hb r
  rw [hrec]
  have hlower' : ∀ l : ℤ,
      (∑' u : Fin n → ℤ,
          shiftedMatrixGaussianSummand W b
            (pureImaginaryLinear
              (sumInrTransformedRealLinear S r l)) u) =
        complexShiftedMatrixThetaNormalization W b * lower l := by
    intro l
    exact hlower W hW (sumInrTransformedRealLinear S r l)
  change
    1 / (b * (S (Sum.inl ()) (Sum.inl ()) : ℂ)) ^ (1 / 2 : ℂ) *
        (∑' l : ℤ, head l *
          ∑' u : Fin n → ℤ,
            shiftedMatrixGaussianSummand W b
              (pureImaginaryLinear
                (sumInrTransformedRealLinear S r l)) u) = _
  simp_rw [hlower']
  have hfactor :
      (∑' l : ℤ,
          head l *
            (complexShiftedMatrixThetaNormalization W b * lower l)) =
        complexShiftedMatrixThetaNormalization W b *
          ∑' l : ℤ, head l * lower l := by
    calc
      _ = ∑' l : ℤ,
          complexShiftedMatrixThetaNormalization W b *
            (head l * lower l) := by
        apply tsum_congr
        intro l
        ring
      _ = _ := tsum_mul_left
  rw [hfactor, ← mul_assoc,
    scalar_mul_complexNormalization_schur S hS hb]
  congr 1
  let E : ((Fin n → ℤ) × ℤ) ≃ (Unit ⊕ Fin n → ℤ) :=
    sumInrIntegerVectorEquiv
  have hfull : Summable
      (complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r) :=
    summable_complexCenteredMatrixGaussianSummand_inv S hS hb r
  have hpair : Summable (fun p : (Fin n → ℤ) × ℤ =>
      complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r (E p)) :=
    E.summable_iff.mpr hfull
  calc
    (∑' l : ℤ, head l * lower l) =
        ∑' l : ℤ, ∑' v : Fin n → ℤ,
          complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r (E (v, l)) := by
      apply tsum_congr
      intro l
      rw [← tsum_mul_left]
      apply tsum_congr
      intro v
      exact
        (complexCenteredMatrixGaussianSummand_inv_eq_head_mul_schur
          S hS hb r l v).symm
    _ = ∑' v : Fin n → ℤ, ∑' l : ℤ,
          complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r (E (v, l)) :=
      hpair.tsum_comm
    _ = ∑' p : (Fin n → ℤ) × ℤ,
          complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r (E p) :=
      hpair.tsum_prod.symm
    _ = ∑' y : Unit ⊕ Fin n → ℤ,
          complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r y :=
      E.tsum_eq _

private theorem shiftedMatrixGaussianSummand_complex_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (b : ℂ)
    (r : α → ℝ) (z : β → ℤ) :
    shiftedMatrixGaussianSummand (S.submatrix e e) b
        (pureImaginaryLinear (fun i => r (e i))) z =
      shiftedMatrixGaussianSummand S b
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

private theorem complexCenteredMatrixGaussianSummand_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℝ) (e : β ≃ α) (b : ℂ)
    (r : α → ℝ) (z : β → ℤ) :
    complexCenteredMatrixGaussianSummand (S.submatrix e e) b
        (fun i => r (e i)) z =
      complexCenteredMatrixGaussianSummand S b r
        (fun i => z (e.symm i)) := by
  rw [complexCenteredMatrixGaussianSummand,
    complexCenteredMatrixGaussianSummand]
  have hquad := Matrix.dotProduct_mulVec_submatrix_equiv S e
    (fun i => (z i : ℝ) - r (e i))
  have hvector :
      (fun i : α => (z (e.symm i) : ℝ) - r i) =
        fun i => (z (e.symm i) : ℝ) - r (e (e.symm i)) := by
    funext i
    simp
  rw [hvector]
  simpa using congrArg
    (fun q : ℝ => Complex.exp (-Real.pi * b * (q : ℂ))) hquad

private theorem complexShiftedMatrixThetaNormalization_submatrix_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S : Matrix α α ℝ) (e : β ≃ α) (b : ℂ) :
    complexShiftedMatrixThetaNormalization (S.submatrix e e) b =
      complexShiftedMatrixThetaNormalization S b := by
  have hcard : Fintype.card β = Fintype.card α := Fintype.card_congr e
  simp [complexShiftedMatrixThetaNormalization,
    Matrix.det_submatrix_equiv_self, hcard]

theorem tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_centered_inv
    (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) (r : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S b
          (pureImaginaryLinear r) z) =
      complexShiftedMatrixThetaNormalization S b *
        ∑' y : Fin n → ℤ,
          complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r y := by
  induction n with
  | zero =>
      simp [shiftedMatrixGaussianSummand,
        complexCenteredMatrixGaussianSummand,
        complexShiftedMatrixThetaNormalization, pureImaginaryLinear,
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
              shiftedMatrixGaussianSummand T b
                (pureImaginaryLinear rT) z) =
            complexShiftedMatrixThetaNormalization T b *
              ∑' y : Unit ⊕ Fin n → ℤ,
                complexCenteredMatrixGaussianSummand T⁻¹ b⁻¹ rT y := by
        apply
          tsum_shiftedMatrixGaussianSummand_complex_sum_eq_centered_inv_of_lower
            T hT hb rT
        intro W hW rW
        exact ih W hW rW
      let E : (Unit ⊕ Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
        { toFun := fun z i => z (e.symm i)
          invFun := fun z i => z (e i)
          left_inv := by intro z; ext i; simp
          right_inv := by intro z; ext i; simp }
      have hleft :
          (∑' z : Unit ⊕ Fin n → ℤ,
              shiftedMatrixGaussianSummand T b
                (pureImaginaryLinear rT) z) =
            ∑' z : Fin (n + 1) → ℤ,
              shiftedMatrixGaussianSummand S b
                (pureImaginaryLinear r) z := by
        calc
          _ = ∑' z : Unit ⊕ Fin n → ℤ,
                shiftedMatrixGaussianSummand S b
                  (pureImaginaryLinear r) (E z) := by
              apply tsum_congr
              intro z
              exact shiftedMatrixGaussianSummand_complex_submatrix_equiv
                S e b r z
          _ = _ := E.tsum_eq _
      have hnormalization :
          complexShiftedMatrixThetaNormalization T b =
            complexShiftedMatrixThetaNormalization S b :=
        complexShiftedMatrixThetaNormalization_submatrix_equiv S e b
      have hinv : T⁻¹ = S⁻¹.submatrix e e := by
        change (S.submatrix e e)⁻¹ = S⁻¹.submatrix e e
        exact Matrix.inv_submatrix_equiv S e e
      have hright :
          (∑' y : Unit ⊕ Fin n → ℤ,
              complexCenteredMatrixGaussianSummand T⁻¹ b⁻¹ rT y) =
            ∑' y : Fin (n + 1) → ℤ,
              complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r y := by
        rw [hinv]
        calc
          _ = ∑' y : Unit ⊕ Fin n → ℤ,
                complexCenteredMatrixGaussianSummand S⁻¹ b⁻¹ r (E y) := by
              apply tsum_congr
              intro y
              exact complexCenteredMatrixGaussianSummand_submatrix_equiv
                S⁻¹ e b⁻¹ r y
          _ = _ := E.tsum_eq _
      rw [hleft, hnormalization, hright] at hnative
      exact hnative

@[simp]
theorem complexCenteredMatrixGaussianSummand_zero
    {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (b : ℂ) (z : ι → ℤ) :
    complexCenteredMatrixGaussianSummand S b 0 z =
      shiftedMatrixGaussianSummand S b 0 z := by
  rw [complexCenteredMatrixGaussianSummand,
    shiftedMatrixGaussianSummand]
  simp only [Pi.zero_apply, sub_zero]
  rw [show (fun i => (z i : ℝ)) = integerVectorReal z by rfl]
  simp

/-- An integral matrix unit acts bijectively on integer coordinate vectors by
matrix-vector multiplication. -/
noncomputable def integerMatrixUnitMulVecEquiv (n : ℕ)
    (U : (Matrix (Fin n) (Fin n) ℤ)ˣ) : (Fin n → ℤ) ≃ (Fin n → ℤ) where
  toFun z := U.val.mulVec z
  invFun z := U.inv.mulVec z
  left_inv z := by
    dsimp
    rw [Matrix.mulVec_mulVec, show (↑U⁻¹ * ↑U : Matrix (Fin n) (Fin n) ℤ) = 1 by
      exact U.inv_mul]
    rw [Matrix.one_mulVec]
  right_inv z := by
    dsimp
    rw [Matrix.mulVec_mulVec, show (↑U * ↑U⁻¹ : Matrix (Fin n) (Fin n) ℤ) = 1 by
      exact U.mul_inv]
    rw [Matrix.one_mulVec]

/-- Reindex an integer theta sum by an integral matrix unit.  This is the
abstract reindexing step needed before applying determinant-one integrality to
the inverse theta in the Type II obstruction route. -/
theorem tsum_comp_integerMatrixUnit_mulVec (n : ℕ)
    (U : (Matrix (Fin n) (Fin n) ℤ)ˣ) (f : (Fin n → ℤ) → ℂ) :
    (∑' z : Fin n → ℤ, f (U.val.mulVec z)) = ∑' z : Fin n → ℤ, f z := by
  simpa [integerMatrixUnitMulVecEquiv] using
    (integerMatrixUnitMulVecEquiv n U).tsum_eq f

/-- A square integer matrix with determinant `1` is a unit. -/
theorem integerMatrix_isUnit_of_det_eq_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det = 1) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, hdet]
  exact isUnit_one

/-- Reindex an integer theta sum by a determinant-one integer matrix. -/
theorem tsum_comp_integerMatrix_mulVec_of_det_eq_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det = 1)
    (f : (Fin n → ℤ) → ℂ) :
    (∑' z : Fin n → ℤ, f (A.mulVec z)) = ∑' z : Fin n → ℤ, f z := by
  rcases integerMatrix_isUnit_of_det_eq_one A hdet with ⟨U, hU⟩
  subst hU
  exact tsum_comp_integerMatrixUnit_mulVec n U f

theorem tsum_shiftedMatrixGaussianSummand_complex_zero_eq_inv
    (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {b : ℂ} (hb : 0 < b.re) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S b 0 z) =
      complexShiftedMatrixThetaNormalization S b *
        ∑' y : Fin n → ℤ,
          shiftedMatrixGaussianSummand S⁻¹ b⁻¹ 0 y := by
  have hzero : pureImaginaryLinear (0 : Fin n → ℝ) = 0 := by
    funext i
    simp [pureImaginaryLinear]
  have h :=
    tsum_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear_eq_centered_inv
      n S hS hb (0 : Fin n → ℝ)
  rw [hzero] at h
  simpa only [complexCenteredMatrixGaussianSummand_zero] using h

/-- The inverse of the complex scale `1 + i`, written in the form used by the
Type II obstruction theta comparison. -/
theorem one_add_complex_I_inv :
    (1 + Complex.I : ℂ)⁻¹ = (1 - Complex.I) / 2 := by
  apply inv_eq_of_mul_eq_one_right
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- The right-half-plane theta identity specialized to the Type II rank-obstruction
scale `1 + i`, with the inverse scale simplified to `(1 - i) / 2`. -/
theorem tsum_shiftedMatrixGaussianSummand_complex_zero_eq_inv_one_add_I
    (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S (1 + Complex.I) 0 z) =
      complexShiftedMatrixThetaNormalization S (1 + Complex.I) *
        ∑' y : Fin n → ℤ,
          shiftedMatrixGaussianSummand S⁻¹ ((1 - Complex.I) / 2) 0 y := by
  have h :=
    tsum_shiftedMatrixGaussianSummand_complex_zero_eq_inv n S hS
      (b := 1 + Complex.I) (by norm_num)
  simpa [one_add_complex_I_inv] using h

end PositiveDefiniteIntegralLattice
