import SMSFormula.RationalAdeleVectorShiftedGaussianSchur
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Summability for positive-definite matrix Gaussians

The Schur-complement theta induction needs an analytic justification before
the remaining two infinite sums may be interchanged.  This file supplies the
basic coercive estimate and the resulting summability theorem for an
unshifted positive-definite matrix Gaussian at a positive real scale.

The proof works on the existing integer coordinate carrier.  It uses no
diagonalization or new coordinate chart.
-/

noncomputable section

open Matrix Set Filter Asymptotics

namespace PositiveDefiniteIntegralLattice

/-- A real positive-definite matrix dominates a positive multiple of the
standard sum of coordinate squares. -/
theorem _root_.Matrix.PosDef.exists_pos_mul_sum_sq_le
    {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℝ,
      c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ S.mulVec v := by
  by_cases hn : n = 0
  · subst hn
    use 1
    norm_num
  · have hunitLower :
        ∃ c > 0, ∀ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 →
          c ≤ v ⬝ᵥ S.mulVec v := by
      have hcompact : IsCompact {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1} := by
        refine Metric.isCompact_iff_isClosed_bounded.mpr ?_
        exact ⟨isClosed_eq
            (continuous_finset_sum _ fun _ _ => Continuous.pow (continuous_apply _) _)
            continuous_const,
          isBounded_iff_forall_norm_le.mpr ⟨1, by
            rintro v (hv : ∑ i, v i ^ 2 = 1)
            exact pi_norm_le_iff_of_nonneg (by norm_num) |>.2 fun i => by
              simpa [hv] using
                Real.abs_le_sqrt
                  (Finset.single_le_sum (fun i _ => sq_nonneg (v i))
                    (Finset.mem_univ i))⟩⟩
      have hminimum :
          ∃ c ∈ Set.image (fun v : Fin n → ℝ => v ⬝ᵥ S.mulVec v)
              {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1},
            ∀ y ∈ Set.image (fun v : Fin n → ℝ => v ⬝ᵥ S.mulVec v)
                {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1}, c ≤ y := by
        apply_rules [IsCompact.exists_isLeast, hcompact]
        · exact hcompact.image <|
            Continuous.dotProduct continuous_id' <|
              Continuous.matrix_mulVec continuous_const continuous_id'
        · exact ⟨_,
            ⟨fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then 1 else 0,
              by norm_num, rfl⟩⟩
      obtain ⟨c, hc_mem, hc_min⟩ := hminimum
      refine ⟨c, ?_, ?_⟩
      · rcases hc_mem with ⟨x, hx_norm, rfl⟩
        have hx_ne : x ≠ 0 := by
          intro hx
          simp [hx] at hx_norm
        exact hS.dotProduct_mulVec_pos hx_ne
      · intro v hv
        exact hc_min _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc_pos, hc_unit⟩ := hunitLower
    refine ⟨c, hc_pos, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv, Matrix.mulVec, dotProduct]
    · let N : ℝ := ∑ i, v i ^ 2
      have hN_nonneg : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hN_pos : 0 < N := by
        exact lt_of_le_of_ne hN_nonneg <| Ne.symm <| by
          contrapose! hv
          ext i
          simp_all +decide [N, Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg]
      have hunit : (∑ i, (v i / Real.sqrt N) ^ 2) = 1 := by
        norm_num [div_pow, Real.sq_sqrt hN_nonneg]
        rw [← Finset.sum_div, div_self (ne_of_gt hN_pos)]
      have hscale :
          ((fun i => v i / Real.sqrt N) ⬝ᵥ
              S.mulVec (fun i => v i / Real.sqrt N)) * N =
            v ⬝ᵥ S.mulVec v := by
        have hsqrt_ne : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN_pos)
        have hsqrt_sq : Real.sqrt N * Real.sqrt N = N := by
          rw [← pow_two, Real.sq_sqrt hN_nonneg]
        have hinvN : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ * N = 1 := by
          calc
            (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ * N =
                (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ *
                  (Real.sqrt N * Real.sqrt N) := by rw [hsqrt_sq]
            _ = ((Real.sqrt N)⁻¹ * Real.sqrt N) *
                ((Real.sqrt N)⁻¹ * Real.sqrt N) := by ring
            _ = 1 := by rw [inv_mul_cancel₀ hsqrt_ne]; ring
        have hscale_q :
            ((fun i => v i / Real.sqrt N) ⬝ᵥ
                S.mulVec (fun i => v i / Real.sqrt N)) =
              (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ *
                (v ⬝ᵥ S.mulVec v) := by
          simp +decide [div_eq_inv_mul, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
        calc
          ((fun i => v i / Real.sqrt N) ⬝ᵥ
              S.mulVec (fun i => v i / Real.sqrt N)) * N =
              ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ * N) *
                (v ⬝ᵥ S.mulVec v) := by rw [hscale_q]; ring
          _ = v ⬝ᵥ S.mulVec v := by rw [hinvN]; ring
      calc
        c * N ≤ ((fun i => v i / Real.sqrt N) ⬝ᵥ
            S.mulVec (fun i => v i / Real.sqrt N)) * N :=
          mul_le_mul_of_nonneg_right (hc_unit _ hunit) hN_nonneg
        _ = v ⬝ᵥ S.mulVec v := hscale

/-- Scalar complex Gaussians at positive real scale are summable over the
integers. -/
theorem summable_int_gaussian_of_posReal
    {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ =>
      Complex.exp (-Real.pi * (a : ℂ) * (z : ℂ) ^ 2)) := by
  have hpi : 0 < ((Real.pi : ℂ) * (a : ℂ)).re := by
    simpa using mul_pos Real.pi_pos ha
  have hdecay :
      (fun x : ℝ => Complex.exp (-Real.pi * (a : ℂ) * (x : ℂ) ^ 2))
          =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    convert (isLittleO_exp_neg_mul_sq_cocompact hpi (-2)).isBigO using 1
    all_goals simp [mul_assoc]
  exact summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num))
    (hdecay.comp_tendsto Int.tendsto_coe_cofinite)

/-- Translating a positive real scalar Gaussian by a fixed real center
preserves summability over the integers. -/
theorem summable_int_centeredGaussian_of_posReal
    {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Summable (fun z : ℤ =>
      Complex.exp
        (-Real.pi * (a : ℂ) * ((z : ℂ) - (r : ℂ)) ^ 2)) := by
  have hhalf : 0 < a / 2 := div_pos ha (by norm_num)
  let base : ℤ → ℂ := fun z =>
    Complex.exp (-Real.pi * ((a / 2 : ℝ) : ℂ) * (z : ℂ) ^ 2)
  have hbase : Summable base := summable_int_gaussian_of_posReal hhalf
  let constant : ℂ := Complex.exp (Real.pi * a * r ^ 2)
  have hdom : Summable (fun z => constant * base z) := hbase.mul_left constant
  apply Summable.of_norm_bounded hdom.norm
  intro z
  have hsquare :
      (z : ℝ) ^ 2 / 2 - 2 * (z : ℝ) * r + 2 * r ^ 2 =
        ((z : ℝ) - 2 * r) ^ 2 / 2 := by ring
  have hquad : (z : ℝ) ^ 2 / 2 - r ^ 2 ≤ ((z : ℝ) - r) ^ 2 := by
    nlinarith [sq_nonneg ((z : ℝ) - 2 * r)]
  have hexponent :
      -Real.pi * a * ((z : ℝ) - r) ^ 2 ≤
        Real.pi * a * r ^ 2 - Real.pi * (a / 2) * (z : ℝ) ^ 2 := by
    calc
      -Real.pi * a * ((z : ℝ) - r) ^ 2 ≤
          (-Real.pi * a) * ((z : ℝ) ^ 2 / 2 - r ^ 2) :=
        mul_le_mul_of_nonpos_left hquad
          (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr Real.pi_pos.le) ha.le)
      _ = Real.pi * a * r ^ 2 -
          Real.pi * (a / 2) * (z : ℝ) ^ 2 := by ring
  calc
    ‖Complex.exp
        (-Real.pi * (a : ℂ) * ((z : ℂ) - (r : ℂ)) ^ 2)‖ =
        Real.exp (-Real.pi * a * ((z : ℝ) - r) ^ 2) := by
      rw [Complex.norm_exp]
      simp [pow_two, Complex.mul_re]
    _ ≤ Real.exp
        (Real.pi * a * r ^ 2 - Real.pi * (a / 2) * (z : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr hexponent
    _ = ‖constant * base z‖ := by
      simp [constant, base, Complex.norm_exp, ← Real.exp_add, pow_two,
        Complex.mul_re]
      ring

/-- A finite coordinate product of a summable complex family is summable. -/
theorem summable_fin_coordinate_product
    {α : Type*} {f : α → ℂ} (hf : Summable f) (n : ℕ) :
    Summable (fun x : Fin n → α => ∏ i, f (x i)) := by
  induction n with
  | zero =>
      apply summable_of_finite_support
      exact Set.toFinite _
  | succ n ih =>
      let e : (Fin (n + 1) → α) ≃ α × (Fin n → α) :=
        (Fin.insertNthEquiv (fun _ => α) 0).symm
      apply e.symm.summable_iff.mp
      refine (summable_mul_of_summable_norm hf.norm ih.norm).congr ?_
      intro x
      simp [e, Fin.prod_univ_succ]

/-- An unshifted positive-definite matrix Gaussian at positive real scale is
summable on the integer coordinate lattice. -/
theorem summable_shiftedMatrixGaussianSummand_zero
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) :
    Summable (shiftedMatrixGaussianSummand S (a : ℂ) 0) := by
  obtain ⟨c, hc_pos, hc⟩ := hS.exists_pos_mul_sum_sq_le
  have hac : 0 < a * c := mul_pos ha hc_pos
  let scalar : ℤ → ℂ := fun z =>
    Complex.exp (-Real.pi * ((a * c : ℝ) : ℂ) * (z : ℂ) ^ 2)
  have hscalar : Summable scalar := by
    exact summable_int_gaussian_of_posReal hac
  have hproduct : Summable (fun z : Fin n → ℤ => ∏ i, scalar (z i)) :=
    summable_fin_coordinate_product hscalar n
  apply Summable.of_norm_bounded hproduct.norm
  intro z
  have hq := hc (integerVectorReal z)
  have hineq :
      -Real.pi * a *
          (integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)) ≤
        -Real.pi * (a * c) * ∑ i, (z i : ℝ) ^ 2 := by
    calc
      -Real.pi * a *
          (integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)) =
          (-Real.pi * a) *
            (integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)) := by ring
      _ ≤ (-Real.pi * a) * (c * ∑ i, (z i : ℝ) ^ 2) :=
        mul_le_mul_of_nonpos_left (by simpa [integerVectorReal] using hq)
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) ha.le)
      _ = -Real.pi * (a * c) * ∑ i, (z i : ℝ) ^ 2 := by ring
  calc
    ‖shiftedMatrixGaussianSummand S (a : ℂ) 0 z‖ =
        Real.exp (-Real.pi * a *
          (integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z))) := by
      rw [shiftedMatrixGaussianSummand, Complex.norm_exp]
      simp
    _ ≤ Real.exp (-Real.pi * (a * c) * ∑ i, (z i : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr hineq
    _ = ‖∏ i, scalar (z i)‖ := by
      simp [scalar, Complex.norm_exp, ← Real.exp_sum, pow_two,
        Complex.mul_re, Finset.mul_sum]

/-! ## The joint Schur family -/

/-- A real vector regarded as a purely imaginary complex linear term.  This
class of shifts contains the zero input and is preserved by Schur recursion
at positive real scale. -/
def pureImaginaryLinear {ι : Type*} (r : ι → ℝ) : ι → ℂ :=
  fun i => Complex.I * (r i : ℂ)

/-- The real linear term underlying the lower purely imaginary shift after a
Schur step. -/
def sumInrTransformedRealLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (r : Unit ⊕ Fin n → ℝ) (l : ℤ) : Fin n → ℝ :=
  fun j => r (Sum.inr j) +
    (((l : ℝ) - r (Sum.inl ())) /
      S (Sum.inl ()) (Sum.inl ())) * S (Sum.inl ()) (Sum.inr j)

/-- Schur recursion preserves the class of purely imaginary linear terms. -/
theorem sumInrTransformedLinear_pureImaginaryLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0)
    (r : Unit ⊕ Fin n → ℝ) (l : ℤ) :
    sumInrTransformedLinear S (pureImaginaryLinear r) l =
      pureImaginaryLinear (sumInrTransformedRealLinear S r l) := by
  funext j
  simp [sumInrTransformedLinear, pureImaginaryLinear,
    sumInrTransformedRealLinear]
  field_simp [hs]

/-- The joint Schur family with an arbitrary purely imaginary initial linear
term. -/
noncomputable def schurDualGaussianFamilyOfRealLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (a : ℝ) (r : Unit ⊕ Fin n → ℝ) (u : Fin n → ℤ) (l : ℤ) : ℂ :=
  Complex.exp
      (-Real.pi / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) *
        ((l : ℂ) + Complex.I * pureImaginaryLinear r (Sum.inl ())) ^ 2) *
    shiftedMatrixGaussianSummand (sumInrSchurComplement S) (a : ℂ)
      (sumInrTransformedLinear S (pureImaginaryLinear r) l) u

/-- The double family remaining after the head-coordinate theta transform,
specialized to zero initial shift and a positive real scale. -/
noncomputable def schurDualGaussianFamily
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (a : ℝ) (u : Fin n → ℤ) (l : ℤ) : ℂ :=
  Complex.exp
      (-Real.pi / ((a : ℂ) *
          (S (Sum.inl ()) (Sum.inl ()) : ℂ)) * (l : ℂ) ^ 2) *
    shiftedMatrixGaussianSummand (sumInrSchurComplement S) (a : ℂ)
      (sumInrTransformedLinear S 0 l) u

theorem schurDualGaussianFamilyOfRealLinear_zero
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (a : ℝ) (u : Fin n → ℤ) (l : ℤ) :
    schurDualGaussianFamilyOfRealLinear S a 0 u l =
      schurDualGaussianFamily S a u l := by
  have hzero : pureImaginaryLinear (0 : Unit ⊕ Fin n → ℝ) = 0 := by
    funext i
    simp [pureImaginaryLinear]
  rw [schurDualGaussianFamilyOfRealLinear, schurDualGaussianFamily, hzero]
  simp

/-- Positive definiteness forces the distinguished diagonal entry to be
positive. -/
theorem posDef_sumInl_entry_pos
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) :
    0 < S (Sum.inl ()) (Sum.inl ()) := by
  let e : Unit ⊕ Fin n → ℝ := Sum.elim (fun _ : Unit => 1) (fun _ => 0)
  have he : e ≠ 0 := by
    intro he
    have h := congr_fun he (Sum.inl ())
    norm_num [e] at h
  have hpos := hS.dotProduct_mulVec_pos (x := e) he
  simpa [e, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using hpos

/-- The dual-integer-dependent lower shift in the Schur family is a pure
phase. Consequently the norm of the joint summand is exactly the product of
the unshifted head and lower Gaussian norms. -/
theorem norm_schurDualGaussianFamily
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (a : ℝ) (u : Fin n → ℤ) (l : ℤ) :
    ‖schurDualGaussianFamily S a u l‖ =
      ‖Complex.exp
          (-Real.pi *
            (((1 / (a * S (Sum.inl ()) (Sum.inl ())) : ℝ)) : ℂ) *
              (l : ℂ) ^ 2)‖ *
        ‖shiftedMatrixGaussianSummand (sumInrSchurComplement S)
          (a : ℂ) 0 u‖ := by
  rw [schurDualGaussianFamily, norm_mul]
  congr 1
  · rw [Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp [div_eq_mul_inv, pow_two, Complex.mul_re, mul_comm,
      mul_left_comm, mul_assoc]
  · rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand,
      Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp [sumInrTransformedLinear, Complex.div_re, Complex.mul_re,
      Finset.mul_sum]

/-- For a purely imaginary initial shift, the lower transformed linear term
still contributes only a phase.  The norm is a real-centered head Gaussian
times the unshifted lower matrix Gaussian. -/
theorem norm_schurDualGaussianFamilyOfRealLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (a : ℝ) (ha : a ≠ 0)
    (hs : S (Sum.inl ()) (Sum.inl ()) ≠ 0)
    (r : Unit ⊕ Fin n → ℝ) (u : Fin n → ℤ) (l : ℤ) :
    ‖schurDualGaussianFamilyOfRealLinear S a r u l‖ =
      ‖Complex.exp
          (-Real.pi *
            (((1 / (a * S (Sum.inl ()) (Sum.inl ())) : ℝ)) : ℂ) *
              ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)‖ *
        ‖shiftedMatrixGaussianSummand (sumInrSchurComplement S)
          (a : ℂ) 0 u‖ := by
  rw [schurDualGaussianFamilyOfRealLinear, norm_mul]
  congr 1
  · rw [Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp [pureImaginaryLinear, div_eq_mul_inv, pow_two, Complex.mul_re,
      mul_comm, mul_left_comm, mul_assoc, ha, hs]
    ring
  · rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand,
      Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp [sumInrTransformedLinear, pureImaginaryLinear, Complex.div_re,
      Complex.mul_re, Finset.mul_sum]

/-- The explicit tail/dual-integer Schur family is jointly summable.  This is
the analytic certificate needed before the two remaining theta sums may be
interchanged. -/
theorem summable_schurDualGaussianFamily
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a) :
    Summable (fun p : (Fin n → ℤ) × ℤ =>
      schurDualGaussianFamily S a p.1 p.2) := by
  let s : ℝ := S (Sum.inl ()) (Sum.inl ())
  have hs : 0 < s := posDef_sumInl_entry_pos S hS
  have hheadScale : 0 < 1 / (a * s) := one_div_pos.mpr (mul_pos ha hs)
  let head : ℤ → ℂ := fun l =>
    Complex.exp (-Real.pi * ((1 / (a * s) : ℝ) : ℂ) * (l : ℂ) ^ 2)
  let lower : (Fin n → ℤ) → ℂ :=
    shiftedMatrixGaussianSummand (sumInrSchurComplement S) (a : ℂ) 0
  have hhead : Summable head := summable_int_gaussian_of_posReal hheadScale
  have hlower : Summable lower :=
    summable_shiftedMatrixGaussianSummand_zero
      (sumInrSchurComplement S) (sumInrSchurComplement_posDef S hS) ha
  have hproduct : Summable (fun p : (Fin n → ℤ) × ℤ =>
      lower p.1 * head p.2) :=
    summable_mul_of_summable_norm hlower.norm hhead.norm
  apply Summable.of_norm_bounded hproduct.norm
  intro p
  rw [norm_schurDualGaussianFamily]
  simp only [norm_mul]
  change _ ≤ ‖lower p.1‖ * ‖head p.2‖
  simp [lower, head, s, mul_comm]

/-- The joint Schur family is summable for every purely imaginary initial
linear term. This is the stable class of shifts required by the recursive
theta argument. -/
theorem summable_schurDualGaussianFamilyOfRealLinear
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a)
    (r : Unit ⊕ Fin n → ℝ) :
    Summable (fun p : (Fin n → ℤ) × ℤ =>
      schurDualGaussianFamilyOfRealLinear S a r p.1 p.2) := by
  let s : ℝ := S (Sum.inl ()) (Sum.inl ())
  have hs : 0 < s := posDef_sumInl_entry_pos S hS
  have hheadScale : 0 < 1 / (a * s) := one_div_pos.mpr (mul_pos ha hs)
  let head : ℤ → ℂ := fun l =>
    Complex.exp
      (-Real.pi * ((1 / (a * s) : ℝ) : ℂ) *
        ((l : ℂ) - (r (Sum.inl ()) : ℂ)) ^ 2)
  let lower : (Fin n → ℤ) → ℂ :=
    shiftedMatrixGaussianSummand (sumInrSchurComplement S) (a : ℂ) 0
  have hhead : Summable head :=
    summable_int_centeredGaussian_of_posReal hheadScale (r (Sum.inl ()))
  have hlower : Summable lower :=
    summable_shiftedMatrixGaussianSummand_zero
      (sumInrSchurComplement S) (sumInrSchurComplement_posDef S hS) ha
  have hproduct : Summable (fun p : (Fin n → ℤ) × ℤ =>
      lower p.1 * head p.2) :=
    summable_mul_of_summable_norm hlower.norm hhead.norm
  apply Summable.of_norm_bounded hproduct.norm
  intro p
  rw [norm_schurDualGaussianFamilyOfRealLinear S a ha.ne' hs.ne']
  simp only [norm_mul]
  change _ ≤ ‖lower p.1‖ * ‖head p.2‖
  simp [lower, head, s, mul_comm]

/-- Absolute summability justifies exchanging the tail and dual-integer sums
in the Schur family. -/
theorem tsum_schurDualGaussianFamily_comm
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a) :
    (∑' l : ℤ, ∑' u : Fin n → ℤ, schurDualGaussianFamily S a u l) =
      ∑' u : Fin n → ℤ, ∑' l : ℤ, schurDualGaussianFamily S a u l := by
  exact (summable_schurDualGaussianFamily S hS ha).tsum_comm

/-- The stable purely imaginary shifted family admits the same justified
exchange of its tail and dual-integer sums. -/
theorem tsum_schurDualGaussianFamilyOfRealLinear_comm
    {n : ℕ} (S : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ)
    (hS : S.PosDef) {a : ℝ} (ha : 0 < a)
    (r : Unit ⊕ Fin n → ℝ) :
    (∑' l : ℤ, ∑' u : Fin n → ℤ,
        schurDualGaussianFamilyOfRealLinear S a r u l) =
      ∑' u : Fin n → ℤ, ∑' l : ℤ,
        schurDualGaussianFamilyOfRealLinear S a r u l := by
  exact (summable_schurDualGaussianFamilyOfRealLinear S hS ha r).tsum_comm

end PositiveDefiniteIntegralLattice
