import SMSFormula.RationalAdeleVectorCenteredGaussianAbel

/-!
# Periodic Gaussian Abel limits

This file splits the integer lattice by its canonical coordinatewise Euclidean
quotient and remainder.  For a positive modulus `m`, this gives an exact
equivalence

`ℤⁿ ≃ (ZMod m)ⁿ × ℤⁿ`.

Every residue-class slice of a positive-definite Gaussian is then one of the
centered Gaussians treated by
`RationalAdeleVectorCenteredGaussianAbel.lean`.  Consequently an arbitrary
complex weight periodic modulo `m` has its exact normalized Gaussian Abel
limit.  Summability is proved before any reindexing or `tsum` identity.

The Euclidean remainder is used only on the integer lattice.  No section of a
finite-adelic quotient, complex phase perturbation, finite Gauss reciprocity,
or Weil index is introduced.
-/

noncomputable section

open Filter Matrix Topology

namespace PositiveDefiniteIntegralLattice

private theorem finEquiv_apply_eq_natCast_val
    {m : ℕ} [NeZero m] (r : Fin m) :
    ZMod.finEquiv m r = (r.val : ZMod m) := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      change r = Fin.ofNat (m + 1) r.val
      apply Fin.ext
      simp

private theorem finEquiv_symm_val_eq
    {m : ℕ} [NeZero m] (r : ZMod m) :
    (((ZMod.finEquiv m).symm r).val : ℤ) = (r.val : ℤ) := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

/-- Coordinatewise Euclidean division gives the canonical residue and quotient
coordinates of an integer vector. -/
noncomputable def integerVectorDivModEquiv (n m : ℕ) [NeZero m] :
    (Fin n → ℤ) ≃ (Fin n → ZMod m) × (Fin n → ℤ) where
  toFun z :=
    (fun i => ZMod.finEquiv m ((Int.divModEquiv m (z i)).2),
      fun i => (Int.divModEquiv m (z i)).1)
  invFun p := fun i =>
    (Int.divModEquiv m).symm
      (p.2 i, (ZMod.finEquiv m).symm (p.1 i))
  left_inv z := by
    funext i
    change (Int.divModEquiv m).symm
      ((Int.divModEquiv m (z i)).1,
        (ZMod.finEquiv m).symm
          (ZMod.finEquiv m ((Int.divModEquiv m (z i)).2))) = z i
    rw [(ZMod.finEquiv m).symm_apply_apply]
    exact (Int.divModEquiv m).symm_apply_apply (z i)
  right_inv p := by
    apply Prod.ext <;> funext i
    · change ZMod.finEquiv m
        ((Int.divModEquiv m
          ((Int.divModEquiv m).symm
            (p.2 i, (ZMod.finEquiv m).symm (p.1 i)))).2) = p.1 i
      rw [(Int.divModEquiv m).apply_symm_apply]
      exact (ZMod.finEquiv m).apply_symm_apply (p.1 i)
    · change (Int.divModEquiv m
        ((Int.divModEquiv m).symm
          (p.2 i, (ZMod.finEquiv m).symm (p.1 i)))).1 = p.2 i
      rw [(Int.divModEquiv m).apply_symm_apply]

/-- The residue coordinate of the division equivalence is ordinary reduction
of each integer coordinate modulo `m`. -/
@[simp] theorem integerVectorDivModEquiv_apply_fst
    {n m : ℕ} [NeZero m] (z : Fin n → ℤ) :
    (integerVectorDivModEquiv n m z).1 =
      fun i => (z i : ZMod m) := by
  funext i
  change ZMod.finEquiv m ((Int.divModEquiv m (z i)).2) = _
  rw [finEquiv_apply_eq_natCast_val]
  have h := congrArg (fun x : ℤ => (x : ZMod m))
    ((Int.divModEquiv m).symm_apply_apply (z i))
  simpa [Int.divModEquiv_symm_apply] using h

/-- Recombining residue and quotient coordinates gives `m*q + r.val`. -/
@[simp] theorem integerVectorDivModEquiv_symm_apply
    {n m : ℕ} [NeZero m] (r : Fin n → ZMod m) (q : Fin n → ℤ) (i : Fin n) :
    (integerVectorDivModEquiv n m).symm (r, q) i =
      q i * m + (r i).val := by
  change (Int.divModEquiv m).symm
      (q i, (ZMod.finEquiv m).symm (r i)) = _
  rw [Int.divModEquiv_symm_apply]
  congr 1
  exact finEquiv_symm_val_eq (r i)

/-- A summable integer-vector family splits exactly into the finite sum of its
residue-class subseries. -/
theorem tsum_integerVector_eq_sum_residue_tsum_div
    {n m : ℕ} [NeZero m] (f : (Fin n → ℤ) → ℂ) (hf : Summable f) :
    ∑' z, f z =
      ∑ r : Fin n → ZMod m, ∑' q : Fin n → ℤ,
        f ((integerVectorDivModEquiv n m).symm (r, q)) := by
  let e := integerVectorDivModEquiv n m
  have hf' : Summable (f ∘ e.symm) := e.symm.summable_iff.mpr hf
  calc
    ∑' z, f z = ∑' p : (Fin n → ZMod m) × (Fin n → ℤ),
        f (e.symm p) := (e.symm.tsum_eq f).symm
    _ = ∑' r : Fin n → ZMod m, ∑' q : Fin n → ℤ,
        f (e.symm (r, q)) := hf'.tsum_prod
    _ = ∑ r : Fin n → ZMod m, ∑' q : Fin n → ℤ,
        f (e.symm (r, q)) := tsum_fintype _

/-- The real center `-r/m` of the Gaussian obtained from the residue class
`m*q+r`. -/
def integerResidueCenter {n m : ℕ} [NeZero m]
    (r : Fin n → ZMod m) : Fin n → ℝ :=
  fun i => -(r i).val / (m : ℝ)

/-- The Gaussian on `m*q+r` is exactly the scale-`a*m^2` Gaussian centered at
`-r/m` on the quotient coordinate. -/
theorem centeredMatrixGaussianSummand_divMod
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (r : Fin n → ZMod m) (q : Fin n → ℤ) :
    centeredMatrixGaussianSummand S a 0
        ((integerVectorDivModEquiv n m).symm (r, q)) =
      centeredMatrixGaussianSummand S (a * (m : ℝ) ^ 2)
        (integerResidueCenter r) q := by
  rw [centeredMatrixGaussianSummand, centeredMatrixGaussianSummand]
  congr 1
  let y : Fin n → ℝ := fun i => (q i : ℝ) - integerResidueCenter r i
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hcoord :
      (fun i =>
        (((integerVectorDivModEquiv n m).symm (r, q) i : ℤ) : ℝ) -
          (0 : Fin n → ℝ) i) =
        (m : ℝ) • y := by
    funext i
    rw [integerVectorDivModEquiv_symm_apply]
    simp only [Pi.zero_apply, sub_zero, Pi.smul_apply, smul_eq_mul]
    dsimp [y, integerResidueCenter]
    push_cast
    field_simp
    ring_nf
  rw [hcoord, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  dsimp only [y]
  push_cast
  ring

/-- A finite-valued periodic weight preserves absolute summability of every
positive-definite Gaussian at positive scale. -/
theorem summable_periodicWeight_mul_centeredMatrixGaussianSummand
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (weight : (Fin n → ZMod m) → ℂ) :
    Summable (fun z : Fin n → ℤ =>
      weight (fun i => (z i : ZMod m)) *
        centeredMatrixGaussianSummand S a 0 z) := by
  let C : ℝ := ∑ r : Fin n → ZMod m, ‖weight r‖
  have hC : ∀ r, ‖weight r‖ ≤ C := by
    intro r
    exact Finset.single_le_sum
      (fun i _hi => norm_nonneg (weight i)) (Finset.mem_univ r)
  have hgauss := (summable_centeredMatrixGaussianSummand S hS ha 0).norm
  apply Summable.of_norm_bounded (hgauss.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hC (fun i => (z i : ZMod m)))
    (norm_nonneg (centeredMatrixGaussianSummand S a 0 z))

/-- Exact residue-class decomposition of a periodically weighted Gaussian
series into finitely many centered Gaussian series. -/
theorem tsum_periodicWeight_mul_centeredMatrixGaussianSummand_eq
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (weight : (Fin n → ZMod m) → ℂ) :
    (∑' z : Fin n → ℤ,
        weight (fun i => (z i : ZMod m)) *
          centeredMatrixGaussianSummand S a 0 z) =
      ∑ r : Fin n → ZMod m, weight r *
        ∑' q : Fin n → ℤ,
          centeredMatrixGaussianSummand S (a * (m : ℝ) ^ 2)
            (integerResidueCenter r) q := by
  rw [tsum_integerVector_eq_sum_residue_tsum_div (m := m) _
    (summable_periodicWeight_mul_centeredMatrixGaussianSummand
      S hS ha weight)]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  have he := (integerVectorDivModEquiv n m).apply_symm_apply (r, q)
  have hres : (fun i =>
      (((integerVectorDivModEquiv n m).symm (r, q)) i : ZMod m)) = r := by
    simpa only [integerVectorDivModEquiv_apply_fst] using congrArg Prod.fst he
  rw [hres, centeredMatrixGaussianSummand_divMod]

/-- With the residue-class scale included in the square-root normalization,
the periodically weighted Gaussian tends to the unnormalized finite residue
sum. -/
theorem tendsto_periodicGaussian_scaledNormalization_nhdsGT_zero
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ) :
    Tendsto
      (fun a : ℝ =>
        (Real.sqrt ((a * (m : ℝ) ^ 2) ^ n * S.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            weight (fun i => (z i : ZMod m)) *
              centeredMatrixGaussianSummand S a 0 z)
      (𝓝[>] 0) (𝓝 (∑ r, weight r)) := by
  have hm : 0 < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hlim := tendsto_fintype_sum_centeredGaussianAbel_nhdsGT_zero
    S hS weight
      (fun r : Fin n → ZMod m => integerResidueCenter r)
      (sq_pos_of_pos hm)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [tsum_periodicWeight_mul_centeredMatrixGaussianSummand_eq
    S hS ha weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- The residue-class scale contributes the exact factor `m^n` to the real
square-root determinant normalization. -/
theorem sqrt_periodicGaussian_scaledNormalization
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    Real.sqrt ((a * (m : ℝ) ^ 2) ^ n * S.det) =
      (m : ℝ) ^ n * Real.sqrt (a ^ n * S.det) := by
  have hmnonneg : 0 ≤ (m : ℝ) ^ n := by positivity
  have harg : ((a * (m : ℝ) ^ 2) ^ n * S.det) =
      ((m : ℝ) ^ n) ^ 2 * (a ^ n * S.det) := by ring
  rw [harg, Real.sqrt_mul (sq_nonneg ((m : ℝ) ^ n)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hmnonneg]

/-- Periodic Gaussian Abel limit: the normalized integer-lattice sum tends to
the uniform residue average, with the literal factor `m^{-n}`. -/
theorem tendsto_periodicGaussianAbel_nhdsGT_zero
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ) :
    Tendsto
      (fun a : ℝ =>
        (Real.sqrt (a ^ n * S.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            weight (fun i => (z i : ZMod m)) *
              centeredMatrixGaussianSummand S a 0 z)
      (𝓝[>] 0)
      (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
  have hscaled :=
    (tendsto_periodicGaussian_scaledNormalization_nhdsGT_zero
      S hS weight).const_mul ((((m : ℝ) ^ n : ℂ)⁻¹))
  apply hscaled.congr'
  apply Filter.Eventually.of_forall
  intro a
  change ((((m : ℝ) ^ n : ℂ)⁻¹) *
      ((Real.sqrt ((a * (m : ℝ) ^ 2) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i => (z i : ZMod m)) *
            centeredMatrixGaussianSummand S a 0 z)) =
    (Real.sqrt (a ^ n * S.det) : ℂ) *
      ∑' z : Fin n → ℤ,
        weight (fun i => (z i : ZMod m)) *
          centeredMatrixGaussianSummand S a 0 z
  rw [sqrt_periodicGaussian_scaledNormalization S a]
  push_cast
  have hm : ((m : ℂ) ^ n) ≠ 0 := by
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr (NeZero.ne m))
  let X : ℂ := Real.sqrt (a ^ n * S.det)
  let Y : ℂ := ∑' z : Fin n → ℤ,
    weight (fun i => (z i : ZMod m)) *
      centeredMatrixGaussianSummand S a 0 z
  change ((m : ℂ) ^ n)⁻¹ * (((m : ℂ) ^ n * X) * Y) = X * Y
  calc
    ((m : ℂ) ^ n)⁻¹ * (((m : ℂ) ^ n * X) * Y) =
        (((m : ℂ) ^ n)⁻¹ * (m : ℂ) ^ n) * (X * Y) := by ring
    _ = X * Y := by rw [inv_mul_cancel₀ hm, one_mul]

end PositiveDefiniteIntegralLattice
