import SMSFormula.BlockCayleyCoordinates
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Integrality of the block conjugation matrices

For a subring `S` of a field containing `f₀, f₁, f₂`, their inverses and `1/2`:

* `M(h, k) = θ⁻¹ R_{k̄} L_h θ` has entries in `S` when `h, k` do;
* conversely, if `M(h, k)` has entries in `S` then every product `hₘ kⱼ` lies in `S`, by the
  quaternion identity `Σᵢ wᵢ⁻¹ (h eᵢ k̄) eⱼ ēᵢ = 4 wⱼ kⱼ h` (`wᵢ = N(eᵢ)`);
* over `ℚ_p` with `S = ℤ_p`, two norm-one quaternions whose products `hₘ kⱼ` are integral are
  integral (ultrametric inequality).

Hence `M(h, k)` is integral iff `h` and `k` are, for norm-one `h, k`.  Pure algebra; nothing is chosen.
-/

noncomputable section

open Matrix

namespace BlockConjugationCoordinates

variable {K : Type*} [Field K] (S : Subring K) {f0 f1 f2 : K}

/-! ## Closure -/

theorem qmul_mem (hf0 : f0 ∈ S) (hf1 : f1 ∈ S) (hf2 : f2 ∈ S) {h k : Fin 4 → K} (hh : ∀ i, h i ∈ S)
    (hk : ∀ i, k i ∈ S) (i : Fin 4) : qmul f0 f1 f2 h k i ∈ S := by
  fin_cases i <;>
    simp only [qmul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    apply_rules [Subring.sub_mem, Subring.add_mem, Subring.mul_mem, Subring.neg_mem]

theorem qconj_mem {h : Fin 4 → K} (hh : ∀ i, h i ∈ S) (i : Fin 4) : qconj h i ∈ S := by
  fin_cases i <;>
    simp only [qconj, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    apply_rules [Subring.neg_mem]

theorem theta_mem (hf0 : f0 ∈ S) (hf1 : f1 ∈ S) (hf2 : f2 ∈ S) {c : Fin 4 → K} (hc : ∀ i, c i ∈ S) (i : Fin 4) :
    theta f0 f1 f2 c i ∈ S := by
  fin_cases i <;>
    simp only [theta, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    apply_rules [Subring.mul_mem, Subring.neg_mem]

theorem thetaInv_mem {u0 u1 u2 d : K} (hu0 : u0 ∈ S) (hu1 : u1 ∈ S) (hu2 : u2 ∈ S) (hd : d ∈ S)
    {y : Fin 4 → K} (hy : ∀ i, y i ∈ S) (i : Fin 4) : thetaInv u0 u1 u2 d y i ∈ S := by
  fin_cases i <;>
    simp only [thetaInv, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    apply_rules [Subring.mul_mem, Subring.neg_mem]

theorem single_mem (j i : Fin 4) : (Pi.single j (1 : K) : Fin 4 → K) i ∈ S := by
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem mulVec_mem {M : Matrix (Fin 4) (Fin 4) K} (hM : ∀ i j, M i j ∈ S) {v : Fin 4 → K} (hv : ∀ i, v i ∈ S)
    (i : Fin 4) : (M *ᵥ v) i ∈ S := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hM i j) (hv j)

/-- `M(h, k)` is integral when `h` and `k` are. -/
theorem conjMatrix_mem (hf0 : f0 ∈ S) (hf1 : f1 ∈ S) (hf2 : f2 ∈ S) {u0 u1 u2 d : K} (hu0 : u0 ∈ S)
    (hu1 : u1 ∈ S) (hu2 : u2 ∈ S) (hd : d ∈ S) {h k : Fin 4 → K} (hh : ∀ i, h i ∈ S) (hk : ∀ i, k i ∈ S)
    (i j : Fin 4) : conjMatrix f0 f1 f2 u0 u1 u2 d h k i j ∈ S := by
  rw [conjMatrix_apply, conjCoords]
  exact thetaInv_mem S hu0 hu1 hu2 hd (qmul_mem S hf0 hf1 hf2 (qmul_mem S hf0 hf1 hf2 hh
    (theta_mem S hf0 hf1 hf2 (single_mem S j))) (qconj_mem S hk)) i

/-! ## Recovering the products `hₘ kⱼ` -/

/-- The quaternion norms `wᵢ = N(eᵢ)` of the basis. -/
def basisNorm (f0 f1 f2 : K) : Fin 4 → K := ![1, f0 * f1, f0 * f2, f1 * f2]

omit [Field K] in
theorem qmul_e0 {R : Type*} [CommRing R] (g0 g1 g2 : R) (h : Fin 4 → R) :
    qmul g0 g1 g2 h (Pi.single 0 1) = h := by
  funext i
  fin_cases i <;> simp [qmul]

omit [Field K] in
theorem qmul_e1 {R : Type*} [CommRing R] (g0 g1 g2 : R) (h : Fin 4 → R) :
    qmul g0 g1 g2 h (Pi.single 1 1) = ![-(g0 * g1 * h 1), h 0, -(g1 * h 3), g0 * h 2] := by
  funext i
  fin_cases i <;> simp [qmul]

omit [Field K] in
theorem qmul_e2 {R : Type*} [CommRing R] (g0 g1 g2 : R) (h : Fin 4 → R) :
    qmul g0 g1 g2 h (Pi.single 2 1) = ![-(g0 * g2 * h 2), g2 * h 3, h 0, -(g0 * h 1)] := by
  funext i
  fin_cases i <;> simp [qmul]

omit [Field K] in
theorem qmul_e3 {R : Type*} [CommRing R] (g0 g1 g2 : R) (h : Fin 4 → R) :
    qmul g0 g1 g2 h (Pi.single 3 1) = ![-(g1 * g2 * h 3), -(g2 * h 2), g1 * h 1, h 0] := by
  funext i
  fin_cases i <;> simp [qmul]

omit [Field K] in
theorem qconj_single_zero {R : Type*} [CommRing R] : qconj (Pi.single (0 : Fin 4) (1 : R)) = Pi.single 0 1 := by
  funext i
  fin_cases i <;> simp [qconj]

omit [Field K] in
theorem qconj_single_of_ne {R : Type*} [CommRing R] {i : Fin 4} (hi : i ≠ 0) :
    qconj (Pi.single i (1 : R)) = -Pi.single i 1 := by
  funext a
  fin_cases i <;> fin_cases a <;> simp_all [qconj]

omit [Field K] in
theorem qmul_neg_right' {R : Type*} [CommRing R] (g0 g1 g2 : R) (h k : Fin 4 → R) :
    qmul g0 g1 g2 h (-k) = -qmul g0 g1 g2 h k := by
  funext i
  fin_cases i <;> simp [qmul] <;> ring

/-- The denominator-free recovery coefficients `(w₁w₂w₃)/wᵢ`. -/
def recoveryCoeff (f0 f1 f2 : K) : Fin 4 → K :=
  ![f0 ^ 2 * f1 ^ 2 * f2 ^ 2, f0 * f1 * f2 ^ 2, f0 * f1 ^ 2 * f2, f0 ^ 2 * f1 * f2]

/-- The recovery identity `Σᵢ (W/wᵢ) (h eᵢ k̄) eⱼ ēᵢ = 4 W wⱼ kⱼ h`, `W = w₁w₂w₃`. -/
theorem sum_recovery (h k : Fin 4 → K) (j : Fin 4) :
    ∑ i, recoveryCoeff f0 f1 f2 i • qmul f0 f1 f2 (qmul f0 f1 f2 (qmul f0 f1 f2 (qmul f0 f1 f2 h
        (Pi.single i 1)) (qconj k)) (Pi.single j 1)) (qconj (Pi.single i 1)) =
      (4 * (f0 ^ 2 * f1 ^ 2 * f2 ^ 2) * basisNorm f0 f1 f2 j * k j) • h := by
  rw [Fin.sum_univ_four, qconj_single_zero, qconj_single_of_ne (by decide), qconj_single_of_ne (by decide),
    qconj_single_of_ne (by decide)]
  simp only [qmul_neg_right', qmul_e0, qmul_e1, qmul_e2, qmul_e3]
  funext m
  fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, qmul_e0, qmul_e1, qmul_e2, qmul_e3] <;>
    fin_cases m <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      recoveryCoeff, basisNorm, qmul, qconj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    ring

/-- An integral `M(h, k)` has integral products `hₘ kⱼ`. -/
theorem mul_mem_of_conjMatrix_mem (hf0 : f0 ∈ S) (hf1 : f1 ∈ S) (hf2 : f2 ∈ S) (hf0' : f0⁻¹ ∈ S)
    (hf1' : f1⁻¹ ∈ S) (hf2' : f2⁻¹ ∈ S) (h2 : (2 : K)⁻¹ ∈ S) (h2ne : (2 : K) ≠ 0) (hn0 : f0 ≠ 0) (hn1 : f1 ≠ 0)
    (hn2 : f2 ≠ 0) {h k : Fin 4 → K}
    (hM : ∀ i j, conjMatrix f0 f1 f2 f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ h k i j ∈ S) (m j : Fin 4) :
    h m * k j ∈ S := by
  have hd : (f0 * f1 * f2)⁻¹ ∈ S := by
    rw [mul_inv, mul_inv]
    exact Subring.mul_mem _ (Subring.mul_mem _ hf0' hf1') hf2'
  -- the columns `h eᵢ k̄` are integral
  have hv : ∀ i a, qmul f0 f1 f2 (qmul f0 f1 f2 h (Pi.single i 1)) (qconj k) a ∈ S := by
    intro i a
    have hcol : qmul f0 f1 f2 (qmul f0 f1 f2 h (Pi.single i 1)) (qconj k) =
        theta f0 f1 f2 (conjMatrix f0 f1 f2 f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ h k *ᵥ
          thetaInv f0⁻¹ f1⁻¹ f2⁻¹ (f0 * f1 * f2)⁻¹ (Pi.single i 1)) := by
      rw [← conjCoords_eq_mulVec, conjCoords, theta_thetaInv' f0 f1 f2 hn0 hn1 hn2,
        theta_thetaInv' f0 f1 f2 hn0 hn1 hn2]
    rw [hcol]
    exact theta_mem S hf0 hf1 hf2 (mulVec_mem S hM (thetaInv_mem S hf0' hf1' hf2' hd (single_mem S i))) a
  have hc : ∀ i, recoveryCoeff f0 f1 f2 i ∈ S := by
    intro i
    fin_cases i <;> simp only [recoveryCoeff, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
      apply_rules [Subring.mul_mem, Subring.pow_mem]
  have hsum := congrFun (sum_recovery (f0 := f0) (f1 := f1) (f2 := f2) h k j) m
  have hmem : ((4 * (f0 ^ 2 * f1 ^ 2 * f2 ^ 2) * basisNorm f0 f1 f2 j * k j) • h) m ∈ S := by
    rw [← hsum, Finset.sum_apply]
    refine Subring.sum_mem _ fun i _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ (hc i) (qmul_mem S hf0 hf1 hf2 (qmul_mem S hf0 hf1 hf2 (hv i) (single_mem S j))
      (qconj_mem S (single_mem S i)) m)
  have hwj : basisNorm f0 f1 f2 j ≠ 0 := by
    fin_cases j <;> simp [basisNorm, hn0, hn1, hn2]
  have hw' : (basisNorm f0 f1 f2 j)⁻¹ ∈ S := by
    fin_cases j <;> simp only [basisNorm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      inv_one, mul_inv]
    · exact Subring.one_mem _
    all_goals exact Subring.mul_mem _ ‹_› ‹_›
  have h4ne : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2ne h2ne
  have hinv : (4 * (f0 ^ 2 * f1 ^ 2 * f2 ^ 2) * basisNorm f0 f1 f2 j)⁻¹ ∈ S := by
    rw [mul_inv, mul_inv, show (4 : K)⁻¹ = 2⁻¹ * 2⁻¹ by rw [← mul_inv]; norm_num, mul_inv, mul_inv,
      ← inv_pow, ← inv_pow, ← inv_pow]
    apply_rules [Subring.mul_mem, Subring.pow_mem]
  have heq : h m * k j = (4 * (f0 ^ 2 * f1 ^ 2 * f2 ^ 2) * basisNorm f0 f1 f2 j)⁻¹ *
      ((4 * (f0 ^ 2 * f1 ^ 2 * f2 ^ 2) * basisNorm f0 f1 f2 j * k j) • h) m := by
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [heq]
  exact Subring.mul_mem _ hinv hmem

end BlockConjugationCoordinates

/-! ## Norm-one quaternions over `ℚ_p` -/

namespace BlockConjugationCoordinates

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Two norm-one quaternions over `ℚ_p` with integral products `hₘ kⱼ` are integral. -/
theorem mem_of_mul_mem {f0 f1 f2 : ℚ_[p]} (hf0 : f0 ∈ PadicInt.subring p) (hf1 : f1 ∈ PadicInt.subring p)
    (hf2 : f2 ∈ PadicInt.subring p) {h k : Fin 4 → ℚ_[p]} (hk : qnorm f0 f1 f2 k = 1)
    (hhk : ∀ m j, h m * k j ∈ PadicInt.subring p) (m : Fin 4) : h m ∈ PadicInt.subring p := by
  rw [PadicInt.mem_subring_iff] at hf0 hf1 hf2 ⊢
  by_contra hm
  push_neg at hm
  have hpos : 0 < ‖h m‖ := lt_trans zero_lt_one hm
  have hsmall : ∀ j, ‖k j‖ < 1 := by
    intro j
    have := (PadicInt.mem_subring_iff p).1 (hhk m j)
    rw [norm_mul] at this
    by_contra hj
    push_neg at hj
    have : 1 < ‖h m‖ * ‖k j‖ := by nlinarith
    linarith
  have hsq : ∀ (c : ℚ_[p]), ‖c‖ ≤ 1 → ∀ j, ‖c * k j ^ 2‖ < 1 := by
    intro c hc j
    rw [norm_mul, norm_pow]
    have hk0 := norm_nonneg (k j)
    calc ‖c‖ * ‖k j‖ ^ 2 ≤ 1 * ‖k j‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ < 1 := by nlinarith [hsmall j]
  have h0 : ‖k 0 ^ 2‖ < 1 := by simpa using hsq 1 (by simp) 0
  have h1 := hsq (f0 * f1) (by rw [norm_mul]; nlinarith [norm_nonneg f0, norm_nonneg f1]) 1
  have h2 := hsq (f0 * f2) (by rw [norm_mul]; nlinarith [norm_nonneg f0, norm_nonneg f2]) 2
  have h3 := hsq (f1 * f2) (by rw [norm_mul]; nlinarith [norm_nonneg f1, norm_nonneg f2]) 3
  have hlt : ‖qnorm f0 f1 f2 k‖ < 1 := by
    unfold qnorm
    refine lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt ?_ h3)
    refine lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt ?_ h2)
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt h0 h1)
  rw [hk, norm_one] at hlt
  exact lt_irrefl _ hlt

end BlockConjugationCoordinates
