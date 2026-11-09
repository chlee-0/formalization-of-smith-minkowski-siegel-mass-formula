import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! The finite-field count of a diagonal quadratic form. Over a finite field `F`
of odd characteristic with `q = #F` and quadratic character `χ`, for nonzero
weights `w₁, …, w_n` the number `N_w(a)` of solutions of `∑ wᵢ xᵢ² = a` is

* `n = 2m + 1`: `N_w(a) = q^{2m} + q^m · χ((-1)^m · ∏ wᵢ · a)`;
* `n = 2m + 2`: `N_w(a) = q^{2m+1} + q^m · χ((-1)^{m+1} · ∏ wᵢ) · (q·[a = 0] − 1)`.

The proof adds one variable at a time: `#{x : c x² = t} = 1 + χ(c t)` and the
quadratic Jacobi sum `∑_t χ(t) χ(a − t) = χ(−1)·(q·[a = 0] − 1)`. -/
noncomputable section
open Finset

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of solutions of `∑ wᵢ xᵢ² = a` in `F^n`. -/
def diagonalQuadraticCount {n : ℕ} (w : Fin n → F) (a : F) : ℕ :=
  (univ.filter fun x : Fin n → F ↦ ∑ i, w i * x i ^ 2 = a).card

omit [Field F] in
/-- Regrouping a sum along the fibers of `g`. -/
theorem sum_comp_eq_sum_card_mul {α : Type*} [Fintype α] (g : α → F) (f : F → ℤ) :
    ∑ x, f (g x) = ∑ t, ((univ.filter fun x ↦ g x = t).card : ℤ) * f t := by
  rw [← Finset.sum_fiberwise univ g (fun x ↦ f (g x))]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [sum_congr rfl (fun x hx ↦ congrArg f (mem_filter.mp hx).2), sum_const, nsmul_eq_mul]

/-- `#{x : c x² = t} = 1 + χ(c t)` for `c ≠ 0`. -/
theorem card_mul_sq_eq (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) (t : F) :
    ((univ.filter fun x : F ↦ c * x ^ 2 = t).card : ℤ) = 1 + quadraticChar F (c * t) := by
  have hset : (univ.filter fun x : F ↦ c * x ^ 2 = t) = {x : F | x ^ 2 = t / c}.toFinset := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset, Set.mem_setOf_eq,
      eq_div_iff hc, mul_comm c]
  rw [hset, quadraticChar_card_sqrts hF, add_comm]
  congr 1
  rw [show t / c = c * t * c⁻¹ ^ 2 by field_simp, map_mul, map_pow,
    quadraticChar_sq_one (inv_ne_zero hc), mul_one]

theorem sum_quadraticChar_mul (hF : ringChar F ≠ 2) (c : F) :
    ∑ t, quadraticChar F (c * t) = 0 := by
  simp only [map_mul, ← mul_sum, quadraticChar_sum_zero hF, mul_zero]

/-- The quadratic Jacobi sum: `∑_t χ(t) χ(a − t) = χ(−1)·(q·[a = 0] − 1)`. -/
theorem sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) (a : F) :
    ∑ t, quadraticChar F t * quadraticChar F (a - t) =
      quadraticChar F (-1) * ((if a = 0 then (Fintype.card F : ℤ) else 0) - 1) := by
  have hq := quadraticChar_isQuadratic F
  by_cases ha : a = 0
  · subst ha
    have h : ∀ t : F, quadraticChar F t * quadraticChar F (0 - t) =
        quadraticChar F (-1) * (1 : MulChar F ℤ) t := by
      intro t
      rw [zero_sub, show -t = -1 * t by ring, map_mul, ← hq.sq_eq_one, pow_two,
        MulChar.coeToFun_mul, Pi.mul_apply]
      ring
    rw [sum_congr rfl fun t _ ↦ h t, ← mul_sum, MulChar.sum_one_eq_card_units,
      Fintype.card_units, if_pos rfl, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · have h : ∀ s : F, quadraticChar F (a * s) * quadraticChar F (a - a * s) =
        quadraticChar F s * quadraticChar F (1 - s) := by
      intro s
      rw [show a - a * s = a * (1 - s) by ring, map_mul, map_mul]
      have := quadraticChar_sq_one (F := F) ha
      linear_combination (quadraticChar F s * quadraticChar F (1 - s)) * this
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ a ha)]
    change ∑ s, quadraticChar F (a * s) * quadraticChar F (a - a * s) = _
    rw [sum_congr rfl fun s _ ↦ h s, if_neg ha]
    have hJ := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rw [hq.inv, jacobiSum] at hJ
    rw [hJ]
    ring

omit [Field F] [DecidableEq F] in
theorem card_fun_eq (n : ℕ) : Fintype.card (Fin n → F) = Fintype.card F ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin]

theorem sum_diagonalQuadraticCount {n : ℕ} (w : Fin n → F) :
    ∑ s, (diagonalQuadraticCount w s : ℤ) = (Fintype.card F : ℤ) ^ n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n → F)))
    (t := univ) (f := fun x ↦ ∑ i, w i * x i ^ 2) (fun _ _ ↦ mem_univ _)
  rw [card_univ, card_fun_eq] at h
  unfold diagonalQuadraticCount
  exact_mod_cast h.symm

/-- One-variable step: `N_w(a) = q^n + ∑_t χ(w₀ t) N_{tail w}(a − t)`. -/
theorem diagonalQuadraticCount_succ (hF : ringChar F ≠ 2) {n : ℕ} (w : Fin (n + 1) → F)
    (hw0 : w 0 ≠ 0) (a : F) :
    (diagonalQuadraticCount w a : ℤ) = (Fintype.card F : ℤ) ^ n +
      ∑ t, quadraticChar F (w 0 * t) * diagonalQuadraticCount (Fin.tail w) (a - t) := by
  have h1 : (diagonalQuadraticCount w a : ℤ) =
      ∑ x0 : F, (diagonalQuadraticCount (Fin.tail w) (a - w 0 * x0 ^ 2) : ℤ) := by
    simp only [diagonalQuadraticCount, natCast_card_filter]
    rw [← (Fin.consEquiv fun _ ↦ F).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun x0 _ ↦ sum_congr rfl fun y _ ↦ ?_
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail,
      eq_sub_iff_add_eq']
  rw [h1, sum_comp_eq_sum_card_mul (fun x0 ↦ w 0 * x0 ^ 2)
    (fun t ↦ (diagonalQuadraticCount (Fin.tail w) (a - t) : ℤ))]
  simp only [card_mul_sq_eq hF hw0, add_mul, one_mul, sum_add_distrib]
  congr 1
  rw [← sum_diagonalQuadraticCount (Fin.tail w)]
  exact (Equiv.subLeft a).sum_comp (fun s ↦ (diagonalQuadraticCount (Fin.tail w) s : ℤ))

theorem diagonalQuadraticCount_zero (w : Fin 0 → F) (a : F) :
    (diagonalQuadraticCount w a : ℤ) = if a = 0 then 1 else 0 := by
  unfold diagonalQuadraticCount
  rw [natCast_card_filter, Fintype.sum_unique]
  simp only [univ_eq_empty, sum_empty, eq_comm (a := (0 : F))]

theorem sum_quadraticChar_mul_ite (c a : F) (r : ℤ) :
    ∑ t, quadraticChar F (c * t) * (if a - t = 0 then r else 0) = r * quadraticChar F (c * a) := by
  simp only [sub_eq_zero, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  ring

theorem diagonalQuadraticCount_one (hF : ringChar F ≠ 2) {n : ℕ} (hn : n = 1)
    (w : Fin n → F) (hw : ∀ i, w i ≠ 0) (a : F) :
    (diagonalQuadraticCount w a : ℤ) = 1 + quadraticChar F ((∏ i, w i) * a) := by
  subst hn
  rw [diagonalQuadraticCount_succ hF w (hw 0) a]
  simp only [diagonalQuadraticCount_zero, pow_zero, Fin.prod_univ_one]
  rw [sum_quadraticChar_mul_ite, one_mul]

/-- The odd-dimensional closed form. -/
def OddCountFormula (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m : ℕ) : Prop :=
  ∀ n, n = 2 * m + 1 → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ a : F,
    (diagonalQuadraticCount w a : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
      (Fintype.card F : ℤ) ^ m * quadraticChar F ((-1) ^ m * (∏ i, w i) * a)

/-- The even-dimensional closed form. -/
def EvenCountFormula (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m : ℕ) : Prop :=
  ∀ n, n = 2 * m + 2 → ∀ w : Fin n → F, (∀ i, w i ≠ 0) → ∀ a : F,
    (diagonalQuadraticCount w a : ℤ) = (Fintype.card F : ℤ) ^ (2 * m + 1) +
      (Fintype.card F : ℤ) ^ m * quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) *
        ((if a = 0 then (Fintype.card F : ℤ) else 0) - 1)

theorem oddCountFormula_zero (hF : ringChar F ≠ 2) : OddCountFormula F 0 := by
  intro n hn w hw a
  rw [diagonalQuadraticCount_one hF hn w hw a]
  simp

theorem evenCountFormula_of_odd (hF : ringChar F ≠ 2) {m : ℕ} (h : OddCountFormula F m) :
    EvenCountFormula F m := by
  intro n hn w hw a
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [diagonalQuadraticCount_succ hF w (hw 0) a]
  have hsum : ∑ t, quadraticChar F (w 0 * t) * (diagonalQuadraticCount (Fin.tail w) (a - t) : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * m) * ∑ t, quadraticChar F (w 0 * t) +
        (Fintype.card F : ℤ) ^ m * quadraticChar F (w 0) *
          quadraticChar F ((-1) ^ m * ∏ i, Fin.tail w i) *
          ∑ t, quadraticChar F t * quadraticChar F (a - t) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [h n (by omega) (Fin.tail w) (fun i ↦ hw _) (a - t)]
    simp only [map_mul]
    ring
  rw [hsum, sum_quadraticChar_mul hF, sum_quadraticChar_mul_sub hF, Fin.prod_univ_succ w,
    show (Fintype.card F : ℤ) ^ n = (Fintype.card F : ℤ) ^ (2 * m + 1) by
      rw [show n = 2 * m + 1 by omega]]
  simp only [map_mul, map_pow, Fin.tail]
  ring

theorem oddCountFormula_succ_of_even (hF : ringChar F ≠ 2) {m : ℕ} (h : EvenCountFormula F m) :
    OddCountFormula F (m + 1) := by
  intro n hn w hw a
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [diagonalQuadraticCount_succ hF w (hw 0) a]
  have hsum : ∑ t, quadraticChar F (w 0 * t) * (diagonalQuadraticCount (Fin.tail w) (a - t) : ℤ) =
      ((Fintype.card F : ℤ) ^ (2 * m + 1) - (Fintype.card F : ℤ) ^ m *
          quadraticChar F ((-1) ^ (m + 1) * ∏ i, Fin.tail w i)) * ∑ t, quadraticChar F (w 0 * t) +
        (Fintype.card F : ℤ) ^ m * quadraticChar F ((-1) ^ (m + 1) * ∏ i, Fin.tail w i) *
          ∑ t, quadraticChar F (w 0 * t) * (if a - t = 0 then (Fintype.card F : ℤ) else 0) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [h n (by omega) (Fin.tail w) (fun i ↦ hw _) (a - t)]
    split_ifs <;> ring
  rw [hsum, sum_quadraticChar_mul hF, sum_quadraticChar_mul_ite, Fin.prod_univ_succ w,
    show (Fintype.card F : ℤ) ^ n = (Fintype.card F : ℤ) ^ (2 * (m + 1)) by
      rw [show n = 2 * (m + 1) by omega]]
  simp only [map_mul, map_pow, Fin.tail]
  ring

theorem oddCountFormula (hF : ringChar F ≠ 2) (m : ℕ) : OddCountFormula F m := by
  induction m with
  | zero => exact oddCountFormula_zero hF
  | succ m ih => exact oddCountFormula_succ_of_even hF (evenCountFormula_of_odd hF ih)

/-- Odd dimension `n = 2m + 1`: `N_w(a) = q^{2m} + q^m χ((-1)^m ∏ wᵢ · a)`. -/
theorem diagonalQuadraticCount_odd (hF : ringChar F ≠ 2) (m : ℕ) (w : Fin (2 * m + 1) → F)
    (hw : ∀ i, w i ≠ 0) (a : F) :
    (diagonalQuadraticCount w a : ℤ) = (Fintype.card F : ℤ) ^ (2 * m) +
      (Fintype.card F : ℤ) ^ m * quadraticChar F ((-1) ^ m * (∏ i, w i) * a) :=
  oddCountFormula hF m _ rfl w hw a

/-- Even dimension `n = 2m + 2`:
`N_w(a) = q^{2m+1} + q^m χ((-1)^{m+1} ∏ wᵢ) (q·[a = 0] − 1)`. -/
theorem diagonalQuadraticCount_even (hF : ringChar F ≠ 2) (m : ℕ) (w : Fin (2 * m + 2) → F)
    (hw : ∀ i, w i ≠ 0) (a : F) :
    (diagonalQuadraticCount w a : ℤ) = (Fintype.card F : ℤ) ^ (2 * m + 1) +
      (Fintype.card F : ℤ) ^ m * quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) *
        ((if a = 0 then (Fintype.card F : ℤ) else 0) - 1) :=
  evenCountFormula_of_odd hF (oddCountFormula hF m) _ rfl w hw a

end FiniteField
