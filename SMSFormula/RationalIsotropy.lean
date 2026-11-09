import SMSFormula.QuadraticReflection
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Rational local-global isotropy

This module begins the direct Hasse--Minkowski development with the binary
case.  It proves from rational factorization that an element of `ℚ` is a
square exactly when it is a square over `ℝ` and every `ℚ_[p]`, then translates
that criterion into isotropy of a nonsingular binary diagonal Gram matrix.
It also identifies diagonal ternary isotropy with representation by a
quadratic-algebra norm, isolating the arithmetic input needed for the ternary
local-global step.
-/

noncomputable section

open scoped Matrix

namespace Rat

private lemma nat_isSquare_of_factorization_even {n : ℕ}
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [← Nat.prod_factorization_pow_eq_self hn]
  apply Finset.isSquare_prod
  intro p hp
  obtain ⟨k, hk⟩ := h p
  rw [hk]
  exact ⟨p ^ k, by simp [pow_add]⟩

/-- A nonzero rational square in `ℚ_[p]` has even `p`-adic valuation. -/
lemma padicValRat_even_of_isSquare
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hs : IsSquare (q : ℚ_[p])) : Even (padicValRat p q) := by
  obtain ⟨x, hx⟩ := hs
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hq
    simpa [hx0] using congrArg (fun z : ℚ_[p] => z) hx
  have hv := congrArg Padic.valuation hx
  rw [Padic.valuation_ratCast, Padic.valuation_mul hx0 hx0] at hv
  exact ⟨x.valuation, by omega⟩

private lemma num_den_factorization_even_of_padic_square
    {q : ℚ} (hq : q ≠ 0)
    (hs : ∀ (p : ℕ) [Fact p.Prime], IsSquare (q : ℚ_[p])) :
    (∀ p, Even (q.num.natAbs.factorization p)) ∧
      ∀ p, Even (q.den.factorization p) := by
  constructor
  · intro p
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      by_cases hpd : p ∣ q.num.natAbs
      · have hcop : p.Coprime q.den := q.reduced.of_dvd_left hpd
        have hnd : ¬p ∣ q.den := hp.coprime_iff_not_dvd.mp hcop
        have hval : padicValRat p q = q.num.natAbs.factorization p := by
          rw [padicValRat_def, padicValInt, Nat.factorization_def _ hp,
            padicValNat.eq_zero_of_not_dvd hnd]
          omega
        have heven := padicValRat_even_of_isSquare hq (hs p)
        rw [hval] at heven
        exact_mod_cast heven
      · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
        exact Even.zero
    · simp [Nat.factorization, hp]
  · intro p
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      by_cases hpd : p ∣ q.den
      · have hcop : q.num.natAbs.Coprime p := q.reduced.of_dvd_right hpd
        have hnnum : ¬p ∣ q.num.natAbs :=
          hp.coprime_iff_not_dvd.mp hcop.symm
        have hval : padicValRat p q = -(q.den.factorization p : ℤ) := by
          rw [padicValRat_def, padicValInt,
            padicValNat.eq_zero_of_not_dvd hnnum, Nat.factorization_def _ hp]
          omega
        have heven := padicValRat_even_of_isSquare hq (hs p)
        rw [hval, even_neg] at heven
        exact_mod_cast heven
      · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
        exact Even.zero
    · simp [Nat.factorization, hp]

/-- A rational number is a square if and only if it is a square over the real
completion and every `p`-adic completion. -/
theorem isSquare_iff_isSquare_real_and_padic (q : ℚ) :
    IsSquare q ↔
      IsSquare (q : ℝ) ∧
        ∀ (p : ℕ) [Fact p.Prime], IsSquare (q : ℚ_[p]) := by
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · refine ⟨(x : ℝ), ?_⟩
      norm_cast
    · intro p
      refine ⟨(x : ℚ_[p]), ?_⟩
      norm_cast
  · rintro ⟨hreal, hpadic⟩
    by_cases hq : q = 0
    · simp [hq]
    have hq_nonneg : 0 ≤ q := by
      obtain ⟨x, hx⟩ := hreal
      have hreal_nonneg : (0 : ℝ) ≤ (q : ℝ) := by
        rw [hx]
        exact mul_self_nonneg x
      exact_mod_cast hreal_nonneg
    obtain ⟨hnum_even, hden_even⟩ :=
      num_den_factorization_even_of_padic_square hq hpadic
    have hnum_nat : IsSquare q.num.natAbs :=
      nat_isSquare_of_factorization_even hnum_even
    have hden : IsSquare q.den :=
      nat_isSquare_of_factorization_even hden_even
    rw [Rat.isSquare_iff]
    refine ⟨?_, hden⟩
    obtain ⟨a, ha⟩ := hnum_nat
    refine ⟨(a : ℤ), ?_⟩
    have hnum_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
    rw [← Int.natAbs_of_nonneg hnum_nonneg]
    exact_mod_cast ha

end Rat

namespace PositiveDefiniteIntegralLattice

/-- A Gram matrix is isotropic when its quadratic value vanishes on a
nonzero vector. -/
def GramIsotropic {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ x : Fin n → K, x ≠ 0 ∧ gramQuadraticValue A x = 0

/-- A nonsingular binary diagonal Gram matrix is isotropic exactly when its
coefficient ratio is a square. -/
theorem binaryDiagonal_gramIsotropic_iff_isSquare_neg_div
    {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    GramIsotropic (Matrix.diagonal ![a, b]) ↔ IsSquare (-b / a) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hxcoord : x 0 ≠ 0 := by
      intro hxzero
      have hyzero : x 1 = 0 := by
        have h := hx
        simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, hxzero, hb] at h
        exact h
      apply hx0
      funext i
      fin_cases i <;> assumption
    have hycoord : x 1 ≠ 0 := by
      intro hyzero
      have hxzero : x 0 = 0 := by
        have h := hx
        simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, hyzero, ha] at h
        exact h
      apply hx0
      funext i
      fin_cases i <;> assumption
    refine ⟨x 0 / x 1, ?_⟩
    have h := hx
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h
    field_simp [ha, hycoord]
    linear_combination -h
  · rintro ⟨z, hz⟩
    refine ⟨![z, 1], ?_, ?_⟩
    · intro hzero
      have := congrFun hzero 1
      simp at this
    · simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      field_simp [ha] at hz
      linear_combination -hz

/-- Binary Hasse--Minkowski: a nonsingular rational diagonal binary Gram
matrix is isotropic exactly when it is isotropic over `ℝ` and every
`ℚ_[p]`. -/
theorem binaryDiagonal_gramIsotropic_iff_real_and_padic
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    GramIsotropic (Matrix.diagonal ![a, b]) ↔
      GramIsotropic ((Matrix.diagonal ![a, b]).map (algebraMap ℚ ℝ)) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          GramIsotropic
            ((Matrix.diagonal ![a, b]).map (algebraMap ℚ ℚ_[p])) := by
  rw [binaryDiagonal_gramIsotropic_iff_isSquare_neg_div a b ha hb]
  rw [Rat.isSquare_iff_isSquare_real_and_padic]
  constructor
  · rintro ⟨hreal, hpadic⟩
    constructor
    · rw [show (Matrix.diagonal ![a, b]).map (algebraMap ℚ ℝ) =
          Matrix.diagonal ![(a : ℝ), (b : ℝ)] by
          ext i j
          fin_cases i <;> fin_cases j <;> simp]
      rw [binaryDiagonal_gramIsotropic_iff_isSquare_neg_div]
      · simpa using hreal
      · exact_mod_cast ha
      · exact_mod_cast hb
    · intro p hpprime
      rw [show (Matrix.diagonal ![a, b]).map (algebraMap ℚ ℚ_[p]) =
          Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p])] by
          ext i j
          fin_cases i <;> fin_cases j <;> simp]
      rw [binaryDiagonal_gramIsotropic_iff_isSquare_neg_div]
      · simpa using hpadic p
      · exact_mod_cast ha
      · exact_mod_cast hb
  · rintro ⟨hreal, hpadic⟩
    constructor
    · rw [show (Matrix.diagonal ![a, b]).map (algebraMap ℚ ℝ) =
          Matrix.diagonal ![(a : ℝ), (b : ℝ)] by
          ext i j
          fin_cases i <;> fin_cases j <;> simp] at hreal
      rw [binaryDiagonal_gramIsotropic_iff_isSquare_neg_div] at hreal
      · simpa using hreal
      · exact_mod_cast ha
      · exact_mod_cast hb
    · intro p hpprime
      have hp := hpadic p
      rw [show (Matrix.diagonal ![a, b]).map (algebraMap ℚ ℚ_[p]) =
          Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p])] by
          ext i j
          fin_cases i <;> fin_cases j <;> simp] at hp
      rw [binaryDiagonal_gramIsotropic_iff_isSquare_neg_div] at hp
      · simpa using hp
      · exact_mod_cast ha
      · exact_mod_cast hb

/-- The proposition that `c` is represented by the norm from the quadratic
algebra in which the adjoined generator has square `d`. -/
def quadraticNormRepresents
    {K : Type*} [Field K] (d c : K) : Prop :=
  ∃ z : QuadraticAlgebra K d 0, QuadraticAlgebra.norm z = c

/-- In coordinates, the norm from `K(√d)` is `x² - d y²`. -/
lemma quadraticNormRepresents_iff_exists
    {K : Type*} [Field K] (d c : K) :
    quadraticNormRepresents d c ↔
      ∃ x y : K, x * x - d * y * y = c := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.re, z.im, by
      simpa [QuadraticAlgebra.norm_def] using hz⟩
  · rintro ⟨x, y, hxy⟩
    exact ⟨⟨x, y⟩, by
      simpa [QuadraticAlgebra.norm_def] using hxy⟩

/-- Scalar extension preserves representation by a quadratic norm. -/
lemma quadraticNormRepresents_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    {d c : K} (h : quadraticNormRepresents d c) :
    quadraticNormRepresents (f d) (f c) := by
  rw [quadraticNormRepresents_iff_exists] at h ⊢
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨f x, f y, ?_⟩
  simpa using congrArg f hxy

/-- Multiplication by the quadratic generator, whose norm is `-d`, carries
the norm fiber over `c` to the norm fiber over `-d * c`. -/
lemma quadraticNormRepresents_iff_mul_neg_parameter
    {K : Type*} [Field K] {d c : K} (hd : d ≠ 0) :
    quadraticNormRepresents d c ↔
      quadraticNormRepresents d (-d * c) := by
  rw [quadraticNormRepresents_iff_exists,
    quadraticNormRepresents_iff_exists]
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨d * y, x, ?_⟩
    calc
      (d * y) * (d * y) - d * x * x =
          -d * (x * x - d * y * y) := by ring
      _ = -d * c := by rw [hxy]
  · rintro ⟨x, y, hxy⟩
    refine ⟨y, x / d, ?_⟩
    calc
      y * y - d * (x / d) * (x / d) =
          -(x * x - d * y * y) / d := by
            field_simp [hd]
            ring
      _ = -(-d * c) / d := by rw [hxy]
      _ = c := by field_simp [hd]

/-- Multiplying the quadratic parameter by a nonzero square does not change
its represented norm values. -/
lemma quadraticNormRepresents_iff_mul_sq_parameter
    {K : Type*} [Field K] {d c s : K} (hs : s ≠ 0) :
    quadraticNormRepresents d c ↔
      quadraticNormRepresents (d * s ^ 2) c := by
  rw [quadraticNormRepresents_iff_exists,
    quadraticNormRepresents_iff_exists]
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y / s, ?_⟩
    calc
      x * x - (d * s ^ 2) * (y / s) * (y / s) =
          x * x - d * y * y := by field_simp [hs]
      _ = c := hxy
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, s * y, ?_⟩
    calc
      x * x - d * (s * y) * (s * y) =
          x * x - (d * s ^ 2) * y * y := by ring
      _ = c := hxy

/-- Multiplying a target by a nonzero square preserves representation by a
fixed quadratic norm. -/
lemma quadraticNormRepresents_iff_mul_sq_target
    {K : Type*} [Field K] {d c s : K} (hs : s ≠ 0) :
    quadraticNormRepresents d c ↔
      quadraticNormRepresents d (c * s ^ 2) := by
  rw [quadraticNormRepresents_iff_exists,
    quadraticNormRepresents_iff_exists]
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨s * x, s * y, ?_⟩
    calc
      s * x * (s * x) - d * (s * y) * (s * y) =
          (x * x - d * y * y) * s ^ 2 := by ring
      _ = c * s ^ 2 := by rw [hxy]
  · rintro ⟨x, y, hxy⟩
    refine ⟨x / s, y / s, ?_⟩
    calc
      x / s * (x / s) - d * (y / s) * (y / s) =
          (x * x - d * y * y) / s ^ 2 := by field_simp [hs]
      _ = c * s ^ 2 / s ^ 2 := by rw [hxy]
      _ = c := by field_simp [hs]

/-- Multiplication by a nonzero square does not change squarehood in a field. -/
lemma isSquare_mul_sq_iff_of_ne
    {K : Type*} [Field K] {a s : K} (hs : s ≠ 0) :
    IsSquare (a * s ^ 2) ↔ IsSquare a := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z / s, ?_⟩
    field_simp [hs]
    simpa [pow_two] using hz
  · rintro ⟨z, hz⟩
    refine ⟨z * s, ?_⟩
    rw [hz]
    ring

/-- When `d` is a nonzero square in odd characteristic, the split quadratic
norm represents every scalar. -/
lemma quadraticNormRepresents_of_isSquare
    {K : Type*} [Field K] (d c : K)
    (hchar : ringChar K ≠ 2) (hd0 : d ≠ 0) (hd : IsSquare d) :
    quadraticNormRepresents d c := by
  obtain ⟨t, ht⟩ := hd
  have ht0 : t ≠ 0 := by
    intro htzero
    apply hd0
    simpa [htzero] using ht
  rw [quadraticNormRepresents_iff_exists]
  refine ⟨(c + 1) / 2, (1 - c) / (2 * t), ?_⟩
  rw [ht]
  field_simp [Ring.two_ne_zero hchar, ht0]
  ring

/-- For nonzero parameters and targets in odd characteristic, quadratic norm
representation is symmetric.  This is the projective symmetry of the conic
`x² - d y² = c`. -/
lemma quadraticNormRepresents_symm
    {K : Type*} [Field K] {d c : K}
    (hchar : ringChar K ≠ 2) (hd : d ≠ 0) (hc : c ≠ 0) :
    quadraticNormRepresents d c ↔ quadraticNormRepresents c d := by
  have forward {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
      (hab : quadraticNormRepresents a b) :
      quadraticNormRepresents b a := by
    rw [quadraticNormRepresents_iff_exists] at hab
    obtain ⟨x, y, hxy⟩ := hab
    by_cases hy : y = 0
    · have hbsq : IsSquare b := by
        refine ⟨x, ?_⟩
        simpa [hy] using hxy.symm
      exact quadraticNormRepresents_of_isSquare b a hchar hb hbsq
    · rw [quadraticNormRepresents_iff_exists]
      refine ⟨x / y, 1 / y, ?_⟩
      calc
        x / y * (x / y) - b * (1 / y) * (1 / y) =
            (x * x - b) / (y * y) := by field_simp [hy]
        _ = (a * y * y) / (y * y) := by
          congr 1
          linear_combination hxy
        _ = a := by field_simp [hy]
  exact ⟨forward hd hc, forward hc hd⟩

/-- For nonsquare `d`, isotropy of `<1,-d,-c>` is equivalent to the quadratic
norm equation.  The nonsquare hypothesis forces the last coordinate of every
nonzero isotropic vector to be nonzero. -/
theorem ternaryDiagonal_gramIsotropic_iff_quadraticNormRepresents_of_not_isSquare
    {K : Type*} [Field K] (d c : K) (hd : ¬ IsSquare d) :
    GramIsotropic (Matrix.diagonal ![(1 : K), -d, -c]) ↔
      quadraticNormRepresents d c := by
  rw [quadraticNormRepresents_iff_exists]
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hv2 : v 2 ≠ 0 := by
      intro hv2
      have hxy : v 0 * v 0 - d * (v 1 * v 1) = 0 := by
        have h := hv
        simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, hv2] at h
        linear_combination h
      by_cases hv1 : v 1 = 0
      · have hv0coord : v 0 = 0 := by
          rw [hv1] at hxy
          simpa using hxy
        apply hv0
        funext i
        fin_cases i <;> assumption
      · apply hd
        refine ⟨v 0 / v 1, ?_⟩
        field_simp [hv1]
        linear_combination -hxy
    refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
    have h := hv
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h
    field_simp [hv2]
    linear_combination h
  · rintro ⟨x, y, hxy⟩
    refine ⟨![x, y, 1], ?_, ?_⟩
    · intro hzero
      have := congrFun hzero 2
      simp at this
    · simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
      linear_combination hxy

/-- Ternary norm reduction: in odd characteristic with `d` nonzero, the
diagonal form `<1,-d,-c>` is isotropic exactly when `c` is represented by the
norm from `K(√d)`. -/
theorem ternaryDiagonal_gramIsotropic_iff_quadraticNormRepresents
    {K : Type*} [Field K] (d c : K)
    (hchar : ringChar K ≠ 2) (hd0 : d ≠ 0) :
    GramIsotropic (Matrix.diagonal ![(1 : K), -d, -c]) ↔
      quadraticNormRepresents d c := by
  by_cases hd : IsSquare d
  · constructor
    · intro _
      exact quadraticNormRepresents_of_isSquare d c hchar hd0 hd
    · rw [quadraticNormRepresents_iff_exists]
      rintro ⟨x, y, hxy⟩
      refine ⟨![x, y, 1], ?_, ?_⟩
      · intro hzero
        have := congrFun hzero 2
        simp at this
      · simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]
        linear_combination hxy
  · exact
      ternaryDiagonal_gramIsotropic_iff_quadraticNormRepresents_of_not_isSquare
        d c hd

/-- Dividing a diagonal ternary Gram matrix by its nonzero leading
coefficient does not change isotropy. -/
lemma ternaryDiagonal_gramIsotropic_iff_normalized
    {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) :
    GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
      GramIsotropic (Matrix.diagonal ![(1 : K), b / a, c / a]) := by
  constructor <;> rintro ⟨v, hv0, hv⟩ <;> refine ⟨v, hv0, ?_⟩
  · have h := hv
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h ⊢
    field_simp [ha]
    linear_combination h
  · have h := hv
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h ⊢
    field_simp [ha] at h
    linear_combination h

/-- A diagonal ternary form `<a,b,c>` with `a` and `b` nonzero is isotropic
exactly when `-c/a` is represented by the quadratic norm associated to
`-b/a`. -/
theorem ternaryDiagonal_gramIsotropic_iff_quadraticNormRepresents_ratios
    {K : Type*} [Field K] (a b c : K)
    (hchar : ringChar K ≠ 2) (ha : a ≠ 0) (hb : b ≠ 0) :
    GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
      quadraticNormRepresents (-b / a) (-c / a) := by
  rw [ternaryDiagonal_gramIsotropic_iff_normalized a b c ha]
  simpa [neg_div] using
    ternaryDiagonal_gramIsotropic_iff_quadraticNormRepresents
      (-b / a) (-c / a) hchar (div_ne_zero (neg_ne_zero.mpr hb) ha)

end PositiveDefiniteIntegralLattice
