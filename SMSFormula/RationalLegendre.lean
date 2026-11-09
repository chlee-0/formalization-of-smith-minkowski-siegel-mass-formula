import SMSFormula.RationalHilbertReciprocity
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Legendre's ternary construction over the integers

This module starts an elementary replacement for the quadratic Hasse norm
input in the ternary rational Hasse--Minkowski proof.  The classical Legendre
argument first constructs a nonzero bounded integer triple on which a
diagonal ternary form takes the value `0` or `-a*b*c`.  The identity below
converts the second outcome to the first when `a` and `b` have the same
nonzero sign.  The CRT layer combines chosen roots of Legendre's three square
congruences into the linear divisibility condition used by the finite-box
argument.
-/

namespace Rat

/-- The integral diagonal ternary value used in Legendre's theorem. -/
def legendreTernaryValue
    (a b c x y z : ℤ) : ℤ :=
  a * x ^ 2 + b * y ^ 2 + c * z ^ 2

/-- The triangle bound for Legendre's integral ternary value. -/
lemma legendreTernaryValue_natAbs_le (a b c x y z : ℤ) :
    (legendreTernaryValue a b c x y z).natAbs ≤
      a.natAbs * x.natAbs ^ 2 +
      b.natAbs * y.natAbs ^ 2 +
      c.natAbs * z.natAbs ^ 2 := by
  unfold legendreTernaryValue
  calc
    (a * x ^ 2 + b * y ^ 2 + c * z ^ 2).natAbs ≤
        (a * x ^ 2 + b * y ^ 2).natAbs + (c * z ^ 2).natAbs :=
      Int.natAbs_add_le _ _
    _ ≤ ((a * x ^ 2).natAbs + (b * y ^ 2).natAbs) +
        (c * z ^ 2).natAbs := Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = a.natAbs * x.natAbs ^ 2 + b.natAbs * y.natAbs ^ 2 +
        c.natAbs * z.natAbs ^ 2 := by
      simp only [Int.natAbs_mul, Int.natAbs_pow]

/-- A multiple of a positive natural modulus with absolute value below twice
that modulus is `-M`, `0`, or `M`. -/
theorem eq_neg_natCast_or_zero_or_natCast_of_dvd_of_natAbs_lt_two_mul
    {M : ℕ} {q : ℤ} (hM : M ≠ 0) (hdvd : (M : ℤ) ∣ q)
    (hbound : q.natAbs < 2 * M) :
    q = -(M : ℤ) ∨ q = 0 ∨ q = M := by
  obtain ⟨k, rfl⟩ := hdvd
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hkabs : k.natAbs < 2 := by
    apply (Nat.mul_lt_mul_left hMpos).mp
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_comm] using hbound
  cases k with
  | ofNat n =>
      change n < 2 at hkabs
      have hn : n = 0 ∨ n = 1 := by omega
      rcases hn with rfl | rfl <;> simp
  | negSucc n =>
      change n + 1 < 2 at hkabs
      have hn : n = 0 := by omega
      subst n
      simp

/-- The canonical coordinate bound in Legendre's rectangular box. -/
def legendreBoxBound (u v : ℤ) : ℕ :=
  Nat.sqrt (u.natAbs * v.natAbs)

/-- Each weighted squared canonical box bound is at most `|a*b*c|`.  Cyclic
specializations give the corresponding estimates for all three coordinates. -/
lemma legendreBoxBound_weighted_sq_le (a b c : ℤ) :
    a.natAbs * legendreBoxBound b c ^ 2 ≤ (a * b * c).natAbs := by
  have h := Nat.mul_le_mul_left a.natAbs
    (Nat.sqrt_le' (b.natAbs * c.natAbs))
  simpa only [legendreBoxBound, Int.natAbs_mul, mul_assoc] using h

/-- The canonical Legendre box has strictly more points than the modulus
`|a*b*c|`. -/
theorem natAbs_mul_lt_legendreBox_card (a b c : ℤ) :
    (a * b * c).natAbs <
      (legendreBoxBound b c + 1) *
      (legendreBoxBound c a + 1) *
      (legendreBoxBound a b + 1) := by
  let A := a.natAbs
  let B := b.natAbs
  let C := c.natAbs
  let X := legendreBoxBound b c
  let Y := legendreBoxBound c a
  let Z := legendreBoxBound a b
  have hX : B * C < (X + 1) ^ 2 := by
    simpa only [X, B, C, legendreBoxBound] using
      Nat.lt_succ_sqrt' (b.natAbs * c.natAbs)
  have hY : C * A < (Y + 1) ^ 2 := by
    simpa only [Y, C, A, legendreBoxBound] using
      Nat.lt_succ_sqrt' (c.natAbs * a.natAbs)
  have hZ : A * B < (Z + 1) ^ 2 := by
    simpa only [Z, A, B, legendreBoxBound] using
      Nat.lt_succ_sqrt' (a.natAbs * b.natAbs)
  apply Nat.mul_self_lt_mul_self_iff.mp
  calc
    (a * b * c).natAbs * (a * b * c).natAbs =
        (B * C) * (C * A) * (A * B) := by
      simp only [A, B, C, Int.natAbs_mul]
      ring
    _ < (X + 1) ^ 2 * (Y + 1) ^ 2 * (Z + 1) ^ 2 := by
      gcongr
    _ = ((legendreBoxBound b c + 1) *
          (legendreBoxBound c a + 1) *
          (legendreBoxBound a b + 1)) *
        ((legendreBoxBound b c + 1) *
          (legendreBoxBound c a + 1) *
          (legendreBoxBound a b + 1)) := by
      simp only [X, Y, Z]
      ring

/-- With two positive coefficients and one negative coefficient, the
canonical box bounds put the ternary value between `-|a*b*c|` and
`2*|a*b*c|`. -/
lemma legendreTernaryValue_bounds_of_signs_of_boxBounds
    {a b c x y z : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hx : x.natAbs ≤ legendreBoxBound b c)
    (hy : y.natAbs ≤ legendreBoxBound c a)
    (hz : z.natAbs ≤ legendreBoxBound a b) :
    -((a * b * c).natAbs : ℤ) ≤ legendreTernaryValue a b c x y z ∧
      legendreTernaryValue a b c x y z ≤
        2 * ((a * b * c).natAbs : ℤ) := by
  let M := (a * b * c).natAbs
  have haxNat : a.natAbs * x.natAbs ^ 2 ≤ M := by
    calc
      a.natAbs * x.natAbs ^ 2 ≤
          a.natAbs * legendreBoxBound b c ^ 2 := by gcongr
      _ ≤ M := legendreBoxBound_weighted_sq_le a b c
  have hbyNat : b.natAbs * y.natAbs ^ 2 ≤ M := by
    calc
      b.natAbs * y.natAbs ^ 2 ≤
          b.natAbs * legendreBoxBound c a ^ 2 := by gcongr
      _ ≤ M := by
        simpa only [M, mul_comm, mul_left_comm, mul_assoc] using
          legendreBoxBound_weighted_sq_le b c a
  have hczNat : c.natAbs * z.natAbs ^ 2 ≤ M := by
    calc
      c.natAbs * z.natAbs ^ 2 ≤
          c.natAbs * legendreBoxBound a b ^ 2 := by gcongr
      _ ≤ M := by
        simpa only [M, mul_comm, mul_left_comm, mul_assoc] using
          legendreBoxBound_weighted_sq_le c a b
  have hax : a * x ^ 2 ≤ (M : ℤ) := by
    have haxCast :
        ((a.natAbs * x.natAbs ^ 2 : ℕ) : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast haxNat
    simpa [Int.natAbs_of_nonneg ha.le] using haxCast
  have hby : b * y ^ 2 ≤ (M : ℤ) := by
    have hbyCast :
        ((b.natAbs * y.natAbs ^ 2 : ℕ) : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hbyNat
    simpa [Int.natAbs_of_nonneg hb.le] using hbyCast
  have hcz : (-c) * z ^ 2 ≤ (M : ℤ) := by
    have hczCast :
        ((c.natAbs * z.natAbs ^ 2 : ℕ) : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hczNat
    simpa [Int.natCast_natAbs, abs_of_neg hc] using hczCast
  unfold legendreTernaryValue
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- The upper canonical-box bound is strict as soon as either positive
weighted square is strictly below `|a*b*c|`. -/
lemma legendreTernaryValue_lt_two_mul_natAbs_of_signs_of_boxBounds
    {a b c x y z : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hx : x.natAbs ≤ legendreBoxBound b c)
    (hy : y.natAbs ≤ legendreBoxBound c a)
    (hstrict :
      a.natAbs * x.natAbs ^ 2 < (a * b * c).natAbs ∨
      b.natAbs * y.natAbs ^ 2 < (a * b * c).natAbs) :
    legendreTernaryValue a b c x y z <
      2 * ((a * b * c).natAbs : ℤ) := by
  let M := (a * b * c).natAbs
  have haxNat : a.natAbs * x.natAbs ^ 2 ≤ M := by
    calc
      a.natAbs * x.natAbs ^ 2 ≤
          a.natAbs * legendreBoxBound b c ^ 2 := by gcongr
      _ ≤ M := legendreBoxBound_weighted_sq_le a b c
  have hbyNat : b.natAbs * y.natAbs ^ 2 ≤ M := by
    calc
      b.natAbs * y.natAbs ^ 2 ≤
          b.natAbs * legendreBoxBound c a ^ 2 := by gcongr
      _ ≤ M := by
        simpa only [M, mul_comm, mul_left_comm, mul_assoc] using
          legendreBoxBound_weighted_sq_le b c a
  have hax : a * x ^ 2 ≤ (M : ℤ) := by
    have haxCast :
        ((a.natAbs * x.natAbs ^ 2 : ℕ) : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast haxNat
    simpa [Int.natAbs_of_nonneg ha.le] using haxCast
  have hby : b * y ^ 2 ≤ (M : ℤ) := by
    have hbyCast :
        ((b.natAbs * y.natAbs ^ 2 : ℕ) : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hbyNat
    simpa [Int.natAbs_of_nonneg hb.le] using hbyCast
  rcases hstrict with haxNatLt | hbyNatLt
  · have haxLt : a * x ^ 2 < (M : ℤ) := by
      have haxCast :
          ((a.natAbs * x.natAbs ^ 2 : ℕ) : ℤ) < (M : ℤ) := by
        exact_mod_cast haxNatLt
      simpa [Int.natAbs_of_nonneg ha.le] using haxCast
    unfold legendreTernaryValue
    nlinarith [sq_nonneg z]
  · have hbyLt : b * y ^ 2 < (M : ℤ) := by
      have hbyCast :
          ((b.natAbs * y.natAbs ^ 2 : ℕ) : ℤ) < (M : ℤ) := by
        exact_mod_cast hbyNatLt
      simpa [Int.natAbs_of_nonneg hb.le] using hbyCast
    unfold legendreTernaryValue
    nlinarith [sq_nonneg z]

/-- A squarefree natural number that is a square is one. -/
lemma nat_eq_one_of_squarefree_of_isSquare {n : ℕ} (hn : Squarefree n)
    (hsquare : IsSquare n) : n = 1 := by
  obtain ⟨m, rfl⟩ := hsquare
  have hunit : IsUnit m := by
    apply hn m
    exact ⟨1, by simp⟩
  have hm : m = 1 := Nat.isUnit_iff.mp hunit
  simp [hm]

/-- If both positive weighted squares saturate the canonical modulus, then
squarefreeness forces all three coefficient absolute values to be one. -/
lemma natAbs_eq_one_of_two_weightedSquares_eq
    {a b c x y : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hx : a.natAbs * x.natAbs ^ 2 = (a * b * c).natAbs)
    (hy : b.natAbs * y.natAbs ^ 2 = (a * b * c).natAbs) :
    a.natAbs = 1 ∧ b.natAbs = 1 ∧ c.natAbs = 1 := by
  have haPos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hbPos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hxSq : x.natAbs ^ 2 = b.natAbs * c.natAbs := by
    apply Nat.eq_of_mul_eq_mul_left haPos
    simpa only [Int.natAbs_mul, mul_assoc] using hx
  have hySq : y.natAbs ^ 2 = c.natAbs * a.natAbs := by
    apply Nat.eq_of_mul_eq_mul_left hbPos
    simpa only [Int.natAbs_mul, mul_assoc, mul_comm, mul_left_comm] using hy
  have hbcSq : Squarefree (b.natAbs * c.natAbs) :=
    (Nat.squarefree_mul hbc).2 ⟨hsb, hsc⟩
  have hcaSq : Squarefree (c.natAbs * a.natAbs) :=
    (Nat.squarefree_mul hac.symm).2 ⟨hsc, hsa⟩
  have hbcOne : b.natAbs * c.natAbs = 1 :=
    nat_eq_one_of_squarefree_of_isSquare hbcSq
      ⟨x.natAbs, by simpa [pow_two] using hxSq.symm⟩
  have hcaOne : c.natAbs * a.natAbs = 1 :=
    nat_eq_one_of_squarefree_of_isSquare hcaSq
      ⟨y.natAbs, by simpa [pow_two] using hySq.symm⟩
  obtain ⟨hbOne, hcOne⟩ := mul_eq_one.mp hbcOne
  obtain ⟨_, haOne⟩ := mul_eq_one.mp hcaOne
  exact ⟨haOne, hbOne, hcOne⟩

/-- Unless every coefficient has absolute value one, one of the two positive
weighted squares is strictly below the canonical modulus. -/
lemma one_weightedSquare_lt_of_squarefree_of_not_all_natAbs_eq_one
    {a b c x y : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hx : x.natAbs ≤ legendreBoxBound b c)
    (hy : y.natAbs ≤ legendreBoxBound c a)
    (hnot : ¬(a.natAbs = 1 ∧ b.natAbs = 1 ∧ c.natAbs = 1)) :
    a.natAbs * x.natAbs ^ 2 < (a * b * c).natAbs ∨
      b.natAbs * y.natAbs ^ 2 < (a * b * c).natAbs := by
  have hax : a.natAbs * x.natAbs ^ 2 ≤ (a * b * c).natAbs := by
    calc
      a.natAbs * x.natAbs ^ 2 ≤
          a.natAbs * legendreBoxBound b c ^ 2 := by gcongr
      _ ≤ (a * b * c).natAbs :=
        legendreBoxBound_weighted_sq_le a b c
  have hby : b.natAbs * y.natAbs ^ 2 ≤ (a * b * c).natAbs := by
    calc
      b.natAbs * y.natAbs ^ 2 ≤
          b.natAbs * legendreBoxBound c a ^ 2 := by gcongr
      _ ≤ (a * b * c).natAbs := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          legendreBoxBound_weighted_sq_le b c a
  rcases lt_or_eq_of_le hax with haxLt | haxEq
  · exact Or.inl haxLt
  rcases lt_or_eq_of_le hby with hbyLt | hbyEq
  · exact Or.inr hbyLt
  exact False.elim <| hnot <|
    natAbs_eq_one_of_two_weightedSquares_eq
      ha hb hsa hsb hsc hac hbc haxEq hbyEq

/-- For squarefree coefficients not all of absolute value one, the canonical
box value has strict upper bound `2*|a*b*c|`. -/
lemma legendreTernaryValue_lt_two_mul_natAbs_of_signs_of_squarefree
    {a b c x y z : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hx : x.natAbs ≤ legendreBoxBound b c)
    (hy : y.natAbs ≤ legendreBoxBound c a)
    (hnot : ¬(a.natAbs = 1 ∧ b.natAbs = 1 ∧ c.natAbs = 1)) :
    legendreTernaryValue a b c x y z <
      2 * ((a * b * c).natAbs : ℤ) := by
  exact legendreTernaryValue_lt_two_mul_natAbs_of_signs_of_boxBounds
    ha hb hc hx hy
      (one_weightedSquare_lt_of_squarefree_of_not_all_natAbs_eq_one
        (ne_of_gt ha) (ne_of_gt hb) hsa hsb hsc hac hbc hx hy hnot)

/-- The signed coefficient case with all absolute values one has the explicit
nontrivial zero `(1, 0, 1)`. -/
lemma exists_legendreTernaryValue_eq_zero_of_all_natAbs_eq_one
    {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (haOne : a.natAbs = 1) (hbOne : b.natAbs = 1)
    (hcOne : c.natAbs = 1) :
    ∃ x y z : ℤ, z ≠ 0 ∧ legendreTernaryValue a b c x y z = 0 := by
  have haEq : a = 1 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) haOne
    simpa [Int.natAbs_of_nonneg ha.le] using hcast
  have hbEq : b = 1 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hbOne
    simpa [Int.natAbs_of_nonneg hb.le] using hcast
  have hcEq : c = -1 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hcOne
    have : -c = 1 := by
      simpa [Int.natCast_natAbs, abs_of_neg hc] using hcast
    omega
  refine ⟨1, 0, 1, by norm_num, ?_⟩
  simp [legendreTernaryValue, haEq, hbEq, hcEq]

/-- Equality at the lower signed box bound forces both positive coordinates
to vanish.  For squarefree coprime positive coefficients, their absolute
values must both be one; the negative coefficient remains unrestricted. -/
lemma lower_endpoint_structure_of_signs_of_squarefree
    {a b c x y z : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hz : z.natAbs ≤ legendreBoxBound a b)
    (hvalue : legendreTernaryValue a b c x y z =
      -((a * b * c).natAbs : ℤ)) :
    x = 0 ∧ y = 0 ∧
      c.natAbs * z.natAbs ^ 2 = (a * b * c).natAbs ∧
      a.natAbs = 1 ∧ b.natAbs = 1 := by
  let M := (a * b * c).natAbs
  have hczNat : c.natAbs * z.natAbs ^ 2 ≤ M := by
    calc
      c.natAbs * z.natAbs ^ 2 ≤
          c.natAbs * legendreBoxBound a b ^ 2 := by gcongr
      _ ≤ M := by
        simpa only [M, mul_comm, mul_left_comm, mul_assoc] using
          legendreBoxBound_weighted_sq_le c a b
  have hcz : (-c) * z ^ 2 ≤ (M : ℤ) := by
    have hcast :
        ((c.natAbs * z.natAbs ^ 2 : ℕ) : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hczNat
    simpa [Int.natCast_natAbs, abs_of_neg hc] using hcast
  have hvalue' : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = -(M : ℤ) := by
    simpa only [legendreTernaryValue] using hvalue
  have hxZero : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hyZero : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hczEq : (-c) * z ^ 2 = (M : ℤ) := by
    rw [hxZero, hyZero] at hvalue'
    norm_num at hvalue' ⊢
    nlinarith
  have hczNatEq : c.natAbs * z.natAbs ^ 2 = M := by
    have hcast :
        ((c.natAbs * z.natAbs ^ 2 : ℕ) : ℤ) = (M : ℤ) := by
      simpa [Int.natCast_natAbs, abs_of_neg hc] using hczEq
    exact_mod_cast hcast
  have hcPos : 0 < c.natAbs := Int.natAbs_pos.mpr (ne_of_lt hc)
  have hzSq : z.natAbs ^ 2 = a.natAbs * b.natAbs := by
    apply Nat.eq_of_mul_eq_mul_left hcPos
    simpa only [M, Int.natAbs_mul, mul_comm, mul_left_comm, mul_assoc] using
      hczNatEq
  have habSq : Squarefree (a.natAbs * b.natAbs) :=
    (Nat.squarefree_mul hab).2 ⟨hsa, hsb⟩
  have habOne : a.natAbs * b.natAbs = 1 :=
    nat_eq_one_of_squarefree_of_isSquare habSq
      ⟨z.natAbs, by simpa [pow_two] using hzSq.symm⟩
  obtain ⟨haOne, hbOne⟩ := mul_eq_one.mp habOne
  exact ⟨hxZero, hyZero, hczNatEq, haOne, hbOne⟩

/-- An explicit integer square root of `-1` modulo `n` produces a natural
sum-of-two-squares representation of `n`. -/
lemma exists_eq_sq_add_sq_of_int_sq_modEq_neg_one
    {n : ℕ} {r : ℤ} (hr : r ^ 2 ≡ -1 [ZMOD n]) :
    ∃ u v : ℕ, n = u ^ 2 + v ^ 2 := by
  apply Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
  refine ⟨(r : ZMod n), ?_⟩
  have hcast := (ZMod.intCast_eq_intCast_iff _ _ _).2 hr
  simpa only [Int.cast_neg, Int.cast_one, Int.cast_pow, Int.cast_mul, pow_two] using
    hcast.symm

/-- When the two positive coefficients have absolute value one, the third
Legendre congruence gives an explicit nontrivial zero via the sum-of-two-
squares theorem. -/
lemma exists_legendreTernaryValue_eq_zero_of_two_natAbs_eq_one_of_modEq
    {a b c r : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (haOne : a.natAbs = 1) (hbOne : b.natAbs = 1)
    (hr : r ^ 2 ≡ -(a * b) [ZMOD c.natAbs]) :
    ∃ x y z : ℤ, z ≠ 0 ∧ legendreTernaryValue a b c x y z = 0 := by
  have haEq : a = 1 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) haOne
    simpa [Int.natAbs_of_nonneg ha.le] using hcast
  have hbEq : b = 1 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hbOne
    simpa [Int.natAbs_of_nonneg hb.le] using hcast
  have hrNegOne : r ^ 2 ≡ -1 [ZMOD c.natAbs] := by
    simpa only [haEq, hbEq, one_mul] using hr
  obtain ⟨u, v, huv⟩ := exists_eq_sq_add_sq_of_int_sq_modEq_neg_one hrNegOne
  have hcEq : c = -(c.natAbs : ℤ) := by
    have hnat : (c.natAbs : ℤ) = -c := by
      rw [Int.natCast_natAbs, abs_of_neg hc]
    omega
  have huvInt : (c.natAbs : ℤ) = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 := by
    exact_mod_cast huv
  refine ⟨u, v, 1, by norm_num, ?_⟩
  unfold legendreTernaryValue
  rw [haEq, hbEq, hcEq]
  norm_num
  nlinarith

/-- The composition identity that converts the exceptional value `-a*b*c`
in Legendre's finite-box argument into an isotropic vector. -/
lemma legendreTernaryValue_composition
    (a b c x y z : ℤ) :
    legendreTernaryValue a b c
        (x * z + b * y) (y * z - a * x) (z ^ 2 + a * b) =
      (z ^ 2 + a * b) *
        (legendreTernaryValue a b c x y z + a * b * c) := by
  unfold legendreTernaryValue
  ring

/-- If two coefficients have the same nonzero sign, a representation of the
exceptional value `-a*b*c` gives a nontrivial integral zero of the ternary
form.  The transformed final coordinate is strictly positive. -/
theorem exists_legendreTernaryValue_eq_zero_of_eq_neg_mul
    {a b c x y z : ℤ} (hab : 0 < a * b)
    (hvalue : legendreTernaryValue a b c x y z = -(a * b * c)) :
    ∃ X Y Z : ℤ, Z ≠ 0 ∧ legendreTernaryValue a b c X Y Z = 0 := by
  have hZpos : 0 < z ^ 2 + a * b :=
    add_pos_of_nonneg_of_pos (sq_nonneg z) hab
  refine ⟨x * z + b * y, y * z - a * x, z ^ 2 + a * b,
    ne_of_gt hZpos, ?_⟩
  rw [legendreTernaryValue_composition, hvalue]
  ring

/-- A nontrivial zero of a binary diagonal form over a field gives an
explicit square root of the negative coefficient product. -/
lemma exists_sq_eq_neg_mul_of_binary_eq_zero
    {K : Type*} [Field K] {b c y z : K}
    (hb : b ≠ 0) (hyz : y ≠ 0 ∨ z ≠ 0)
    (hzero : b * y ^ 2 + c * z ^ 2 = 0) :
    ∃ r : K, r ^ 2 = -(b * c) := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero] at hzero
    have hy : y = 0 := by
      apply (sq_eq_zero_iff).mp
      exact (mul_eq_zero.mp hzero).resolve_left hb
    exact hyz.elim (· hy) (· rfl)
  refine ⟨b * y / z, ?_⟩
  field_simp
  linear_combination hzero

/-- A binary zero in the p-adic residue field, represented by integral
coordinates, gives an integer square root of the negative coefficient product
modulo `p`. -/
lemma exists_int_sq_modEq_neg_mul_of_padicInt_binary_residue_zero
    {p : ℕ} [Fact p.Prime] {b c : ℤ} {y z : ℤ_[p]}
    (hb : ¬(p : ℤ) ∣ b)
    (hyz : PadicInt.toZMod y ≠ 0 ∨ PadicInt.toZMod z ≠ 0)
    (hzero :
      (b : ZMod p) * PadicInt.toZMod y ^ 2 +
        (c : ZMod p) * PadicInt.toZMod z ^ 2 = 0) :
    ∃ r : ℤ, r ^ 2 ≡ -(b * c) [ZMOD p] := by
  have hbres : (b : ZMod p) ≠ 0 := by
    intro hzero
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hzero)
  obtain ⟨r, hr⟩ := exists_sq_eq_neg_mul_of_binary_eq_zero
    hbres hyz hzero
  refine ⟨(r.val : ℕ), ?_⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  simpa only [Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_mul,
    ZMod.natCast_zmod_val] using hr

/-- A p-adic integral binary zero with a nonzero residue coordinate gives an
integer square root of the negative coefficient product modulo `p`. -/
lemma exists_int_sq_modEq_neg_mul_of_padicInt_binary_zero
    {p : ℕ} [Fact p.Prime] {b c : ℤ} {y z : ℤ_[p]}
    (hb : ¬(p : ℤ) ∣ b)
    (hyz : PadicInt.toZMod y ≠ 0 ∨ PadicInt.toZMod z ≠ 0)
    (hzero : (b : ℤ_[p]) * y ^ 2 + (c : ℤ_[p]) * z ^ 2 = 0) :
    ∃ r : ℤ, r ^ 2 ≡ -(b * c) [ZMOD p] := by
  apply exists_int_sq_modEq_neg_mul_of_padicInt_binary_residue_zero hb hyz
  simpa using congrArg PadicInt.toZMod hzero

private lemma exists_padicInt_common_scale_of_dominating_coordinate
    {p : ℕ} [Fact p.Prime] {x y z t : ℚ_[p]}
    (ht : t ≠ 0) (htcoord : t = x ∨ t = y ∨ t = z)
    (hx : ‖x‖ ≤ ‖t‖) (hy : ‖y‖ ≤ ‖t‖) (hz : ‖z‖ ≤ ‖t‖) :
    ∃ s : ℚ_[p], s ≠ 0 ∧ ∃ X Y Z : ℤ_[p],
      (X : ℚ_[p]) = x * s ∧
      (Y : ℚ_[p]) = y * s ∧
      (Z : ℚ_[p]) = z * s ∧
      (IsUnit X ∨ IsUnit Y ∨ IsUnit Z) ∧
      (PadicInt.toZMod X ≠ 0 ∨ PadicInt.toZMod Y ≠ 0 ∨
        PadicInt.toZMod Z ≠ 0) := by
  let s : ℚ_[p] := t⁻¹
  let X : ℤ_[p] := ⟨x / t, by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr ht)).2 hx⟩
  let Y : ℤ_[p] := ⟨y / t, by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr ht)).2 hy⟩
  let Z : ℤ_[p] := ⟨z / t, by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr ht)).2 hz⟩
  have hs : s ≠ 0 := inv_ne_zero ht
  have hunit : IsUnit X ∨ IsUnit Y ∨ IsUnit Z := by
    rcases htcoord with rfl | rfl | rfl
    · left
      have hX : X = 1 := by
        apply Subtype.ext
        simp [X, ht]
      simp [hX]
    · right; left
      have hY : Y = 1 := by
        apply Subtype.ext
        simp [Y, ht]
      simp [hY]
    · right; right
      have hZ : Z = 1 := by
        apply Subtype.ext
        simp [Z, ht]
      simp [hZ]
  have hres : PadicInt.toZMod X ≠ 0 ∨ PadicInt.toZMod Y ≠ 0 ∨
      PadicInt.toZMod Z ≠ 0 := by
    rcases hunit with hX | hY | hZ
    · exact Or.inl (PadicInt.toZMod_ne_zero_of_isUnit hX)
    · exact Or.inr (Or.inl (PadicInt.toZMod_ne_zero_of_isUnit hY))
    · exact Or.inr (Or.inr (PadicInt.toZMod_ne_zero_of_isUnit hZ))
  refine ⟨s, hs, X, Y, Z, ?_, ?_, ?_, hunit, hres⟩
  · simp only [X, s, div_eq_mul_inv]
  · simp only [Y, s, div_eq_mul_inv]
  · simp only [Z, s, div_eq_mul_inv]

/-- A nontrivial p-adic triple can be scaled simultaneously into integral
coordinates, at least one of which is a unit with nonzero residue. -/
theorem exists_padicInt_common_scale_of_nontrivial_triple
    {p : ℕ} [Fact p.Prime] {x y z : ℚ_[p]}
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    ∃ s : ℚ_[p], s ≠ 0 ∧ ∃ X Y Z : ℤ_[p],
      (X : ℚ_[p]) = x * s ∧
      (Y : ℚ_[p]) = y * s ∧
      (Z : ℚ_[p]) = z * s ∧
      (IsUnit X ∨ IsUnit Y ∨ IsUnit Z) ∧
      (PadicInt.toZMod X ≠ 0 ∨ PadicInt.toZMod Y ≠ 0 ∨
        PadicInt.toZMod Z ≠ 0) := by
  by_cases hxmax : ‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖
  · have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      have hy0 : y = 0 := norm_eq_zero.mp
        (le_antisymm (by simpa using hxmax.1) (norm_nonneg y))
      have hz0 : z = 0 := norm_eq_zero.mp
        (le_antisymm (by simpa using hxmax.2) (norm_nonneg z))
      simp [hy0, hz0] at hnonzero
    exact exists_padicInt_common_scale_of_dominating_coordinate
      hx0 (Or.inl rfl) le_rfl hxmax.1 hxmax.2
  · by_cases hymax : ‖z‖ ≤ ‖y‖
    · have hxy : ‖x‖ ≤ ‖y‖ := by
        by_contra hxy
        have hyx : ‖y‖ ≤ ‖x‖ := le_of_lt (lt_of_not_ge hxy)
        exact hxmax ⟨hyx, hymax.trans hyx⟩
      have hy0 : y ≠ 0 := by
        intro hy0
        subst y
        have hx0 : x = 0 := norm_eq_zero.mp
          (le_antisymm (by simpa using hxy) (norm_nonneg x))
        have hz0 : z = 0 := norm_eq_zero.mp
          (le_antisymm (by simpa using hymax) (norm_nonneg z))
        simp [hx0, hz0] at hnonzero
      exact exists_padicInt_common_scale_of_dominating_coordinate
        hy0 (Or.inr (Or.inl rfl)) hxy le_rfl hymax
    · have hyz : ‖y‖ ≤ ‖z‖ := le_of_lt (lt_of_not_ge hymax)
      have hxz : ‖x‖ ≤ ‖z‖ := by
        by_contra hxz
        have hzx : ‖z‖ ≤ ‖x‖ := le_of_lt (lt_of_not_ge hxz)
        exact hxmax ⟨hyz.trans hzx, hzx⟩
      have hz0 : z ≠ 0 := by
        intro hz0
        subst z
        have hx0 : x = 0 := norm_eq_zero.mp
          (le_antisymm (by simpa using hxz) (norm_nonneg x))
        have hy0 : y = 0 := norm_eq_zero.mp
          (le_antisymm (by simpa using hyz) (norm_nonneg y))
        simp [hx0, hy0] at hnonzero
      exact exists_padicInt_common_scale_of_dominating_coordinate
        hz0 (Or.inr (Or.inr rfl)) hxz hyz le_rfl

/-- Common scaling preserves a homogeneous p-adic ternary zero while making
its coordinates integral with at least one unit residue. -/
theorem exists_padicInt_normalized_ternary_zero
    {p : ℕ} [Fact p.Prime] {a b c x y z : ℚ_[p]}
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (hzero : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    ∃ X Y Z : ℤ_[p],
      (IsUnit X ∨ IsUnit Y ∨ IsUnit Z) ∧
      (PadicInt.toZMod X ≠ 0 ∨ PadicInt.toZMod Y ≠ 0 ∨
        PadicInt.toZMod Z ≠ 0) ∧
      a * (X : ℚ_[p]) ^ 2 + b * (Y : ℚ_[p]) ^ 2 +
        c * (Z : ℚ_[p]) ^ 2 = 0 := by
  obtain ⟨s, _, X, Y, Z, hX, hY, hZ, hunit, hres⟩ :=
    exists_padicInt_common_scale_of_nontrivial_triple hnonzero
  refine ⟨X, Y, Z, hunit, hres, ?_⟩
  rw [hX, hY, hZ]
  calc
    a * (x * s) ^ 2 + b * (y * s) ^ 2 + c * (z * s) ^ 2 =
        (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) * s ^ 2 := by ring
    _ = 0 := by rw [hzero, zero_mul]

/-- In a normalized integral ternary zero with squarefree first integer
coefficient, one of the last two coordinates has nonzero residue. -/
lemma padicInt_second_or_third_residue_ne_zero_of_squarefree_ternary_zero
    {p : ℕ} [Fact p.Prime] {a b c : ℤ} {X Y Z : ℤ_[p]}
    (hsa : Squarefree a.natAbs)
    (hres : PadicInt.toZMod X ≠ 0 ∨ PadicInt.toZMod Y ≠ 0 ∨
      PadicInt.toZMod Z ≠ 0)
    (hzero : (a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2 +
      (c : ℤ_[p]) * Z ^ 2 = 0) :
    PadicInt.toZMod Y ≠ 0 ∨ PadicInt.toZMod Z ≠ 0 := by
  by_contra hyz
  simp only [not_or, ne_eq, not_not] at hyz
  have hXres : PadicInt.toZMod X ≠ 0 := hres.resolve_right (by simp [hyz])
  have hXunit : IsUnit X := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro hXzero
    apply hXres
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    simp [hXzero]
  have hYdvd : (p : ℤ_[p]) ∣ Y := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hyz.1
  have hZdvd : (p : ℤ_[p]) ∣ Z := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hyz.2
  obtain ⟨Y', hY⟩ := hYdvd
  obtain ⟨Z', hZ⟩ := hZdvd
  have hrest : (p : ℤ_[p]) ^ 2 ∣
      (b : ℤ_[p]) * Y ^ 2 + (c : ℤ_[p]) * Z ^ 2 := by
    refine ⟨(b : ℤ_[p]) * Y' ^ 2 + (c : ℤ_[p]) * Z' ^ 2, ?_⟩
    rw [hY, hZ]
    ring
  have hAX : (a : ℤ_[p]) * X ^ 2 =
      -((b : ℤ_[p]) * Y ^ 2 + (c : ℤ_[p]) * Z ^ 2) := by
    linear_combination hzero
  have hAXdvd : (p : ℤ_[p]) ^ 2 ∣ (a : ℤ_[p]) * X ^ 2 := by
    rw [hAX]
    exact dvd_neg.mpr hrest
  have hadvdPadic : (p : ℤ_[p]) ^ 2 ∣ (a : ℤ_[p]) :=
    (hXunit.pow 2).dvd_mul_right.mp hAXdvd
  have hadvdInt : (p ^ 2 : ℤ) ∣ a :=
    (PadicInt.pow_p_dvd_int_iff 2 a).mp hadvdPadic
  have hadvdNat : p ^ 2 ∣ a.natAbs := Int.natCast_dvd.mp hadvdInt
  exact (Nat.squarefree_iff_prime_squarefree.mp hsa p Fact.out)
    (by simpa [pow_two] using hadvdNat)

/-- A nontrivial p-adic ternary zero with squarefree first integer coefficient
has an integral normalization in which one of the last two residues is
nonzero. -/
theorem exists_padicInt_normalized_ternary_zero_second_or_third_residue
    {p : ℕ} [Fact p.Prime] {a b c : ℤ} {x y z : ℚ_[p]}
    (hsa : Squarefree a.natAbs)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (hzero : (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 +
      (c : ℚ_[p]) * z ^ 2 = 0) :
    ∃ X Y Z : ℤ_[p],
      (PadicInt.toZMod Y ≠ 0 ∨ PadicInt.toZMod Z ≠ 0) ∧
      (a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2 +
        (c : ℤ_[p]) * Z ^ 2 = 0 := by
  obtain ⟨X, Y, Z, _, hres, hzeroQ⟩ :=
    exists_padicInt_normalized_ternary_zero hnonzero hzero
  have hzeroInt : (a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2 +
      (c : ℤ_[p]) * Z ^ 2 = 0 := by
    apply Subtype.coe_injective
    simpa using hzeroQ
  exact ⟨X, Y, Z,
    padicInt_second_or_third_residue_ne_zero_of_squarefree_ternary_zero
      hsa hres hzeroInt,
    hzeroInt⟩

/-- A nontrivial p-adic zero of a ternary form gives the Legendre congruence
root at a prime dividing its squarefree first coefficient. -/
theorem exists_int_sq_modEq_neg_mul_of_padic_ternary_zero
    {p : ℕ} [Fact p.Prime] {a b c : ℤ} {x y z : ℚ_[p]}
    (hsa : Squarefree a.natAbs) (hpa : p ∣ a.natAbs)
    (hb : ¬(p : ℤ) ∣ b)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (hzero : (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 +
      (c : ℚ_[p]) * z ^ 2 = 0) :
    ∃ r : ℤ, r ^ 2 ≡ -(b * c) [ZMOD p] := by
  obtain ⟨X, Y, Z, hyz, hzeroInt⟩ :=
    exists_padicInt_normalized_ternary_zero_second_or_third_residue
      hsa hnonzero hzero
  have hares : (a : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd a p).2 (Int.natCast_dvd.mpr hpa)
  have hzeroRes :
      (b : ZMod p) * PadicInt.toZMod Y ^ 2 +
        (c : ZMod p) * PadicInt.toZMod Z ^ 2 = 0 := by
    have hmap := congrArg PadicInt.toZMod hzeroInt
    simpa [hares] using hmap
  exact exists_int_sq_modEq_neg_mul_of_padicInt_binary_residue_zero
    hb hyz hzeroRes

/-- Primewise square roots combine to a square root modulo a squarefree
natural number.  The empty prime-factor set handles modulus one. -/
theorem exists_int_sq_modEq_of_prime_roots_of_squarefree
    (d : ℤ) {n : ℕ} (hn : Squarefree n)
    (hlocal : ∀ p, p.Prime → p ∣ n →
      ∃ r : ℤ, r ^ 2 ≡ d [ZMOD p]) :
    ∃ r : ℤ, r ^ 2 ≡ d [ZMOD n] := by
  classical
  let root : ℕ → ℤ := fun p =>
    if hp : p ∈ n.primeFactors then
      Classical.choose
        (hlocal p (Nat.prime_of_mem_primeFactors hp)
          ((Nat.mem_primeFactors.mp hp).2.1))
    else 0
  have hroot (p : ℕ) (hp : p ∈ n.primeFactors) :
      root p ^ 2 ≡ d [ZMOD p] := by
    simp only [root, dif_pos hp]
    exact Classical.choose_spec
      (hlocal p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors.mp hp).2.1))
  let residue : ℕ → ℕ := fun p => (root p : ZMod p).val
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have hne (p : ℕ) (hp : p ∈ n.primeFactors) : p ≠ 0 :=
    (hprime p hp).ne_zero
  have hpair : Set.Pairwise (n.primeFactors : Set ℕ)
      (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).2 hpq
  let R : ℕ :=
    Nat.chineseRemainderOfFinset residue id n.primeFactors hne hpair
  have hR (p : ℕ) (hp : p ∈ n.primeFactors) :
      R ≡ residue p [MOD p] :=
    (Nat.chineseRemainderOfFinset residue id n.primeFactors hne hpair).prop
      p hp
  refine ⟨(R : ℤ), ?_⟩
  rw [← Nat.prod_primeFactors_of_squarefree hn]
  apply Int.modEq_iff_dvd.mpr
  have hprod : (∏ p ∈ n.primeFactors, (p : ℤ)) ∣ d - (R : ℤ) ^ 2 := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (hprime p hp) (hprime q hq)).2 hpq).isCoprime
    · intro p hp
      apply Int.ModEq.dvd
      haveI : NeZero p := ⟨hne p hp⟩
      have hRres : (R : ℤ) ≡ (residue p : ℤ) [ZMOD p] :=
        Int.natCast_modEq_iff.mpr (hR p hp)
      have hresRoot : (residue p : ℤ) ≡ root p [ZMOD p] := by
        apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
        simpa only [residue, Int.cast_natCast] using
          (ZMod.natCast_zmod_val (root p : ZMod p))
      exact ((hRres.trans hresRoot).pow 2).trans (hroot p hp)
  simpa using hprod

/-- An integer is a square modulo the absolute value of a possibly signed
modulus. -/
def IsSquareModuloNatAbs (d m : ℤ) : Prop :=
  ∃ r : ℤ, r ^ 2 ≡ d [ZMOD m.natAbs]

/-- Isotropy of a diagonal ternary Gram matrix is the corresponding explicit
nontrivial coordinate equation. -/
theorem ternaryDiagonal_gramIsotropic_iff_exists_coordinates
    {K : Type*} [Field K] (a b c : K) :
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
      ∃ x y z : K,
        (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
        a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v 0, v 1, v 2, ?_, ?_⟩
    · by_contra hcoords
      push_neg at hcoords
      apply hv0
      funext i
      fin_cases i <;> simp_all
    · have h := hv
      simp [PositiveDefiniteIntegralLattice.gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] at h
      linear_combination h
  · rintro ⟨x, y, z, hxyz, hzero⟩
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro hv
      have hx : x = 0 := by simpa using congrFun hv 0
      have hy : y = 0 := by simpa using congrFun hv 1
      have hz : z = 0 := by simpa using congrFun hv 2
      exact hxyz.elim (· hx) fun hyz => hyz.elim (· hy) (· hz)
    · simp [PositiveDefiniteIntegralLattice.gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
      linear_combination hzero

/-- A nondegenerate isotropic real diagonal ternary form has both a positive
and a negative coefficient. -/
theorem mixed_signs_of_real_ternaryDiagonal_gramIsotropic
    {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![a, b, c])) :
    (0 < a ∨ 0 < b ∨ 0 < c) ∧ (a < 0 ∨ b < 0 ∨ c < 0) := by
  obtain ⟨x, y, z, hxyz, hzero⟩ :=
    (ternaryDiagonal_gramIsotropic_iff_exists_coordinates a b c).mp hiso
  constructor
  · by_contra hpos
    push_neg at hpos
    have haNeg : a < 0 := lt_of_le_of_ne hpos.1 ha
    have hbNeg : b < 0 := lt_of_le_of_ne hpos.2.1 hb
    have hcNeg : c < 0 := lt_of_le_of_ne hpos.2.2 hc
    rcases hxyz with hx | hy | hz
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y, sq_nonneg z]
    · nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy, sq_nonneg z]
    · nlinarith [sq_nonneg x, sq_nonneg y, sq_pos_of_ne_zero hz]
  · by_contra hneg
    push_neg at hneg
    have haPos : 0 < a := lt_of_le_of_ne hneg.1 (Ne.symm ha)
    have hbPos : 0 < b := lt_of_le_of_ne hneg.2.1 (Ne.symm hb)
    have hcPos : 0 < c := lt_of_le_of_ne hneg.2.2 (Ne.symm hc)
    rcases hxyz with hx | hy | hz
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y, sq_nonneg z]
    · nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy, sq_nonneg z]
    · nlinarith [sq_nonneg x, sq_nonneg y, sq_pos_of_ne_zero hz]

/-- Multiplying every coefficient of a diagonal ternary form by one nonzero
scalar preserves isotropy. -/
theorem ternaryDiagonal_gramIsotropic_mul_scalar_iff
    {K : Type*} [Field K] (a b c s : K) (hs : s ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![s * a, s * b, s * c]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) := by
  rw [ternaryDiagonal_gramIsotropic_iff_exists_coordinates,
    ternaryDiagonal_gramIsotropic_iff_exists_coordinates]
  constructor
  · rintro ⟨x, y, z, hxyz, hzero⟩
    refine ⟨x, y, z, hxyz, ?_⟩
    apply (mul_left_cancel₀ hs)
    linear_combination hzero
  · rintro ⟨x, y, z, hxyz, hzero⟩
    refine ⟨x, y, z, hxyz, ?_⟩
    linear_combination s * hzero

/-- Multiplying the first coefficient of a diagonal ternary form by a nonzero
square preserves isotropy. -/
theorem ternaryDiagonal_gramIsotropic_mul_sq_first_iff
    {K : Type*} [Field K] (a b c s : K) (hs : s ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![a * s ^ 2, b, c]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) := by
  rw [ternaryDiagonal_gramIsotropic_iff_exists_coordinates,
    ternaryDiagonal_gramIsotropic_iff_exists_coordinates]
  constructor
  · rintro ⟨x, y, z, hxyz, hzero⟩
    refine ⟨s * x, y, z, ?_, ?_⟩
    · exact hxyz.elim (fun hx => Or.inl (mul_ne_zero hs hx)) Or.inr
    · simpa [mul_pow, mul_assoc] using hzero
  · rintro ⟨x, y, z, hxyz, hzero⟩
    refine ⟨x / s, y, z, ?_, ?_⟩
    · exact hxyz.elim (fun hx => Or.inl (div_ne_zero hx hs)) Or.inr
    · rw [← hzero]
      field_simp

/-- Cyclically permuting a diagonal ternary form does not change its
isotropy. -/
theorem ternaryDiagonal_gramIsotropic_iff_cycle
    {K : Type*} [Field K] (a b c : K) :
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![b, c, a]) := by
  rw [ternaryDiagonal_gramIsotropic_iff_exists_coordinates,
    ternaryDiagonal_gramIsotropic_iff_exists_coordinates]
  constructor
  · rintro ⟨x, y, z, hxyz, hzero⟩
    refine ⟨y, z, x, ?_, ?_⟩
    · exact hxyz.elim (fun hx => Or.inr (Or.inr hx)) fun hyz =>
        hyz.elim Or.inl (fun hz => Or.inr (Or.inl hz))
    · linear_combination hzero
  · rintro ⟨y, z, x, hxyz, hzero⟩
    refine ⟨x, y, z, ?_, ?_⟩
    · exact hxyz.elim (fun hy => Or.inr (Or.inl hy)) fun hzx =>
        hzx.elim (fun hz => Or.inr (Or.inr hz)) Or.inl
    · linear_combination hzero

/-- The second cyclic permutation of a diagonal ternary form also preserves
isotropy. -/
theorem ternaryDiagonal_gramIsotropic_iff_cycle_two
    {K : Type*} [Field K] (a b c : K) :
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![c, a, b]) := by
  calc
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
        PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![b, c, a]) :=
      ternaryDiagonal_gramIsotropic_iff_cycle a b c
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![c, a, b]) :=
      ternaryDiagonal_gramIsotropic_iff_cycle b c a

/-- Multiplying the second coefficient of a diagonal ternary form by a
nonzero square preserves isotropy. -/
theorem ternaryDiagonal_gramIsotropic_mul_sq_second_iff
    {K : Type*} [Field K] (a b c s : K) (hs : s ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![a, b * s ^ 2, c]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) := by
  calc
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b * s ^ 2, c]) ↔
        PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![b * s ^ 2, c, a]) :=
      ternaryDiagonal_gramIsotropic_iff_cycle a (b * s ^ 2) c
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![b, c, a]) :=
      ternaryDiagonal_gramIsotropic_mul_sq_first_iff b c a s hs
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) :=
      (ternaryDiagonal_gramIsotropic_iff_cycle a b c).symm

/-- Multiplying the third coefficient of a diagonal ternary form by a nonzero
square preserves isotropy. -/
theorem ternaryDiagonal_gramIsotropic_mul_sq_third_iff
    {K : Type*} [Field K] (a b c s : K) (hs : s ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![a, b, c * s ^ 2]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) := by
  calc
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c * s ^ 2]) ↔
        PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![c * s ^ 2, a, b]) :=
      ternaryDiagonal_gramIsotropic_iff_cycle_two a b (c * s ^ 2)
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![c, a, b]) :=
      ternaryDiagonal_gramIsotropic_mul_sq_first_iff c a b s hs
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) :=
      (ternaryDiagonal_gramIsotropic_iff_cycle_two a b c).symm

/-- Multiplying all three coefficients of a diagonal ternary form by nonzero
squares preserves isotropy. -/
theorem ternaryDiagonal_gramIsotropic_mul_sq_each_iff
    {K : Type*} [Field K] (a b c sa sb sc : K)
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) (hsc : sc ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![a * sa ^ 2, b * sb ^ 2, c * sc ^ 2]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) := by
  calc
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![a * sa ^ 2, b * sb ^ 2, c * sc ^ 2]) ↔
        PositiveDefiniteIntegralLattice.GramIsotropic
          (Matrix.diagonal ![a, b * sb ^ 2, c * sc ^ 2]) :=
      ternaryDiagonal_gramIsotropic_mul_sq_first_iff
        a (b * sb ^ 2) (c * sc ^ 2) sa hsa
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic
          (Matrix.diagonal ![a, b, c * sc ^ 2]) :=
      ternaryDiagonal_gramIsotropic_mul_sq_second_iff
        a b (c * sc ^ 2) sb hsb
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) :=
      ternaryDiagonal_gramIsotropic_mul_sq_third_iff a b c sc hsc

/-- Over any characteristic-zero field, a nonzero rational diagonal ternary
form is isotropic exactly when its three canonical signed squarefree
representatives form an isotropic diagonal. -/
theorem ternaryDiagonal_gramIsotropic_iff_signedSquarefreeIntegers
    {K : Type*} [Field K] [CharZero K]
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : K), (b : K), (c : K)]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal
          ![(hilbertSignedSquarefreeInteger a : K),
            (hilbertSignedSquarefreeInteger b : K),
            (hilbertSignedSquarefreeInteger c : K)]) := by
  let A : ℤ := hilbertSignedSquarefreeInteger a
  let B : ℤ := hilbertSignedSquarefreeInteger b
  let C : ℤ := hilbertSignedSquarefreeInteger c
  let sa : ℚ := (hilbertSquareClassRootPart a : ℚ) / a.den
  let sb : ℚ := (hilbertSquareClassRootPart b : ℚ) / b.den
  let sc : ℚ := (hilbertSquareClassRootPart c : ℚ) / c.den
  have haeqQ : a = (A : ℚ) * sa ^ 2 :=
    eq_signedSquarefreeInteger_mul_rootPart_div_den_sq ha
  have hbeqQ : b = (B : ℚ) * sb ^ 2 :=
    eq_signedSquarefreeInteger_mul_rootPart_div_den_sq hb
  have hceqQ : c = (C : ℚ) * sc ^ 2 :=
    eq_signedSquarefreeInteger_mul_rootPart_div_den_sq hc
  have hsaQ : sa ≠ 0 := hilbertSquareClassRootPart_div_den_ne_zero ha
  have hsbQ : sb ≠ 0 := hilbertSquareClassRootPart_div_den_ne_zero hb
  have hscQ : sc ≠ 0 := hilbertSquareClassRootPart_div_den_ne_zero hc
  have haeq : (a : K) = (A : K) * (sa : K) ^ 2 := by exact_mod_cast haeqQ
  have hbeq : (b : K) = (B : K) * (sb : K) ^ 2 := by exact_mod_cast hbeqQ
  have hceq : (c : K) = (C : K) * (sc : K) ^ 2 := by exact_mod_cast hceqQ
  have hsa : (sa : K) ≠ 0 := by exact_mod_cast hsaQ
  have hsb : (sb : K) ≠ 0 := by exact_mod_cast hsbQ
  have hsc : (sc : K) ≠ 0 := by exact_mod_cast hscQ
  calc
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : K), (b : K), (c : K)]) ↔
        PositiveDefiniteIntegralLattice.GramIsotropic
          (Matrix.diagonal
            ![(A : K) * (sa : K) ^ 2, (B : K) * (sb : K) ^ 2,
              (C : K) * (sc : K) ^ 2]) := by
      rw [haeq, hbeq, hceq]
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(A : K), (B : K), (C : K)]) :=
      ternaryDiagonal_gramIsotropic_mul_sq_each_iff
        (A : K) (B : K) (C : K) (sa : K) (sb : K) (sc : K) hsa hsb hsc

/-- The distinct primes that divide at least two members of a natural triple. -/
def ternaryRepeatedPrimeSupport (m n k : ℕ) : Finset ℕ :=
  (m * n * k).primeFactors.filter fun p =>
    (p ∣ m ∧ p ∣ n) ∨ (p ∣ m ∧ p ∣ k) ∨
      (p ∣ n ∧ p ∣ k)

/-- The squarefree product of the primes that divide at least two members of a
natural triple. -/
def ternaryRepeatedPrimeKernel (m n k : ℕ) : ℕ :=
  ∏ p ∈ ternaryRepeatedPrimeSupport m n k, p

theorem ternaryRepeatedPrimeKernel_squarefree (m n k : ℕ) :
    Squarefree (ternaryRepeatedPrimeKernel m n k) := by
  unfold ternaryRepeatedPrimeKernel
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    apply (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).2
    exact hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hp).1).prime.squarefree

theorem ternaryRepeatedPrimeKernel_ne_zero (m n k : ℕ) :
    ternaryRepeatedPrimeKernel m n k ≠ 0 :=
  (ternaryRepeatedPrimeKernel_squarefree m n k).ne_zero

/-- For a nonzero natural triple, the repeated-prime kernel has exactly the
prime divisors occurring in at least two members. -/
theorem prime_dvd_ternaryRepeatedPrimeKernel_iff
    {m n k p : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    p ∣ ternaryRepeatedPrimeKernel m n k ↔
      (p ∣ m ∧ p ∣ n) ∨ (p ∣ m ∧ p ∣ k) ∨
        (p ∣ n ∧ p ∣ k) := by
  have hsupportPrime : ∀ q ∈ ternaryRepeatedPrimeSupport m n k, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hdvd_iff : p ∣ ternaryRepeatedPrimeKernel m n k ↔
      p ∈ (ternaryRepeatedPrimeKernel m n k).primeFactors := by
    rw [Nat.mem_primeFactors_of_ne_zero
      (ternaryRepeatedPrimeKernel_ne_zero m n k)]
    exact ⟨fun h ↦ ⟨hp, h⟩, And.right⟩
  rw [hdvd_iff]
  change p ∈ (∏ q ∈ ternaryRepeatedPrimeSupport m n k, q).primeFactors ↔ _
  rw [Nat.primeFactors_prod hsupportPrime]
  constructor
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro hcond
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcond⟩
    apply hp.mem_primeFactors
    · rcases hcond with hmn | hmk | hnk
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hmn.1 n) k
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hmk.1 n) k
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hnk.1 m) k
    · exact mul_ne_zero (mul_ne_zero hm hn) hk

/-- The squarefree symmetric difference of two squarefree naturals, expressed
by removing their common gcd from both sides. -/
def ternaryToggleSquarefree (r m : ℕ) : ℕ :=
  (r / r.gcd m) * (m / r.gcd m)

theorem ternaryToggleSquarefree_squarefree
    {r m : ℕ} (hr : Squarefree r) (hm : Squarefree m) :
    Squarefree (ternaryToggleSquarefree r m) := by
  have hleftDvd : r / r.gcd m ∣ r :=
    ⟨r.gcd m, (Nat.div_mul_cancel (Nat.gcd_dvd_left r m)).symm⟩
  have hrightDvd : m / r.gcd m ∣ m :=
    ⟨r.gcd m, (Nat.div_mul_cancel (Nat.gcd_dvd_right r m)).symm⟩
  have hcop : (r / r.gcd m).Coprime (m / r.gcd m) :=
    (Nat.coprime_div_gcd_of_squarefree hr hm.ne_zero).of_dvd_right hrightDvd
  exact (Nat.squarefree_mul hcop).2
    ⟨hr.squarefree_of_dvd hleftDvd, hm.squarefree_of_dvd hrightDvd⟩

/-- Multiplying two naturals is their gcd-toggle times the square of their
gcd. -/
theorem mul_eq_ternaryToggleSquarefree_mul_gcd_sq {r m : ℕ} :
    r * m = ternaryToggleSquarefree r m * r.gcd m ^ 2 := by
  calc
    r * m = ((r / r.gcd m) * r.gcd m) *
        ((m / r.gcd m) * r.gcd m) := by
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left r m),
        Nat.div_mul_cancel (Nat.gcd_dvd_right r m)]
    _ = ternaryToggleSquarefree r m * r.gcd m ^ 2 := by
      simp only [ternaryToggleSquarefree]
      ring

/-- A prime divides the squarefree gcd-toggle exactly when it divides one,
but not both, of the two squarefree inputs. -/
theorem prime_dvd_ternaryToggleSquarefree_iff
    {r m p : ℕ} (hp : p.Prime) (hr : Squarefree r) (hm : Squarefree m) :
    p ∣ ternaryToggleSquarefree r m ↔
      (p ∣ r ∧ ¬p ∣ m) ∨ (¬p ∣ r ∧ p ∣ m) := by
  have hleft0 : r / r.gcd m ≠ 0 := by
    intro hzero
    have hcancel := Nat.div_mul_cancel (Nat.gcd_dvd_left r m)
    rw [hzero, zero_mul] at hcancel
    exact hr.ne_zero hcancel.symm
  have hright0 : m / r.gcd m ≠ 0 := by
    intro hzero
    have hcancel := Nat.div_mul_cancel (Nat.gcd_dvd_right r m)
    rw [hzero, zero_mul] at hcancel
    exact hm.ne_zero hcancel.symm
  have hleft : p ∣ r / r.gcd m ↔ p ∣ r ∧ ¬p ∣ m := by
    constructor
    · intro hpd
      have hmem : p ∈ (r / r.gcd m).primeFactors :=
        hp.mem_primeFactors hpd hleft0
      rw [Nat.primeFactors_div_gcd hr hm.ne_zero] at hmem
      exact ⟨Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hmem).1,
        fun hpm ↦ (Finset.mem_sdiff.mp hmem).2
          (hp.mem_primeFactors hpm hm.ne_zero)⟩
    · rintro ⟨hpr, hnpm⟩
      apply Nat.dvd_of_mem_primeFactors
      rw [Nat.primeFactors_div_gcd hr hm.ne_zero]
      exact Finset.mem_sdiff.mpr
        ⟨hp.mem_primeFactors hpr hr.ne_zero,
          fun hmem ↦ hnpm (Nat.dvd_of_mem_primeFactors hmem)⟩
  have hright : p ∣ m / r.gcd m ↔ ¬p ∣ r ∧ p ∣ m := by
    have hpf : (m / r.gcd m).primeFactors =
        m.primeFactors \ r.primeFactors := by
      simpa [Nat.gcd_comm] using Nat.primeFactors_div_gcd hm hr.ne_zero
    constructor
    · intro hpd
      have hmem : p ∈ (m / r.gcd m).primeFactors :=
        hp.mem_primeFactors hpd hright0
      rw [hpf] at hmem
      exact ⟨fun hpr ↦ (Finset.mem_sdiff.mp hmem).2
          (hp.mem_primeFactors hpr hr.ne_zero),
        Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hmem).1⟩
    · rintro ⟨hnpr, hpm⟩
      apply Nat.dvd_of_mem_primeFactors
      rw [hpf]
      exact Finset.mem_sdiff.mpr
        ⟨hp.mem_primeFactors hpm hm.ne_zero,
          fun hmem ↦ hnpr (Nat.dvd_of_mem_primeFactors hmem)⟩
  unfold ternaryToggleSquarefree
  rw [hp.dvd_mul, hleft, hright]

/-- The first coefficient obtained by toggling all repeated primes in a
natural triple. -/
def ternaryPairwiseCoefficientFirst (m n k : ℕ) : ℕ :=
  ternaryToggleSquarefree (ternaryRepeatedPrimeKernel m n k) m

/-- The second coefficient obtained by toggling all repeated primes in a
natural triple. -/
def ternaryPairwiseCoefficientSecond (m n k : ℕ) : ℕ :=
  ternaryToggleSquarefree (ternaryRepeatedPrimeKernel m n k) n

/-- The third coefficient obtained by toggling all repeated primes in a
natural triple. -/
def ternaryPairwiseCoefficientThird (m n k : ℕ) : ℕ :=
  ternaryToggleSquarefree (ternaryRepeatedPrimeKernel m n k) k

/-- Each repeated-kernel product is its toggled coefficient times the removed
gcd square. -/
theorem ternaryPairwiseCoefficient_mul_gcd_sq (m n k : ℕ) :
    ternaryRepeatedPrimeKernel m n k * m =
        ternaryPairwiseCoefficientFirst m n k *
          (ternaryRepeatedPrimeKernel m n k).gcd m ^ 2 ∧
      ternaryRepeatedPrimeKernel m n k * n =
        ternaryPairwiseCoefficientSecond m n k *
          (ternaryRepeatedPrimeKernel m n k).gcd n ^ 2 ∧
      ternaryRepeatedPrimeKernel m n k * k =
        ternaryPairwiseCoefficientThird m n k *
          (ternaryRepeatedPrimeKernel m n k).gcd k ^ 2 := by
  exact ⟨mul_eq_ternaryToggleSquarefree_mul_gcd_sq,
    mul_eq_ternaryToggleSquarefree_mul_gcd_sq,
    mul_eq_ternaryToggleSquarefree_mul_gcd_sq⟩

/-- Toggling the repeated-prime kernel against three squarefree coefficients
produces nonzero squarefree pairwise-coprime coefficients. -/
theorem ternaryPairwiseCoefficients_properties
    {m n k : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hk : Squarefree k) :
    (ternaryPairwiseCoefficientFirst m n k ≠ 0 ∧
        Squarefree (ternaryPairwiseCoefficientFirst m n k)) ∧
      (ternaryPairwiseCoefficientSecond m n k ≠ 0 ∧
        Squarefree (ternaryPairwiseCoefficientSecond m n k)) ∧
      (ternaryPairwiseCoefficientThird m n k ≠ 0 ∧
        Squarefree (ternaryPairwiseCoefficientThird m n k)) ∧
      ((ternaryPairwiseCoefficientFirst m n k).Coprime
          (ternaryPairwiseCoefficientSecond m n k) ∧
        (ternaryPairwiseCoefficientFirst m n k).Coprime
          (ternaryPairwiseCoefficientThird m n k) ∧
        (ternaryPairwiseCoefficientSecond m n k).Coprime
          (ternaryPairwiseCoefficientThird m n k)) := by
  let r := ternaryRepeatedPrimeKernel m n k
  have hr : Squarefree r := ternaryRepeatedPrimeKernel_squarefree m n k
  have hfirst : Squarefree (ternaryPairwiseCoefficientFirst m n k) :=
    ternaryToggleSquarefree_squarefree hr hm
  have hsecond : Squarefree (ternaryPairwiseCoefficientSecond m n k) :=
    ternaryToggleSquarefree_squarefree hr hn
  have hthird : Squarefree (ternaryPairwiseCoefficientThird m n k) :=
    ternaryToggleSquarefree_squarefree hr hk
  have hmn : (ternaryPairwiseCoefficientFirst m n k).Coprime
      (ternaryPairwiseCoefficientSecond m n k) := by
    apply Nat.coprime_of_dvd
    intro p hp hpf hps
    have hpr := (prime_dvd_ternaryRepeatedPrimeKernel_iff
      hp hm.ne_zero hn.ne_zero hk.ne_zero)
    have hpf' := (prime_dvd_ternaryToggleSquarefree_iff hp hr hm).mp hpf
    have hps' := (prime_dvd_ternaryToggleSquarefree_iff hp hr hn).mp hps
    tauto
  have hmk : (ternaryPairwiseCoefficientFirst m n k).Coprime
      (ternaryPairwiseCoefficientThird m n k) := by
    apply Nat.coprime_of_dvd
    intro p hp hpf hpt
    have hpr := (prime_dvd_ternaryRepeatedPrimeKernel_iff
      hp hm.ne_zero hn.ne_zero hk.ne_zero)
    have hpf' := (prime_dvd_ternaryToggleSquarefree_iff hp hr hm).mp hpf
    have hpt' := (prime_dvd_ternaryToggleSquarefree_iff hp hr hk).mp hpt
    tauto
  have hnk : (ternaryPairwiseCoefficientSecond m n k).Coprime
      (ternaryPairwiseCoefficientThird m n k) := by
    apply Nat.coprime_of_dvd
    intro p hp hps hpt
    have hpr := (prime_dvd_ternaryRepeatedPrimeKernel_iff
      hp hm.ne_zero hn.ne_zero hk.ne_zero)
    have hps' := (prime_dvd_ternaryToggleSquarefree_iff hp hr hn).mp hps
    have hpt' := (prime_dvd_ternaryToggleSquarefree_iff hp hr hk).mp hpt
    tauto
  exact ⟨⟨hfirst.ne_zero, hfirst⟩, ⟨hsecond.ne_zero, hsecond⟩,
    ⟨hthird.ne_zero, hthird⟩, ⟨hmn, hmk, hnk⟩⟩

/-- The first pairwise-normalized coefficient with the sign of the original
integer coefficient attached. -/
def ternaryPairwiseSignedCoefficientFirst (a b c : ℤ) : ℤ :=
  a.sign * ternaryPairwiseCoefficientFirst a.natAbs b.natAbs c.natAbs

/-- The second pairwise-normalized coefficient with the sign of the original
integer coefficient attached. -/
def ternaryPairwiseSignedCoefficientSecond (a b c : ℤ) : ℤ :=
  b.sign * ternaryPairwiseCoefficientSecond a.natAbs b.natAbs c.natAbs

/-- The third pairwise-normalized coefficient with the sign of the original
integer coefficient attached. -/
def ternaryPairwiseSignedCoefficientThird (a b c : ℤ) : ℤ :=
  c.sign * ternaryPairwiseCoefficientThird a.natAbs b.natAbs c.natAbs

theorem natAbs_ternaryPairwiseSignedCoefficientFirst
    {a b c : ℤ} (ha : a ≠ 0) :
    (ternaryPairwiseSignedCoefficientFirst a b c).natAbs =
      ternaryPairwiseCoefficientFirst a.natAbs b.natAbs c.natAbs := by
  simp only [ternaryPairwiseSignedCoefficientFirst, Int.natAbs_mul,
    Int.natAbs_natCast]
  rw [Int.natAbs_sign_of_ne_zero ha]
  simp

theorem natAbs_ternaryPairwiseSignedCoefficientSecond
    {a b c : ℤ} (hb : b ≠ 0) :
    (ternaryPairwiseSignedCoefficientSecond a b c).natAbs =
      ternaryPairwiseCoefficientSecond a.natAbs b.natAbs c.natAbs := by
  simp only [ternaryPairwiseSignedCoefficientSecond, Int.natAbs_mul,
    Int.natAbs_natCast]
  rw [Int.natAbs_sign_of_ne_zero hb]
  simp

theorem natAbs_ternaryPairwiseSignedCoefficientThird
    {a b c : ℤ} (hc : c ≠ 0) :
    (ternaryPairwiseSignedCoefficientThird a b c).natAbs =
      ternaryPairwiseCoefficientThird a.natAbs b.natAbs c.natAbs := by
  simp only [ternaryPairwiseSignedCoefficientThird, Int.natAbs_mul,
    Int.natAbs_natCast]
  rw [Int.natAbs_sign_of_ne_zero hc]
  simp

/-- Signed pairwise normalization preserves nonvanishing and squarefreeness
and produces pairwise-coprime absolute coefficients. -/
theorem ternaryPairwiseSignedCoefficients_properties
    {a b c : ℤ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (ha : Squarefree a.natAbs) (hb : Squarefree b.natAbs)
    (hc : Squarefree c.natAbs) :
    (ternaryPairwiseSignedCoefficientFirst a b c ≠ 0 ∧
        Squarefree (ternaryPairwiseSignedCoefficientFirst a b c).natAbs) ∧
      (ternaryPairwiseSignedCoefficientSecond a b c ≠ 0 ∧
        Squarefree (ternaryPairwiseSignedCoefficientSecond a b c).natAbs) ∧
      (ternaryPairwiseSignedCoefficientThird a b c ≠ 0 ∧
        Squarefree (ternaryPairwiseSignedCoefficientThird a b c).natAbs) ∧
      ((ternaryPairwiseSignedCoefficientFirst a b c).natAbs.Coprime
          (ternaryPairwiseSignedCoefficientSecond a b c).natAbs ∧
        (ternaryPairwiseSignedCoefficientFirst a b c).natAbs.Coprime
          (ternaryPairwiseSignedCoefficientThird a b c).natAbs ∧
        (ternaryPairwiseSignedCoefficientSecond a b c).natAbs.Coprime
          (ternaryPairwiseSignedCoefficientThird a b c).natAbs) := by
  obtain ⟨⟨hA0, hAsq⟩, ⟨hB0, hBsq⟩, ⟨hC0, hCsq⟩, hAB, hAC, hBC⟩ :=
    ternaryPairwiseCoefficients_properties ha hb hc
  have hA := natAbs_ternaryPairwiseSignedCoefficientFirst
    (b := b) (c := c) ha0
  have hB := natAbs_ternaryPairwiseSignedCoefficientSecond
    (a := a) (c := c) hb0
  have hC := natAbs_ternaryPairwiseSignedCoefficientThird
    (a := a) (b := b) hc0
  constructor
  · exact ⟨Int.natAbs_ne_zero.mp (hA.symm ▸ hA0), hA.symm ▸ hAsq⟩
  constructor
  · exact ⟨Int.natAbs_ne_zero.mp (hB.symm ▸ hB0), hB.symm ▸ hBsq⟩
  constructor
  · exact ⟨Int.natAbs_ne_zero.mp (hC.symm ▸ hC0), hC.symm ▸ hCsq⟩
  · exact ⟨hA.symm ▸ hB.symm ▸ hAB, hA.symm ▸ hC.symm ▸ hAC,
      hB.symm ▸ hC.symm ▸ hBC⟩

/-- Signed pairwise normalization preserves each coefficient's sign. -/
theorem ternaryPairwiseSignedCoefficients_signs
    {a b c : ℤ} (ha : Squarefree a.natAbs) (hb : Squarefree b.natAbs)
    (hc : Squarefree c.natAbs) :
    (ternaryPairwiseSignedCoefficientFirst a b c).sign = a.sign ∧
      (ternaryPairwiseSignedCoefficientSecond a b c).sign = b.sign ∧
      (ternaryPairwiseSignedCoefficientThird a b c).sign = c.sign := by
  obtain ⟨⟨hA0, _⟩, ⟨hB0, _⟩, ⟨hC0, _⟩, _⟩ :=
    ternaryPairwiseCoefficients_properties ha hb hc
  have hApos : (0 : ℤ) < ternaryPairwiseCoefficientFirst
      a.natAbs b.natAbs c.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hA0
  have hBpos : (0 : ℤ) < ternaryPairwiseCoefficientSecond
      a.natAbs b.natAbs c.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hB0
  have hCpos : (0 : ℤ) < ternaryPairwiseCoefficientThird
      a.natAbs b.natAbs c.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hC0
  constructor
  · rw [ternaryPairwiseSignedCoefficientFirst, Int.sign_mul,
      Int.sign_eq_one_of_pos hApos]
    simp
  constructor
  · rw [ternaryPairwiseSignedCoefficientSecond, Int.sign_mul,
      Int.sign_eq_one_of_pos hBpos]
    simp
  · rw [ternaryPairwiseSignedCoefficientThird, Int.sign_mul,
      Int.sign_eq_one_of_pos hCpos]
    simp

/-- In particular, signed pairwise normalization preserves the existence of
both a positive and a negative coefficient. -/
theorem ternaryPairwiseSignedCoefficients_mixed_signs
    {a b c : ℤ} (ha : Squarefree a.natAbs) (hb : Squarefree b.natAbs)
    (hc : Squarefree c.natAbs)
    (hpos : 0 < a ∨ 0 < b ∨ 0 < c)
    (hneg : a < 0 ∨ b < 0 ∨ c < 0) :
    (0 < ternaryPairwiseSignedCoefficientFirst a b c ∨
        0 < ternaryPairwiseSignedCoefficientSecond a b c ∨
        0 < ternaryPairwiseSignedCoefficientThird a b c) ∧
      (ternaryPairwiseSignedCoefficientFirst a b c < 0 ∨
        ternaryPairwiseSignedCoefficientSecond a b c < 0 ∨
        ternaryPairwiseSignedCoefficientThird a b c < 0) := by
  obtain ⟨hA, hB, hC⟩ := ternaryPairwiseSignedCoefficients_signs ha hb hc
  constructor
  · rcases hpos with haPos | hbPos | hcPos
    · left
      apply Int.sign_eq_one_iff_pos.mp
      rw [hA, Int.sign_eq_one_of_pos haPos]
    · right; left
      apply Int.sign_eq_one_iff_pos.mp
      rw [hB, Int.sign_eq_one_of_pos hbPos]
    · right; right
      apply Int.sign_eq_one_iff_pos.mp
      rw [hC, Int.sign_eq_one_of_pos hcPos]
  · rcases hneg with haNeg | hbNeg | hcNeg
    · left
      apply Int.sign_eq_neg_one_iff_neg.mp
      rw [hA, Int.sign_eq_neg_one_of_neg haNeg]
    · right; left
      apply Int.sign_eq_neg_one_iff_neg.mp
      rw [hB, Int.sign_eq_neg_one_of_neg hbNeg]
    · right; right
      apply Int.sign_eq_neg_one_iff_neg.mp
      rw [hC, Int.sign_eq_neg_one_of_neg hcNeg]

/-- The common repeated-prime scalar times each signed coefficient is its
signed pairwise normalization times the corresponding removed gcd square. -/
theorem ternaryPairwiseSignedCoefficient_mul_gcd_sq (a b c : ℤ) :
    (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) * a =
        ternaryPairwiseSignedCoefficientFirst a b c *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            a.natAbs : ℤ) ^ 2 ∧
      (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) * b =
        ternaryPairwiseSignedCoefficientSecond a b c *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            b.natAbs : ℤ) ^ 2 ∧
      (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) * c =
        ternaryPairwiseSignedCoefficientThird a b c *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            c.natAbs : ℤ) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ :=
    ternaryPairwiseCoefficient_mul_gcd_sq a.natAbs b.natAbs c.natAbs
  have ha' : (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
      (a.natAbs : ℤ) =
        (ternaryPairwiseCoefficientFirst a.natAbs b.natAbs c.natAbs : ℤ) *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            a.natAbs : ℤ) ^ 2 := by exact_mod_cast ha
  have hb' : (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
      (b.natAbs : ℤ) =
        (ternaryPairwiseCoefficientSecond a.natAbs b.natAbs c.natAbs : ℤ) *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            b.natAbs : ℤ) ^ 2 := by exact_mod_cast hb
  have hc' : (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
      (c.natAbs : ℤ) =
        (ternaryPairwiseCoefficientThird a.natAbs b.natAbs c.natAbs : ℤ) *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            c.natAbs : ℤ) ^ 2 := by exact_mod_cast hc
  constructor
  · calc
      _ = (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
          (a.sign * (a.natAbs : ℤ)) := congrArg
            (fun t : ℤ ↦
              (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) * t)
            (Int.sign_mul_natAbs a).symm
      _ = a.sign * ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
          (a.natAbs : ℤ)) := by ring
      _ = a.sign * ((ternaryPairwiseCoefficientFirst a.natAbs b.natAbs c.natAbs : ℤ) *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            a.natAbs : ℤ) ^ 2) := by rw [ha']
      _ = _ := by simp [ternaryPairwiseSignedCoefficientFirst]; ring
  constructor
  · calc
      _ = (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
          (b.sign * (b.natAbs : ℤ)) := congrArg
            (fun t : ℤ ↦
              (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) * t)
            (Int.sign_mul_natAbs b).symm
      _ = b.sign * ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
          (b.natAbs : ℤ)) := by ring
      _ = b.sign * ((ternaryPairwiseCoefficientSecond a.natAbs b.natAbs c.natAbs : ℤ) *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            b.natAbs : ℤ) ^ 2) := by rw [hb']
      _ = _ := by simp [ternaryPairwiseSignedCoefficientSecond]; ring
  · calc
      _ = (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
          (c.sign * (c.natAbs : ℤ)) := congrArg
            (fun t : ℤ ↦
              (ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) * t)
            (Int.sign_mul_natAbs c).symm
      _ = c.sign * ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs : ℤ) *
          (c.natAbs : ℤ)) := by ring
      _ = c.sign * ((ternaryPairwiseCoefficientThird a.natAbs b.natAbs c.natAbs : ℤ) *
          ((ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs).gcd
            c.natAbs : ℤ) ^ 2) := by rw [hc']
      _ = _ := by simp [ternaryPairwiseSignedCoefficientThird]; ring

/-- Signed repeated-prime normalization preserves diagonal ternary isotropy
over every characteristic-zero field. -/
theorem ternaryDiagonal_gramIsotropic_iff_pairwiseSignedCoefficients
    {K : Type*} [Field K] [CharZero K] (a b c : ℤ) :
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : K), (b : K), (c : K)]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal
          ![(ternaryPairwiseSignedCoefficientFirst a b c : K),
            (ternaryPairwiseSignedCoefficientSecond a b c : K),
            (ternaryPairwiseSignedCoefficientThird a b c : K)]) := by
  let r := ternaryRepeatedPrimeKernel a.natAbs b.natAbs c.natAbs
  have hr : (r : K) ≠ 0 := by
    exact_mod_cast ternaryRepeatedPrimeKernel_ne_zero a.natAbs b.natAbs c.natAbs
  have hga : (r.gcd a.natAbs : K) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left a.natAbs (Nat.pos_of_ne_zero
      (ternaryRepeatedPrimeKernel_ne_zero a.natAbs b.natAbs c.natAbs))).ne'
  have hgb : (r.gcd b.natAbs : K) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left b.natAbs (Nat.pos_of_ne_zero
      (ternaryRepeatedPrimeKernel_ne_zero a.natAbs b.natAbs c.natAbs))).ne'
  have hgc : (r.gcd c.natAbs : K) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left c.natAbs (Nat.pos_of_ne_zero
      (ternaryRepeatedPrimeKernel_ne_zero a.natAbs b.natAbs c.natAbs))).ne'
  obtain ⟨ha, hb, hc⟩ := ternaryPairwiseSignedCoefficient_mul_gcd_sq a b c
  have ha' : (r : K) * (a : K) =
      (ternaryPairwiseSignedCoefficientFirst a b c : K) *
        (r.gcd a.natAbs : K) ^ 2 := by exact_mod_cast ha
  have hb' : (r : K) * (b : K) =
      (ternaryPairwiseSignedCoefficientSecond a b c : K) *
        (r.gcd b.natAbs : K) ^ 2 := by exact_mod_cast hb
  have hc' : (r : K) * (c : K) =
      (ternaryPairwiseSignedCoefficientThird a b c : K) *
        (r.gcd c.natAbs : K) ^ 2 := by exact_mod_cast hc
  calc
    PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : K), (b : K), (c : K)]) ↔
        PositiveDefiniteIntegralLattice.GramIsotropic
          (Matrix.diagonal ![(r : K) * a, (r : K) * b, (r : K) * c]) :=
      (ternaryDiagonal_gramIsotropic_mul_scalar_iff
        (a : K) (b : K) (c : K) r hr).symm
    _ ↔ PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal
          ![(ternaryPairwiseSignedCoefficientFirst a b c : K),
            (ternaryPairwiseSignedCoefficientSecond a b c : K),
            (ternaryPairwiseSignedCoefficientThird a b c : K)]) := by
      rw [ha', hb', hc']
      exact ternaryDiagonal_gramIsotropic_mul_sq_each_iff
        (ternaryPairwiseSignedCoefficientFirst a b c : K)
        (ternaryPairwiseSignedCoefficientSecond a b c : K)
        (ternaryPairwiseSignedCoefficientThird a b c : K)
        (r.gcd a.natAbs) (r.gcd b.natAbs) (r.gcd c.natAbs) hga hgb hgc

/-- The first final pairwise-normalized integer attached to a rational
coefficient triple. -/
def ternaryPairwiseSignedSquarefreeIntegerFirst (a b c : ℚ) : ℤ :=
  ternaryPairwiseSignedCoefficientFirst
    (hilbertSignedSquarefreeInteger a) (hilbertSignedSquarefreeInteger b)
    (hilbertSignedSquarefreeInteger c)

/-- The second final pairwise-normalized integer attached to a rational
coefficient triple. -/
def ternaryPairwiseSignedSquarefreeIntegerSecond (a b c : ℚ) : ℤ :=
  ternaryPairwiseSignedCoefficientSecond
    (hilbertSignedSquarefreeInteger a) (hilbertSignedSquarefreeInteger b)
    (hilbertSignedSquarefreeInteger c)

/-- The third final pairwise-normalized integer attached to a rational
coefficient triple. -/
def ternaryPairwiseSignedSquarefreeIntegerThird (a b c : ℚ) : ℤ :=
  ternaryPairwiseSignedCoefficientThird
    (hilbertSignedSquarefreeInteger a) (hilbertSignedSquarefreeInteger b)
    (hilbertSignedSquarefreeInteger c)

/-- The final integer coefficients attached to a nonzero rational triple are
nonzero, squarefree, and pairwise coprime in absolute value. -/
theorem ternaryPairwiseSignedSquarefreeIntegers_properties
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (ternaryPairwiseSignedSquarefreeIntegerFirst a b c ≠ 0 ∧
        Squarefree (ternaryPairwiseSignedSquarefreeIntegerFirst a b c).natAbs) ∧
      (ternaryPairwiseSignedSquarefreeIntegerSecond a b c ≠ 0 ∧
        Squarefree (ternaryPairwiseSignedSquarefreeIntegerSecond a b c).natAbs) ∧
      (ternaryPairwiseSignedSquarefreeIntegerThird a b c ≠ 0 ∧
        Squarefree (ternaryPairwiseSignedSquarefreeIntegerThird a b c).natAbs) ∧
      ((ternaryPairwiseSignedSquarefreeIntegerFirst a b c).natAbs.Coprime
          (ternaryPairwiseSignedSquarefreeIntegerSecond a b c).natAbs ∧
        (ternaryPairwiseSignedSquarefreeIntegerFirst a b c).natAbs.Coprime
          (ternaryPairwiseSignedSquarefreeIntegerThird a b c).natAbs ∧
        (ternaryPairwiseSignedSquarefreeIntegerSecond a b c).natAbs.Coprime
          (ternaryPairwiseSignedSquarefreeIntegerThird a b c).natAbs) := by
  simpa [ternaryPairwiseSignedSquarefreeIntegerFirst,
    ternaryPairwiseSignedSquarefreeIntegerSecond,
    ternaryPairwiseSignedSquarefreeIntegerThird] using
    ternaryPairwiseSignedCoefficients_properties
      (hilbertSignedSquarefreeInteger_ne_zero ha)
      (hilbertSignedSquarefreeInteger_ne_zero hb)
      (hilbertSignedSquarefreeInteger_ne_zero hc)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree ha)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hb)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hc)

/-- Real isotropy of a nonzero rational diagonal forces mixed signs on its
final pairwise-normalized integer coefficients. -/
theorem ternaryPairwiseSignedSquarefreeIntegers_mixed_signs_of_real_gramIsotropic
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![(a : ℝ), (b : ℝ), (c : ℝ)])) :
    (0 < ternaryPairwiseSignedSquarefreeIntegerFirst a b c ∨
        0 < ternaryPairwiseSignedSquarefreeIntegerSecond a b c ∨
        0 < ternaryPairwiseSignedSquarefreeIntegerThird a b c) ∧
      (ternaryPairwiseSignedSquarefreeIntegerFirst a b c < 0 ∨
        ternaryPairwiseSignedSquarefreeIntegerSecond a b c < 0 ∨
        ternaryPairwiseSignedSquarefreeIntegerThird a b c < 0) := by
  let A := hilbertSignedSquarefreeInteger a
  let B := hilbertSignedSquarefreeInteger b
  let C := hilbertSignedSquarefreeInteger c
  have hA0 : A ≠ 0 := hilbertSignedSquarefreeInteger_ne_zero ha
  have hB0 : B ≠ 0 := hilbertSignedSquarefreeInteger_ne_zero hb
  have hC0 : C ≠ 0 := hilbertSignedSquarefreeInteger_ne_zero hc
  have hA0R : (A : ℝ) ≠ 0 := by exact_mod_cast hA0
  have hB0R : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
  have hC0R : (C : ℝ) ≠ 0 := by exact_mod_cast hC0
  have hcanonical : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![(A : ℝ), (B : ℝ), (C : ℝ)]) :=
    (ternaryDiagonal_gramIsotropic_iff_signedSquarefreeIntegers
      (K := ℝ) ha hb hc).mp hreal
  obtain ⟨hposR, hnegR⟩ :=
    mixed_signs_of_real_ternaryDiagonal_gramIsotropic
      hA0R hB0R hC0R hcanonical
  have hpos : 0 < A ∨ 0 < B ∨ 0 < C := by exact_mod_cast hposR
  have hneg : A < 0 ∨ B < 0 ∨ C < 0 := by exact_mod_cast hnegR
  simpa [A, B, C, ternaryPairwiseSignedSquarefreeIntegerFirst,
    ternaryPairwiseSignedSquarefreeIntegerSecond,
    ternaryPairwiseSignedSquarefreeIntegerThird] using
    ternaryPairwiseSignedCoefficients_mixed_signs
      (hilbertSignedSquarefreeInteger_natAbs_squarefree ha)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hb)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hc) hpos hneg

/-- A p-adic local-isotropy family for a nonzero rational diagonal transports
to its final signed squarefree pairwise-coprime integer coefficients. -/
theorem padic_gramIsotropic_pairwiseSignedSquarefreeIntegers
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])])) :
    ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal
          ![(ternaryPairwiseSignedSquarefreeIntegerFirst a b c : ℚ_[p]),
            (ternaryPairwiseSignedSquarefreeIntegerSecond a b c : ℚ_[p]),
            (ternaryPairwiseSignedSquarefreeIntegerThird a b c : ℚ_[p])]) := by
  intro p _
  apply (ternaryDiagonal_gramIsotropic_iff_pairwiseSignedCoefficients
    (K := ℚ_[p]) (hilbertSignedSquarefreeInteger a)
      (hilbertSignedSquarefreeInteger b)
      (hilbertSignedSquarefreeInteger c)).mp
  apply (ternaryDiagonal_gramIsotropic_iff_signedSquarefreeIntegers
    (K := ℚ_[p]) ha hb hc).mp
  exact hlocal p

/-- A family of nontrivial p-adic ternary zeros at the primes dividing a
squarefree coefficient gives its complete Legendre congruence root. -/
theorem isSquareModuloNatAbs_neg_mul_of_padic_ternary_zeros
    {a b c : ℤ} (hsa : Squarefree a.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime], p ∣ a.natAbs →
      ∃ x y z : ℚ_[p],
        (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
        (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 +
          (c : ℚ_[p]) * z ^ 2 = 0) :
    IsSquareModuloNatAbs (-(b * c)) a := by
  apply exists_int_sq_modEq_of_prime_roots_of_squarefree (-(b * c)) hsa
  intro p hp hpa
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, z, hnonzero, hzero⟩ := hlocal p hpa
  apply exists_int_sq_modEq_neg_mul_of_padic_ternary_zero hsa hpa
  · intro hpb
    have hpbNat : p ∣ b.natAbs := Int.natCast_dvd.mp hpb
    have hpbCop : p.Coprime b.natAbs := hab.of_dvd_left hpa
    exact hp.ne_one (hpbCop.eq_one_of_dvd hpbNat)
  · exact hnonzero
  · exact hzero

/-- A family of p-adic diagonal Gram-isotropy hypotheses at the primes
dividing a squarefree coefficient gives its complete Legendre congruence
root. -/
theorem isSquareModuloNatAbs_neg_mul_of_padic_gramIsotropic
    {a b c : ℤ} (hsa : Squarefree a.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime], p ∣ a.natAbs →
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])])) :
    IsSquareModuloNatAbs (-(b * c)) a := by
  apply isSquareModuloNatAbs_neg_mul_of_padic_ternary_zeros hsa hab
  intro p _ hpa
  exact (ternaryDiagonal_gramIsotropic_iff_exists_coordinates
    (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])).mp (hlocal p hpa)

/-- One family of p-adic diagonal Gram-isotropy hypotheses gives all three
Legendre congruence roots for squarefree pairwise-coprime coefficients. -/
theorem legendreCongruenceRoots_of_padic_gramIsotropic
    {a b c : ℤ}
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hca : c.natAbs.Coprime a.natAbs)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])])) :
    IsSquareModuloNatAbs (-(b * c)) a ∧
      IsSquareModuloNatAbs (-(c * a)) b ∧
      IsSquareModuloNatAbs (-(a * b)) c := by
  refine ⟨?_, ?_, ?_⟩
  · apply isSquareModuloNatAbs_neg_mul_of_padic_gramIsotropic hsa hab
    intro p _ _
    exact hlocal p
  · apply isSquareModuloNatAbs_neg_mul_of_padic_gramIsotropic hsb hbc
    intro p _ _
    exact (ternaryDiagonal_gramIsotropic_iff_cycle
      (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])).mp (hlocal p)
  · apply isSquareModuloNatAbs_neg_mul_of_padic_gramIsotropic hsc hca
    intro p _ _
    exact (ternaryDiagonal_gramIsotropic_iff_cycle_two
      (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p])).mp (hlocal p)

/-- The integral linear form used in Legendre's CRT construction. -/
def legendreLinearValue (A B C x y z : ℤ) : ℤ :=
  A * x + B * y + C * z

private abbrev legendreBox (X Y Z : ℕ) :=
  Fin (X + 1) × Fin (Y + 1) × Fin (Z + 1)

private def legendreBoxResidue (A B C : ℤ) (M X Y Z : ℕ)
    (p : legendreBox X Y Z) : ZMod M :=
  legendreLinearValue A B C p.1 p.2.1 p.2.2

/-- If a rectangular integer box has more points than a nonzero modulus, two
points have the same linear-form residue.  Their difference is a nonzero
integer triple with the stated coordinate bounds and divisible linear value. -/
theorem exists_bounded_nonzero_legendreLinearValue_dvd
    (A B C : ℤ) {M X Y Z : ℕ} (hM : M ≠ 0)
    (hcard : M < (X + 1) * (Y + 1) * (Z + 1)) :
    ∃ x y z : ℤ,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x.natAbs ≤ X ∧ y.natAbs ≤ Y ∧ z.natAbs ≤ Z ∧
      (M : ℤ) ∣ legendreLinearValue A B C x y z := by
  letI : NeZero M := ⟨hM⟩
  have hcard' : Fintype.card (ZMod M) <
      Fintype.card (legendreBox X Y Z) := by
    simpa [legendreBox, mul_assoc] using hcard
  obtain ⟨p, q, hpq, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (legendreBoxResidue A B C M X Y Z) hcard'
  let x : ℤ := p.1 - q.1
  let y : ℤ := p.2.1 - q.2.1
  let z : ℤ := p.2.2 - q.2.2
  refine ⟨x, y, z, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hzero
    simp only [not_or, not_not] at hzero
    apply hpq
    apply Prod.ext
    · apply Fin.ext
      have hx : (p.1.val : ℤ) = q.1.val := sub_eq_zero.mp hzero.1
      exact_mod_cast hx
    · apply Prod.ext
      · apply Fin.ext
        have hy : (p.2.1.val : ℤ) = q.2.1.val := sub_eq_zero.mp hzero.2.1
        exact_mod_cast hy
      · apply Fin.ext
        have hz : (p.2.2.val : ℤ) = q.2.2.val := sub_eq_zero.mp hzero.2.2
        exact_mod_cast hz
  · exact Int.natAbs_coe_sub_coe_le_of_le
      (Nat.lt_succ_iff.mp p.1.isLt) (Nat.lt_succ_iff.mp q.1.isLt)
  · exact Int.natAbs_coe_sub_coe_le_of_le
      (Nat.lt_succ_iff.mp p.2.1.isLt) (Nat.lt_succ_iff.mp q.2.1.isLt)
  · exact Int.natAbs_coe_sub_coe_le_of_le
      (Nat.lt_succ_iff.mp p.2.2.isLt) (Nat.lt_succ_iff.mp q.2.2.isLt)
  · have hmod : legendreLinearValue A B C p.1 p.2.1 p.2.2 ≡
        legendreLinearValue A B C q.1 q.2.1 q.2.2 [ZMOD M] :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mp heq
    have hdvd : (M : ℤ) ∣
        legendreLinearValue A B C p.1 p.2.1 p.2.2 -
          legendreLinearValue A B C q.1 q.2.1 q.2.2 := hmod.symm.dvd
    rw [show legendreLinearValue A B C x y z =
        legendreLinearValue A B C p.1 p.2.1 p.2.2 -
          legendreLinearValue A B C q.1 q.2.1 q.2.2 by
      simp only [x, y, z, legendreLinearValue]
      ring]
    exact hdvd

private def intNatResidue (r : ℤ) (m : ℕ) : ℕ :=
  (r % (m : ℤ)).toNat

private lemma intNatResidue_modEq (r : ℤ) {m : ℕ} (hm : m ≠ 0) :
    (intNatResidue r m : ℤ) ≡ r [ZMOD m] := by
  unfold intNatResidue
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm))]
  exact Int.mod_modEq r (m : ℤ)

private noncomputable def intChineseRemainderThree (m n k : ℕ)
    (hmn : m.Coprime n) (hmk : m.Coprime k) (hnk : n.Coprime k)
    (rm rn rk : ℤ) : ℤ :=
  let qmn := Nat.chineseRemainder hmn
    (intNatResidue rm m) (intNatResidue rn n)
  (Nat.chineseRemainder (hmk.mul_left hnk) qmn
    (intNatResidue rk k) : ℕ)

private lemma intChineseRemainderThree_mod_left (m n k : ℕ)
    (hm : m ≠ 0) (hmn : m.Coprime n) (hmk : m.Coprime k)
    (hnk : n.Coprime k) (rm rn rk : ℤ) :
    intChineseRemainderThree m n k hmn hmk hnk rm rn rk ≡ rm [ZMOD m] := by
  let qmn := Nat.chineseRemainder hmn
    (intNatResidue rm m) (intNatResidue rn n)
  have hout : (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k) : ℕ) ≡ qmn [MOD m * n] :=
    (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k)).prop.1
  have hleft : (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k) : ℕ) ≡ intNatResidue rm m [MOD m] :=
    (Nat.ModEq.of_dvd (dvd_mul_right m n) hout).trans qmn.prop.1
  exact (Int.natCast_modEq_iff.mpr hleft).trans (intNatResidue_modEq rm hm)

private lemma intChineseRemainderThree_mod_middle (m n k : ℕ)
    (hn : n ≠ 0) (hmn : m.Coprime n) (hmk : m.Coprime k)
    (hnk : n.Coprime k) (rm rn rk : ℤ) :
    intChineseRemainderThree m n k hmn hmk hnk rm rn rk ≡ rn [ZMOD n] := by
  let qmn := Nat.chineseRemainder hmn
    (intNatResidue rm m) (intNatResidue rn n)
  have hout : (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k) : ℕ) ≡ qmn [MOD m * n] :=
    (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k)).prop.1
  have hmiddle : (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k) : ℕ) ≡ intNatResidue rn n [MOD n] :=
    (Nat.ModEq.of_dvd (dvd_mul_left n m) hout).trans qmn.prop.2
  exact (Int.natCast_modEq_iff.mpr hmiddle).trans (intNatResidue_modEq rn hn)

private lemma intChineseRemainderThree_mod_right (m n k : ℕ)
    (hk : k ≠ 0) (hmn : m.Coprime n) (hmk : m.Coprime k)
    (hnk : n.Coprime k) (rm rn rk : ℤ) :
    intChineseRemainderThree m n k hmn hmk hnk rm rn rk ≡ rk [ZMOD k] := by
  let qmn := Nat.chineseRemainder hmn
    (intNatResidue rm m) (intNatResidue rn n)
  have hright : (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k) : ℕ) ≡ intNatResidue rk k [MOD k] :=
    (Nat.chineseRemainder (hmk.mul_left hnk) qmn
      (intNatResidue rk k)).prop.2
  exact (Int.natCast_modEq_iff.mpr hright).trans (intNatResidue_modEq rk hk)

private lemma legendreTernaryValue_dvd_of_localFactor
    {a b c r x y z : ℤ} (hac : a.natAbs.Coprime c.natAbs)
    (hr : r ^ 2 ≡ -(b * c) [ZMOD a.natAbs])
    (hlinear : (a.natAbs : ℤ) ∣ r * y + c * z) :
    (a.natAbs : ℤ) ∣ legendreTernaryValue a b c x y z := by
  have haZ : (a : ZMod a.natAbs) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd a a.natAbs).2 Int.natAbs_dvd_self
  have hrZ : (r : ZMod a.natAbs) ^ 2 = -(b * c : ℤ) := by
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_mul] using
      (ZMod.intCast_eq_intCast_iff _ _ _).2 hr
  have hlinearZ : (r * y + c * z : ZMod a.natAbs) = 0 := by
    simpa only [Int.cast_add, Int.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hlinear
  have hmultipleZ :
      (-c * legendreTernaryValue a b c x y z : ZMod a.natAbs) = 0 := by
    calc
      (-c * legendreTernaryValue a b c x y z : ZMod a.natAbs) =
          -(c : ZMod a.natAbs) *
            ((b : ZMod a.natAbs) * (y : ZMod a.natAbs) ^ 2 +
              (c : ZMod a.natAbs) * (z : ZMod a.natAbs) ^ 2) := by
        simp only [legendreTernaryValue, Int.cast_mul, Int.cast_add,
          Int.cast_pow]
        rw [haZ]
        ring
      _ = (-(b * c : ℤ) : ZMod a.natAbs) * (y : ZMod a.natAbs) ^ 2 -
          (c : ZMod a.natAbs) ^ 2 * (z : ZMod a.natAbs) ^ 2 := by
        simp only [Int.cast_mul]
        ring
      _ = (r : ZMod a.natAbs) ^ 2 * (y : ZMod a.natAbs) ^ 2 -
          (c : ZMod a.natAbs) ^ 2 * (z : ZMod a.natAbs) ^ 2 := by
        rw [hrZ]
      _ = (r * y + c * z : ℤ) * (r * y - c * z : ℤ) := by
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul]
        ring
      _ = 0 := by
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul]
        rw [hlinearZ, zero_mul]
  have hmultiple :
      (a.natAbs : ℤ) ∣ -c * legendreTernaryValue a b c x y z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by
      simpa only [Int.cast_neg, Int.cast_mul] using hmultipleZ)
  have hcop : IsCoprime (a.natAbs : ℤ) (-c) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_neg]
    exact hac
  exact hcop.dvd_of_dvd_mul_left hmultiple

/-- Chosen roots of Legendre's three square congruences determine an integral
linear form whose vanishing modulo `|a*b*c|` forces the ternary value to
vanish modulo the same modulus. -/
theorem exists_legendreLinearValue_dvd_imp_ternaryValue_dvd
    {a b c ra rb rc : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a.natAbs.Coprime b.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hra : ra ^ 2 ≡ -(b * c) [ZMOD a.natAbs])
    (hrb : rb ^ 2 ≡ -(c * a) [ZMOD b.natAbs])
    (hrc : rc ^ 2 ≡ -(a * b) [ZMOD c.natAbs]) :
    ∃ A B C : ℤ, ∀ x y z : ℤ,
      ((a * b * c).natAbs : ℤ) ∣ legendreLinearValue A B C x y z →
        ((a * b * c).natAbs : ℤ) ∣
          legendreTernaryValue a b c x y z := by
  let ma := a.natAbs
  let mb := b.natAbs
  let mc := c.natAbs
  have hma : ma ≠ 0 := by simpa [ma] using Int.natAbs_ne_zero.mpr ha
  have hmb : mb ≠ 0 := by simpa [mb] using Int.natAbs_ne_zero.mpr hb
  have hmc : mc ≠ 0 := by simpa [mc] using Int.natAbs_ne_zero.mpr hc
  let A := intChineseRemainderThree ma mb mc hab hac hbc 0 a rc
  let B := intChineseRemainderThree ma mb mc hab hac hbc ra 0 b
  let C := intChineseRemainderThree ma mb mc hab hac hbc c rb 0
  refine ⟨A, B, C, ?_⟩
  intro x y z hlinear
  have hmaProduct : (ma : ℤ) ∣ ((a * b * c).natAbs : ℤ) := by
    norm_cast
    simp only [ma, Int.natAbs_mul]
    exact ⟨b.natAbs * c.natAbs, by ring⟩
  have hmbProduct : (mb : ℤ) ∣ ((a * b * c).natAbs : ℤ) := by
    norm_cast
    simp only [mb, Int.natAbs_mul]
    exact ⟨a.natAbs * c.natAbs, by ring⟩
  have hmcProduct : (mc : ℤ) ∣ ((a * b * c).natAbs : ℤ) := by
    norm_cast
    simp only [mc, Int.natAbs_mul]
    exact ⟨a.natAbs * b.natAbs, by ring⟩
  have hA_a : A ≡ 0 [ZMOD ma] :=
    intChineseRemainderThree_mod_left ma mb mc hma hab hac hbc 0 a rc
  have hA_b : A ≡ a [ZMOD mb] :=
    intChineseRemainderThree_mod_middle ma mb mc hmb hab hac hbc 0 a rc
  have hA_c : A ≡ rc [ZMOD mc] :=
    intChineseRemainderThree_mod_right ma mb mc hmc hab hac hbc 0 a rc
  have hB_a : B ≡ ra [ZMOD ma] :=
    intChineseRemainderThree_mod_left ma mb mc hma hab hac hbc ra 0 b
  have hB_b : B ≡ 0 [ZMOD mb] :=
    intChineseRemainderThree_mod_middle ma mb mc hmb hab hac hbc ra 0 b
  have hB_c : B ≡ b [ZMOD mc] :=
    intChineseRemainderThree_mod_right ma mb mc hmc hab hac hbc ra 0 b
  have hC_a : C ≡ c [ZMOD ma] :=
    intChineseRemainderThree_mod_left ma mb mc hma hab hac hbc c rb 0
  have hC_b : C ≡ rb [ZMOD mb] :=
    intChineseRemainderThree_mod_middle ma mb mc hmb hab hac hbc c rb 0
  have hC_c : C ≡ 0 [ZMOD mc] :=
    intChineseRemainderThree_mod_right ma mb mc hmc hab hac hbc c rb 0
  have hlinearA : (ma : ℤ) ∣ ra * y + c * z := by
    have hmod := (((hA_a.mul (Int.ModEq.refl x)).add
      (hB_a.mul (Int.ModEq.refl y))).add (hC_a.mul (Int.ModEq.refl z)))
    have hdiv := hmod.dvd_iff.mp (hmaProduct.trans hlinear)
    simpa [legendreLinearValue] using hdiv
  have hlinearB : (mb : ℤ) ∣ rb * z + a * x := by
    have hmod := (((hA_b.mul (Int.ModEq.refl x)).add
      (hB_b.mul (Int.ModEq.refl y))).add (hC_b.mul (Int.ModEq.refl z)))
    have hdiv := hmod.dvd_iff.mp (hmbProduct.trans hlinear)
    simpa [legendreLinearValue, add_comm, add_left_comm, add_assoc] using hdiv
  have hlinearC : (mc : ℤ) ∣ rc * x + b * y := by
    have hmod := (((hA_c.mul (Int.ModEq.refl x)).add
      (hB_c.mul (Int.ModEq.refl y))).add (hC_c.mul (Int.ModEq.refl z)))
    have hdiv := hmod.dvd_iff.mp (hmcProduct.trans hlinear)
    simpa [legendreLinearValue, add_comm, add_left_comm, add_assoc] using hdiv
  have hvalueA : (ma : ℤ) ∣ legendreTernaryValue a b c x y z :=
    legendreTernaryValue_dvd_of_localFactor hac hra hlinearA
  have hvalueB : (mb : ℤ) ∣ legendreTernaryValue a b c x y z := by
    have h := legendreTernaryValue_dvd_of_localFactor
      (a := b) (b := c) (c := a) (r := rb) (x := y) (y := z) (z := x)
      hab.symm hrb hlinearB
    change (b.natAbs : ℤ) ∣ legendreTernaryValue a b c x y z
    simpa only [legendreTernaryValue, add_comm, add_left_comm, add_assoc] using h
  have hvalueC : (mc : ℤ) ∣ legendreTernaryValue a b c x y z := by
    have h := legendreTernaryValue_dvd_of_localFactor
      (a := c) (b := a) (c := b) (r := rc) (x := z) (y := x) (z := y)
      hbc.symm hrc hlinearC
    change (c.natAbs : ℤ) ∣ legendreTernaryValue a b c x y z
    simpa only [legendreTernaryValue, add_comm, add_left_comm, add_assoc] using h
  have habInt : IsCoprime (ma : ℤ) (mb : ℤ) := hab.cast
  have habcInt : IsCoprime ((ma : ℤ) * mb) (mc : ℤ) :=
    (hac.mul_left hbc).cast
  have hvalueAB : legendreTernaryValue a b c x y z ≡ 0
      [ZMOD (ma : ℤ) * mb] :=
    (Int.modEq_and_modEq_iff_modEq_mul
      (by simpa [Int.isCoprime_iff_nat_coprime] using habInt)).mp
      ⟨Int.modEq_zero_iff_dvd.mpr hvalueA,
        Int.modEq_zero_iff_dvd.mpr hvalueB⟩
  have hvalueABC : legendreTernaryValue a b c x y z ≡ 0
      [ZMOD ((ma : ℤ) * mb) * mc] :=
    (Int.modEq_and_modEq_iff_modEq_mul
      (by simpa [Int.isCoprime_iff_nat_coprime] using habcInt)).mp
      ⟨hvalueAB, Int.modEq_zero_iff_dvd.mpr hvalueC⟩
  have hproduct : ((ma : ℤ) * mb) * mc ∣
      legendreTernaryValue a b c x y z :=
    Int.modEq_zero_iff_dvd.mp hvalueABC
  simpa [ma, mb, mc, Int.natAbs_mul] using hproduct

/-- Explicit roots of Legendre's congruences produce a nonzero integer point
in the canonical box whose ternary value is divisible by `|a * b * c|`. -/
theorem exists_bounded_nonzero_legendreTernaryValue_dvd
    {a b c ra rb rc : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a.natAbs.Coprime b.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hra : ra ^ 2 ≡ -(b * c) [ZMOD a.natAbs])
    (hrb : rb ^ 2 ≡ -(c * a) [ZMOD b.natAbs])
    (hrc : rc ^ 2 ≡ -(a * b) [ZMOD c.natAbs]) :
    ∃ x y z : ℤ,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x.natAbs ≤ legendreBoxBound b c ∧
      y.natAbs ≤ legendreBoxBound c a ∧
      z.natAbs ≤ legendreBoxBound a b ∧
      ((a * b * c).natAbs : ℤ) ∣
        legendreTernaryValue a b c x y z := by
  obtain ⟨A, B, C, hlinear⟩ :=
    exists_legendreLinearValue_dvd_imp_ternaryValue_dvd
      ha hb hc hab hac hbc hra hrb hrc
  have habc : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hM : (a * b * c).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr habc
  obtain ⟨x, y, z, hnonzero, hx, hy, hz, hdvd⟩ :=
    exists_bounded_nonzero_legendreLinearValue_dvd A B C hM
      (natAbs_mul_lt_legendreBox_card a b c)
  exact ⟨x, y, z, hnonzero, hx, hy, hz, hlinear x y z hdvd⟩

/-- Legendre's explicit-root theorem in the sign orientation with two
positive coefficients and one negative coefficient. -/
theorem exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
    {a b c ra rb rc : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hsa : Squarefree a.natAbs)
    (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hra : ra ^ 2 ≡ -(b * c) [ZMOD a.natAbs])
    (hrb : rb ^ 2 ≡ -(c * a) [ZMOD b.natAbs])
    (hrc : rc ^ 2 ≡ -(a * b) [ZMOD c.natAbs]) :
    ∃ x y z : ℤ,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      legendreTernaryValue a b c x y z = 0 := by
  by_cases hall : a.natAbs = 1 ∧ b.natAbs = 1 ∧ c.natAbs = 1
  · obtain ⟨x, y, z, hz, hvalue⟩ :=
      exists_legendreTernaryValue_eq_zero_of_all_natAbs_eq_one
        ha hb hc hall.1 hall.2.1 hall.2.2
    exact ⟨x, y, z, Or.inr (Or.inr hz), hvalue⟩
  · obtain ⟨x, y, z, hnonzero, hx, hy, hz, hdvd⟩ :=
      exists_bounded_nonzero_legendreTernaryValue_dvd
        (ne_of_gt ha) (ne_of_gt hb) (ne_of_lt hc)
        hab hac hbc hra hrb hrc
    let M := (a * b * c).natAbs
    have hMne : M ≠ 0 := by
      exact Int.natAbs_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)) (ne_of_lt hc))
    have hMpos : 0 < M := Nat.pos_of_ne_zero hMne
    have hlower : -(M : ℤ) ≤ legendreTernaryValue a b c x y z := by
      simpa only [M] using
        (legendreTernaryValue_bounds_of_signs_of_boxBounds
          ha hb hc hx hy hz).1
    have hupper : legendreTernaryValue a b c x y z < 2 * (M : ℤ) := by
      simpa only [M] using
        legendreTernaryValue_lt_two_mul_natAbs_of_signs_of_squarefree
          ha hb hc hsa hsb hsc hac hbc hx hy hall
    have habs : (legendreTernaryValue a b c x y z).natAbs < 2 * M := by
      have hMposInt : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
      have hcast :
          ((legendreTernaryValue a b c x y z).natAbs : ℤ) <
            ((2 * M : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]
        rw [abs_lt]
        constructor <;> norm_num at * <;> omega
      exact_mod_cast hcast
    rcases eq_neg_natCast_or_zero_or_natCast_of_dvd_of_natAbs_lt_two_mul
        hMne hdvd habs with hneg | hzero | hpos
    · obtain ⟨_, _, _, haOne, hbOne⟩ :=
        lower_endpoint_structure_of_signs_of_squarefree
          ha hb hc hsa hsb hab hz hneg
      obtain ⟨X, Y, Z, hZ, hvalue⟩ :=
        exists_legendreTernaryValue_eq_zero_of_two_natAbs_eq_one_of_modEq
          ha hb hc haOne hbOne hrc
      exact ⟨X, Y, Z, Or.inr (Or.inr hZ), hvalue⟩
    · exact ⟨x, y, z, hnonzero, hzero⟩
    · have habcNeg : a * b * c < 0 :=
        mul_neg_of_pos_of_neg (mul_pos ha hb) hc
      have hcast : (M : ℤ) = -(a * b * c) := by
        simp only [M, Int.natCast_natAbs, abs_of_neg habcNeg]
      obtain ⟨X, Y, Z, hZ, hvalue⟩ :=
        exists_legendreTernaryValue_eq_zero_of_eq_neg_mul
          (mul_pos ha hb) (hpos.trans hcast)
      exact ⟨X, Y, Z, Or.inr (Or.inr hZ), hvalue⟩

/-- Legendre's explicit-root theorem for any ordering of nonzero coefficients
with mixed signs. -/
theorem exists_legendreTernaryValue_eq_zero_of_mixed_signs_of_squarefree
    {a b c ra rb rc : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hpos : 0 < a ∨ 0 < b ∨ 0 < c)
    (hneg : a < 0 ∨ b < 0 ∨ c < 0)
    (hsa : Squarefree a.natAbs)
    (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hra : ra ^ 2 ≡ -(b * c) [ZMOD a.natAbs])
    (hrb : rb ^ 2 ≡ -(c * a) [ZMOD b.natAbs])
    (hrc : rc ^ 2 ≡ -(a * b) [ZMOD c.natAbs]) :
    ∃ x y z : ℤ,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      legendreTernaryValue a b c x y z = 0 := by
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · rcases lt_or_gt_of_ne hb0 with hb | hb
    · rcases lt_or_gt_of_ne hc0 with hc | hc
      · exfalso
        rcases hpos with ha' | hb' | hc' <;> omega
      · obtain ⟨x, y, z, hnonzero, hvalue⟩ :=
          exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
            (a := -a) (b := -b) (c := -c) (ra := ra) (rb := rb) (rc := rc)
            (by omega) (by omega) (by omega)
            (by simpa using hsa) (by simpa using hsb) (by simpa using hsc)
            (by simpa using hab) (by simpa using hac) (by simpa using hbc)
            (by simpa [mul_comm] using hra)
            (by simpa [mul_comm] using hrb)
            (by simpa [mul_comm] using hrc)
        refine ⟨x, y, z, hnonzero, ?_⟩
        unfold legendreTernaryValue at hvalue ⊢
        linarith
    · rcases lt_or_gt_of_ne hc0 with hc | hc
      · obtain ⟨x, y, z, hnonzero, hvalue⟩ :=
          exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
            (a := -a) (b := -c) (c := -b) (ra := ra) (rb := rc) (rc := rb)
            (by omega) (by omega) (by omega)
            (by simpa using hsa) (by simpa using hsc) (by simpa using hsb)
            (by simpa using hac) (by simpa using hab) (by simpa using hbc.symm)
            (by simpa [mul_comm] using hra)
            (by simpa [mul_comm] using hrc)
            (by simpa [mul_comm] using hrb)
        refine ⟨x, z, y, by tauto, ?_⟩
        unfold legendreTernaryValue at hvalue ⊢
        linarith
      · obtain ⟨x, y, z, hnonzero, hvalue⟩ :=
          exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
            (a := b) (b := c) (c := a) (ra := rb) (rb := rc) (rc := ra)
            hb hc ha hsb hsc hsa hbc hab.symm hac.symm
            (by simpa [mul_comm] using hrb)
            (by simpa [mul_comm] using hrc)
            (by simpa [mul_comm] using hra)
        exact ⟨z, x, y, by tauto, by
          simpa [legendreTernaryValue, add_comm, add_left_comm, add_assoc]
            using hvalue⟩
  · rcases lt_or_gt_of_ne hb0 with hb | hb
    · rcases lt_or_gt_of_ne hc0 with hc | hc
      · obtain ⟨x, y, z, hnonzero, hvalue⟩ :=
          exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
            (a := -b) (b := -c) (c := -a) (ra := rb) (rb := rc) (rc := ra)
            (by omega) (by omega) (by omega)
            (by simpa using hsb) (by simpa using hsc) (by simpa using hsa)
            (by simpa using hbc) (by simpa using hab.symm) (by simpa using hac.symm)
            (by simpa [mul_comm] using hrb)
            (by simpa [mul_comm] using hrc)
            (by simpa [mul_comm] using hra)
        refine ⟨z, x, y, by tauto, ?_⟩
        unfold legendreTernaryValue at hvalue ⊢
        linarith
      · obtain ⟨x, y, z, hnonzero, hvalue⟩ :=
          exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
            (a := a) (b := c) (c := b) (ra := ra) (rb := rc) (rc := rb)
            ha hc hb hsa hsc hsb hac hab hbc.symm
            (by simpa [mul_comm] using hra)
            (by simpa [mul_comm] using hrc)
            (by simpa [mul_comm] using hrb)
        exact ⟨x, z, y, by tauto, by
          simpa [legendreTernaryValue, add_comm, add_left_comm, add_assoc]
            using hvalue⟩
    · rcases lt_or_gt_of_ne hc0 with hc | hc
      · obtain ⟨x, y, z, hnonzero, hvalue⟩ :=
          exists_legendreTernaryValue_eq_zero_of_signs_of_squarefree
            (a := a) (b := b) (c := c) (ra := ra) (rb := rb) (rc := rc)
            ha hb hc hsa hsb hsc hab hac hbc hra hrb hrc
        exact ⟨x, y, z, hnonzero, hvalue⟩
      · exfalso
        rcases hneg with ha' | hb' | hc' <;> omega

/-- Nonzero mixed-sign squarefree pairwise-coprime integer coefficients that
are p-adically isotropic at every prime admit a nontrivial integral zero. -/
theorem exists_legendreTernaryValue_eq_zero_of_padic_gramIsotropic
    {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hpos : 0 < a ∨ 0 < b ∨ 0 < c)
    (hneg : a < 0 ∨ b < 0 ∨ c < 0)
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])])) :
    ∃ x y z : ℤ,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      legendreTernaryValue a b c x y z = 0 := by
  obtain ⟨hra, hrb, hrc⟩ :=
    legendreCongruenceRoots_of_padic_gramIsotropic
      hsa hsb hsc hab hbc hac.symm hlocal
  obtain ⟨ra, hra⟩ := hra
  obtain ⟨rb, hrb⟩ := hrb
  obtain ⟨rc, hrc⟩ := hrc
  exact exists_legendreTernaryValue_eq_zero_of_mixed_signs_of_squarefree
    ha0 hb0 hc0 hpos hneg hsa hsb hsc hab hac hbc hra hrb hrc

/-- The normalized integral Legendre construction gives a rational diagonal
Gram-isotropy witness by casting its nontrivial integral zero. -/
theorem ternaryDiagonal_gramIsotropic_rat_of_padic_gramIsotropic
    {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hpos : 0 < a ∨ 0 < b ∨ 0 < c)
    (hneg : a < 0 ∨ b < 0 ∨ c < 0)
    (hsa : Squarefree a.natAbs) (hsb : Squarefree b.natAbs)
    (hsc : Squarefree c.natAbs)
    (hab : a.natAbs.Coprime b.natAbs)
    (hac : a.natAbs.Coprime c.natAbs)
    (hbc : b.natAbs.Coprime c.natAbs)
    (hlocal : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])])) :
    PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![(a : ℚ), (b : ℚ), (c : ℚ)]) := by
  obtain ⟨x, y, z, hnonzero, hzero⟩ :=
    exists_legendreTernaryValue_eq_zero_of_padic_gramIsotropic
      ha0 hb0 hc0 hpos hneg hsa hsb hsc hab hac hbc hlocal
  apply (ternaryDiagonal_gramIsotropic_iff_exists_coordinates
    (a : ℚ) (b : ℚ) (c : ℚ)).mpr
  refine ⟨x, y, z, ?_, ?_⟩
  · rcases hnonzero with hx | hy | hz
    · exact Or.inl (Int.cast_ne_zero.mpr hx)
    · exact Or.inr (Or.inl (Int.cast_ne_zero.mpr hy))
    · exact Or.inr (Or.inr (Int.cast_ne_zero.mpr hz))
  · unfold legendreTernaryValue at hzero
    exact_mod_cast hzero

/-- A nondegenerate rational diagonal ternary form that is isotropic over the
reals and every p-adic field is isotropic over the rationals. -/
theorem ternaryDiagonal_gramIsotropic_rat_of_real_and_padic_gramIsotropic
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hreal : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![(a : ℝ), (b : ℝ), (c : ℝ)]))
    (hlocal : ∀ (p : ℕ) [Fact p.Prime],
      PositiveDefiniteIntegralLattice.GramIsotropic
        (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])])) :
    PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![a, b, c]) := by
  obtain ⟨⟨hA0, hA_squarefree⟩, ⟨hB0, hB_squarefree⟩,
      ⟨hC0, hC_squarefree⟩, hAB, hAC, hBC⟩ :=
    ternaryPairwiseSignedSquarefreeIntegers_properties ha hb hc
  obtain ⟨hpos, hneg⟩ :=
    ternaryPairwiseSignedSquarefreeIntegers_mixed_signs_of_real_gramIsotropic
      ha hb hc hreal
  have hnormalized : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal
        ![(ternaryPairwiseSignedSquarefreeIntegerFirst a b c : ℚ),
          (ternaryPairwiseSignedSquarefreeIntegerSecond a b c : ℚ),
          (ternaryPairwiseSignedSquarefreeIntegerThird a b c : ℚ)]) :=
    ternaryDiagonal_gramIsotropic_rat_of_padic_gramIsotropic
      hA0 hB0 hC0 hpos hneg hA_squarefree hB_squarefree hC_squarefree
      hAB hAC hBC
      (padic_gramIsotropic_pairwiseSignedSquarefreeIntegers ha hb hc hlocal)
  have hcanonical : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal
        ![(hilbertSignedSquarefreeInteger a : ℚ),
          (hilbertSignedSquarefreeInteger b : ℚ),
          (hilbertSignedSquarefreeInteger c : ℚ)]) := by
    exact (ternaryDiagonal_gramIsotropic_iff_pairwiseSignedCoefficients
      (K := ℚ) (hilbertSignedSquarefreeInteger a)
        (hilbertSignedSquarefreeInteger b)
        (hilbertSignedSquarefreeInteger c)).mpr hnormalized
  exact (ternaryDiagonal_gramIsotropic_iff_signedSquarefreeIntegers
    (K := ℚ) ha hb hc).mpr hcanonical

/-- A rational diagonal ternary isotropy witness remains isotropic after
scalar extension to any characteristic-zero field. -/
theorem ternaryDiagonal_gramIsotropic_scalarExtension_of_rat
    {K : Type*} [Field K] [CharZero K] {a b c : ℚ}
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![a, b, c])) :
    PositiveDefiniteIntegralLattice.GramIsotropic
      (Matrix.diagonal ![(a : K), (b : K), (c : K)]) := by
  obtain ⟨x, y, z, hnonzero, hzero⟩ :=
    (ternaryDiagonal_gramIsotropic_iff_exists_coordinates a b c).mp hiso
  apply (ternaryDiagonal_gramIsotropic_iff_exists_coordinates
    (a : K) (b : K) (c : K)).mpr
  refine ⟨(x : K), (y : K), (z : K), ?_, ?_⟩
  · rcases hnonzero with hx | hy | hz
    · exact Or.inl (by exact_mod_cast hx)
    · exact Or.inr (Or.inl (by exact_mod_cast hy))
    · exact Or.inr (Or.inr (by exact_mod_cast hz))
  · exact_mod_cast hzero

/-- Ternary Hasse--Minkowski for a nondegenerate rational diagonal: rational
isotropy is equivalent to real and all p-adic isotropy. -/
theorem ternaryDiagonal_gramIsotropic_iff_real_and_padic
    (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    PositiveDefiniteIntegralLattice.GramIsotropic (Matrix.diagonal ![a, b, c]) ↔
      PositiveDefiniteIntegralLattice.GramIsotropic
          (Matrix.diagonal ![(a : ℝ), (b : ℝ), (c : ℝ)]) ∧
        ∀ (p : ℕ) [Fact p.Prime],
          PositiveDefiniteIntegralLattice.GramIsotropic
            (Matrix.diagonal ![(a : ℚ_[p]), (b : ℚ_[p]), (c : ℚ_[p])]) := by
  constructor
  · intro hiso
    exact ⟨ternaryDiagonal_gramIsotropic_scalarExtension_of_rat
        (K := ℝ) hiso,
      fun p _ ↦ ternaryDiagonal_gramIsotropic_scalarExtension_of_rat
        (K := ℚ_[p]) hiso⟩
  · rintro ⟨hreal, hlocal⟩
    exact ternaryDiagonal_gramIsotropic_rat_of_real_and_padic_gramIsotropic
      ha hb hc hreal hlocal

end Rat
