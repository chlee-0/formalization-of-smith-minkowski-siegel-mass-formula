import SMSFormula.FiniteQuadraticSumAdjugateKernel

/-!
# The kernel bound of the finite quadratic-sum estimate, completed

The adjugate step put `ker(H mod q)` inside the `det H`-torsion coordinatewise and reduced the bound
to one generic input: the cardinality of that torsion in `ZMod q`.  `ZMod.addOrderOf_coe` gives an
element's order, not the multiplication kernel's cardinality, but the needed inequality is available
in cyclic form: `IsAddCyclic.card_nsmul_eq_zero_le` bounds `#{a : alpha | n . a = 0}` by `n`, and
`ZMod q` is an instance.  Multiplication by an integer `d` is `d.natAbs`-smul up to the sign `-1`,
which does not affect vanishing, so the torsion count is at most `|d|` -- no `gcd` computation
needed.

Combining, the kernel of an integral matrix reduced modulo any nonzero conductor satisfies

`#ker(H mod q) <= |det H|^n`,

with the right-hand side independent of `q`.  That is exactly the conductor-uniform input of the
modulus bound.

Negative scope: the classical count is `gcd(det H, q)`, and only the inequality is proved here --
nothing computes the torsion exactly.  The squaring and finite character orthogonality reduction,
the summation by conductor, and the archimedean factor are not done here, and no character sum
is estimated.
-/

namespace SMSFormula.FiniteQuadraticSum

open Matrix Finset

/-- The generic input: the `d`-torsion of `ZMod q` has at most `|d|` elements.  Multiplication by
an integer is `natAbs`-smul up to a sign, and `ZMod q` is additively cyclic, so the cyclic bound
applies with no `gcd` computation. -/
theorem card_scalar_torsion_le (q : ℕ) [NeZero q] {d : ℤ} (hd : d ≠ 0) :
    Nat.card {x : ZMod q // (d : ZMod q) * x = 0} ≤ d.natAbs := by
  classical
  have hpos : 0 < d.natAbs := Int.natAbs_pos.2 hd
  have hcast : ((d.natAbs : ℕ) : ZMod q) = ((d.natAbs : ℤ) : ZMod q) :=
    (Int.cast_natCast (R := ZMod q) d.natAbs).symm
  have key : ((d.natAbs : ℕ) : ZMod q) = (d : ZMod q) ∨
      ((d.natAbs : ℕ) : ZMod q) = -(d : ZMod q) := by
    rcases le_or_gt 0 d with hd0 | hd0
    · left
      have h1 : ((d.natAbs : ℤ)) = d := Int.natAbs_of_nonneg hd0
      rw [hcast, h1]
    · right
      have h1 : (((-d).natAbs : ℕ) : ℤ) = -d := Int.natAbs_of_nonneg (by linarith)
      rw [Int.natAbs_neg] at h1
      rw [hcast, h1, Int.cast_neg]
  have hset : ∀ x : ZMod q, ((d : ZMod q) * x = 0) ↔ (d.natAbs • x = 0) := by
    intro x
    rw [nsmul_eq_mul]
    rcases key with h | h
    · rw [h]
    · rw [h, neg_mul, neg_eq_zero]
  have hcyc := IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod q) hpos
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine le_trans (le_of_eq ?_) hcyc
  congr 1
  ext x
  simp [hset x]

/-- The conductor-uniform kernel bound: for a nonsingular integral matrix, the kernel of its
reduction modulo any nonzero conductor has at most `|det H|^n` elements, a bound with no `q` in
it. -/
theorem card_kernel_le_det_pow {m : Type*} [Fintype m] [DecidableEq m]
    (q : ℕ) [NeZero q] (H : Matrix m m ℤ) (hdet : H.det ≠ 0) :
    Nat.card {h : m → ZMod q // (H.map (Int.cast : ℤ → ZMod q)) *ᵥ h = 0} ≤
      H.det.natAbs ^ Fintype.card m := by
  classical
  refine (card_kernel_le q H).trans ?_
  have hpi : Nat.card (m → {x : ZMod q // ((H.det : ℤ) : ZMod q) * x = 0}) =
      (Nat.card {x : ZMod q // ((H.det : ℤ) : ZMod q) * x = 0}) ^ Fintype.card m := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [hpi]
  exact Nat.pow_le_pow_left (card_scalar_torsion_le q hdet) _

end SMSFormula.FiniteQuadraticSum
