import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Defs
import SMSFormula.FiniteQuadraticSumPolarization

/-!
# The orthogonality reduction of the quadratic-sum bound

The polarization step showed that translating the affine quadratic by `h` changes it by a term free
of `w` plus the pairing of `w` with `H h = 2 B h`.  What remains of Lemma B's reduction is to sum
that over `w` and see the pairing term collapse.

The mechanism is orthogonality, and mathlib already has it in usable form:
`AddChar.sum_eq_ite` says the sum of an additive character over a finite additive group is the
cardinality when the character is trivial and zero otherwise.  What was missing is the carrier: the
map `w |-> psi(v . w)` is itself an additive character on the finite vector group, and it is trivial
exactly when `v = 0`, provided `psi` is injective -- which is the genuine form of "of exact order
`q`".  Both directions are proved below, the forward one by testing against a standard basis vector.

Combining with the polarization gives Lemma B's reduction in one statement: for every `h`,

`sum over w of psi(Q(w+h) - Q(w))` is `psi(h.Bh + l.h) * card` when `H h = 0`, and zero otherwise.

So only the kernel of `H mod q` survives the inner sum -- and that kernel is exactly what the two
earlier files bound by `|det H|^n`, uniformly in the conductor.

Negative scope: injectivity of the character is a real hypothesis, not cosmetic -- for a character
with a nontrivial kernel the pairing character can be trivial at a nonzero `v`, and the collapse
fails.  The outer sum, the modulus estimate and the passage to `|G_q|` are not done here; this
supplies the inner-sum evaluation only.
-/

namespace SMSFormula.FiniteQuadraticSum

open Matrix Finset

variable {q : ℕ} {R : Type*} {m : Type*}

/-- The pairing character: a character composed with a linear form is again an additive character,
on the finite vector group. -/
noncomputable def linearAddChar [CommMonoid R] [Fintype m]
    (psi : AddChar (ZMod q) R) (v : m → ZMod q) : AddChar (m → ZMod q) R where
  toFun w := psi (v ⬝ᵥ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' w w' := by simp [dotProduct_add, AddChar.map_add_eq_mul]

@[simp]
theorem linearAddChar_apply [CommMonoid R] [Fintype m]
    (psi : AddChar (ZMod q) R) (v w : m → ZMod q) :
    linearAddChar psi v w = psi (v ⬝ᵥ w) := rfl

/-- The triviality criterion: the pairing character is trivial exactly at the zero vector, provided
the character is injective.  The forward direction tests against a standard basis vector. -/
theorem linearAddChar_eq_zero_iff [CommMonoid R] [Fintype m] [DecidableEq m]
    {psi : AddChar (ZMod q) R} (hpsi : Function.Injective psi) (v : m → ZMod q) :
    linearAddChar psi v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    have hw := congrFun (congrArg (fun (f : AddChar (m → ZMod q) R) ↦ (f : (m → ZMod q) → R)) hv)
      (Pi.single i 1)
    simp only [linearAddChar_apply, AddChar.zero_apply] at hw
    have hdot : v ⬝ᵥ (Pi.single i (1 : ZMod q)) = v i := by
      simp [dotProduct_single]
    rw [hdot] at hw
    have : psi (v i) = psi 0 := by rw [hw, AddChar.map_zero_eq_one]
    simpa using hpsi this
  · rintro rfl
    ext w
    simp

/-- Orthogonality against a linear form on the finite vector group: the sum is the cardinality at
the zero vector and zero at every other. -/
theorem sum_linearAddChar [CommSemiring R] [IsDomain R] [Fintype m] [DecidableEq m] [NeZero q]
    {psi : AddChar (ZMod q) R} (hpsi : Function.Injective psi) (v : m → ZMod q)
    [Decidable (v = 0)] :
    ∑ w : m → ZMod q, psi (v ⬝ᵥ w) =
      if v = 0 then (Fintype.card (m → ZMod q) : R) else 0 := by
  classical
  have h := AddChar.sum_eq_ite (linearAddChar psi v)
  simp only [linearAddChar_apply] at h
  rw [h]
  simp [linearAddChar_eq_zero_iff hpsi]

/-- Lemma B's inner sum, evaluated.  Polarization plus orthogonality: summing the character of the
translation difference over `w` gives the constant times the cardinality when `h` lies in the kernel
of `H = B + B`, and zero otherwise.  Only that kernel survives. -/
theorem sum_char_affineQuadratic_translate_sub
    [CommSemiring R] [IsDomain R] [Fintype m] [DecidableEq m] [NeZero q]
    {psi : AddChar (ZMod q) R} (hpsi : Function.Injective psi)
    {B : Matrix m m (ZMod q)} (hB : B.IsSymm) (l : m → ZMod q) (c : ZMod q) (h : m → ZMod q)
    [Decidable ((B + B) *ᵥ h = 0)] :
    ∑ w : m → ZMod q,
        psi (affineQuadratic B l c (w + h) - affineQuadratic B l c w) =
      if (B + B) *ᵥ h = 0 then
        psi (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) * (Fintype.card (m → ZMod q) : R) else 0 := by
  classical
  have hsplit : ∀ w : m → ZMod q,
      affineQuadratic B l c (w + h) - affineQuadratic B l c w =
        (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) + ((B + B) *ᵥ h) ⬝ᵥ w := by
    intro w
    rw [affineQuadratic_add hB l c w h]
    ring
  calc ∑ w : m → ZMod q, psi (affineQuadratic B l c (w + h) - affineQuadratic B l c w)
      = ∑ w : m → ZMod q,
          psi (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) * psi (((B + B) *ᵥ h) ⬝ᵥ w) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [hsplit w, AddChar.map_add_eq_mul]
    _ = psi (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) * ∑ w : m → ZMod q, psi (((B + B) *ᵥ h) ⬝ᵥ w) := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [sum_linearAddChar hpsi ((B + B) *ᵥ h)]
        by_cases hk : (B + B) *ᵥ h = 0 <;> simp [hk]

end SMSFormula.FiniteQuadraticSum
