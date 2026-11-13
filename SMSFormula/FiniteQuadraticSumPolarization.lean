import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.LinearCombination

/-!
# The squaring step of the quadratic-sum bound: polarization, and where `H = 2B` comes from

Lemma B estimates an affine quadratic character sum by squaring its modulus and applying finite
character orthogonality.  The algebra that makes that work -- and the reason the matrix `H = 2B`
appears at all -- is a polarization identity, and it is what this file proves.

For a symmetric `B` and the affine quadratic `Q(x) = x . B x + l . x + c` over any commutative
ring, translating the argument by `h` changes the value by

`Q(w + h) - Q(w) = (h . B h + l . h) + ((B + B) h) . w`,

so the dependence on `w` is entirely through the pairing of `w` with `(B + B) h = 2 B h = H h`.
That is the whole content of the squaring step: after the substitution `z = w + h`, the inner sum
over `w` is a sum of a character against a linear form whose coefficient vector is `H h`, and
character orthogonality kills it unless `H h = 0` -- which is exactly why the kernel of `H mod q`,
bounded in the two previous files, is the quantity that survives.

Symmetry is used, once: the cross terms `w . B h` and `h . B w` are equal only because `B` is
symmetric, and combining them is what produces `B + B` rather than a one-sided `B`.

Negative scope: this is the algebraic step.  No character is introduced, no orthogonality is
invoked, no sum is formed, and no modulus is estimated; the reduction of the double sum to the
kernel sum is not carried out here.
-/

namespace SMSFormula.FiniteQuadraticSum

open Matrix

variable {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]

/-- The affine quadratic form of Lemma B: a symmetric quadratic part, a linear term and a
constant. -/
def affineQuadratic (B : Matrix m m R) (l : m → R) (c : R) (x : m → R) : R :=
  x ⬝ᵥ (B *ᵥ x) + l ⬝ᵥ x + c

/-- Symmetry, used once: for a symmetric matrix the two cross terms agree. -/
theorem dotProduct_mulVec_comm_of_isSymm {B : Matrix m m R} (hB : B.IsSymm) (w h : m → R) :
    w ⬝ᵥ (B *ᵥ h) = h ⬝ᵥ (B *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq]
  exact dotProduct_comm _ _

/-- The polarization identity.  Translating the argument by `h` changes the affine quadratic by a
term free of `w`, plus the pairing of `w` with `(B + B) h`.  The matrix `B + B = 2B` is exactly
`H`. -/
theorem affineQuadratic_add {B : Matrix m m R} (hB : B.IsSymm) (l : m → R) (c : R) (w h : m → R) :
    affineQuadratic B l c (w + h) =
      affineQuadratic B l c w + (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) + ((B + B) *ᵥ h) ⬝ᵥ w := by
  have hswap := dotProduct_mulVec_comm_of_isSymm hB w h
  have hcomm : ((B *ᵥ h)) ⬝ᵥ w = w ⬝ᵥ (B *ᵥ h) := dotProduct_comm _ _
  simp only [affineQuadratic, Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct]
  linear_combination -hswap - 2 * hcomm

/-- `H` is `2B`, literally. -/
theorem add_self_eq_two_smul (B : Matrix m m R) : B + B = (2 : R) • B := by
  rw [two_smul]

/-- The consequence that drives the estimate: on the kernel of `H = 2B` the translation changes the
affine quadratic by a quantity independent of `w`.  Off the kernel the change still depends on `w`
only through the pairing with `H h`, which is what character orthogonality then annihilates. -/
theorem affineQuadratic_add_of_mulVec_eq_zero {B : Matrix m m R} (hB : B.IsSymm)
    (l : m → R) (c : R) {h : m → R} (hh : ((B + B) *ᵥ h) = 0) (w : m → R) :
    affineQuadratic B l c (w + h) =
      affineQuadratic B l c w + (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) := by
  rw [affineQuadratic_add hB l c w h, hh, zero_dotProduct, add_zero]

end SMSFormula.FiniteQuadraticSum
