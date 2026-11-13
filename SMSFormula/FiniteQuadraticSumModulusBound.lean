import SMSFormula.FiniteQuadraticSumOrthogonality
import SMSFormula.FiniteQuadraticSumKernelCount
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The modulus bound of the finite quadratic-sum estimate, assembled

The three inputs are in hand: polarization produces the matrix `H = B + B`, character
orthogonality isolates its kernel, and the adjugate argument bounds that kernel by `|det H|^n`
uniformly in the conductor.  This file performs the assembly.

The squaring identity is stated first in purely algebraic form over an arbitrary finite abelian
domain group: the product of the character sum with the sum of the negated values is the double
sum of the translate difference.  Only the reindexing `w' = w + h` is used, so no analysis and no
complex conjugation enter at this stage.

Specialising to the affine quadratic and applying the orthogonality evaluation collapses the inner
sum, leaving `card * (sum over the kernel)`.  Over `ℂ` the second factor is the conjugate, because
a character of a finite group takes values of modulus one, so the left side becomes the squared
modulus and the triangle inequality gives

`‖sum_w psi (Q w)‖^2 <= card * #ker(H)`,

and with the conductor-uniform kernel count, `‖sum_w psi (Q w)‖^2 <= q^n * |det H|^n` -- the
unnormalised form of `|G_q| <= |det H|^(n/2) q^(-n/2)`.

Negative scope: nothing here evaluates a Gauss sum, computes the kernel exactly (only the
inequality is available), or touches the archimedean factor, the summation over conductors, or the
integrability statement over all conductors.  The hypothesis relating `B + B` to an integral
matrix is carried explicitly; no integral model is constructed.
-/

namespace SMSFormula.FiniteQuadraticSum

open Matrix Finset Complex

variable {q : ℕ} {R : Type*} {m : Type*}

/-- The squaring identity, purely algebraic: the product of a character sum with the sum of its
negated values is the double sum over translates.  Only the reindexing `w' = w + h` is used. -/
theorem sum_mul_sum_neg {G A : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup A]
    [CommSemiring R] (psi : AddChar A R) (f : G → A) :
    (∑ w : G, psi (f w)) * (∑ w : G, psi (-(f w))) =
      ∑ h : G, ∑ w : G, psi (f (w + h) - f w) := by
  classical
  calc (∑ w : G, psi (f w)) * (∑ w : G, psi (-(f w)))
      = ∑ w' : G, ∑ w : G, psi (f w') * psi (-(f w)) := Fintype.sum_mul_sum _ _
    _ = ∑ w' : G, ∑ w : G, psi (f w' - f w) := by
        refine Finset.sum_congr rfl fun w' _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
        rw [← AddChar.map_add_eq_mul, sub_eq_add_neg]
    _ = ∑ w : G, ∑ w' : G, psi (f w' - f w) := Finset.sum_comm
    _ = ∑ w : G, ∑ h : G, psi (f (w + h) - f w) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        exact (Fintype.sum_equiv (Equiv.addLeft w)
          (fun h ↦ psi (f (w + h) - f w)) (fun w' ↦ psi (f w' - f w)) (fun h ↦ by simp)).symm
    _ = ∑ h : G, ∑ w : G, psi (f (w + h) - f w) := Finset.sum_comm

/-- The collapsed square: combining the squaring identity with the orthogonality evaluation, the
double sum reduces to the cardinality times a sum over the kernel of `B + B`. -/
theorem sum_mul_sum_neg_affineQuadratic [CommSemiring R] [IsDomain R] [Fintype m] [DecidableEq m]
    [NeZero q] {psi : AddChar (ZMod q) R} (hpsi : Function.Injective psi)
    {B : Matrix m m (ZMod q)} (hB : B.IsSymm) (l : m → ZMod q) (c : ZMod q) :
    (∑ w : m → ZMod q, psi (affineQuadratic B l c w)) *
        (∑ w : m → ZMod q, psi (-(affineQuadratic B l c w))) =
      (Fintype.card (m → ZMod q) : R) *
        ∑ h ∈ Finset.univ.filter (fun h : m → ZMod q ↦ (B + B) *ᵥ h = 0),
          psi (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) := by
  classical
  rw [sum_mul_sum_neg, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [sum_char_affineQuadratic_translate_sub hpsi hB l c h]
  by_cases hk : (B + B) *ᵥ h = 0 <;> simp [hk, mul_comm]

/-- The modulus bound: over `ℂ` the second factor of the squaring identity is the conjugate, so
the squared modulus of the character sum is bounded by the cardinality times the kernel size. -/
theorem norm_sq_sum_char_affineQuadratic_le [Fintype m] [DecidableEq m] [NeZero q]
    {psi : AddChar (ZMod q) ℂ} (hpsi : Function.Injective psi)
    {B : Matrix m m (ZMod q)} (hB : B.IsSymm) (l : m → ZMod q) (c : ZMod q) :
    ‖∑ w : m → ZMod q, psi (affineQuadratic B l c w)‖ ^ 2 ≤
      (Fintype.card (m → ZMod q) : ℝ) *
        (Finset.univ.filter (fun h : m → ZMod q ↦ (B + B) *ᵥ h = 0)).card := by
  classical
  set S : ℂ := ∑ w : m → ZMod q, psi (affineQuadratic B l c w) with hS
  have hconj : (∑ w : m → ZMod q, psi (-(affineQuadratic B l c w))) = (starRingEnd ℂ) S := by
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun w _ ↦ AddChar.map_neg_eq_conj psi _
  have key := sum_mul_sum_neg_affineQuadratic hpsi hB l c (psi := psi)
  rw [← hS, hconj, Complex.mul_conj'] at key
  have hnorm : ((‖S‖ ^ 2 : ℝ) : ℂ) =
      (Fintype.card (m → ZMod q) : ℂ) *
        ∑ h ∈ Finset.univ.filter (fun h : m → ZMod q ↦ (B + B) *ᵥ h = 0),
          psi (h ⬝ᵥ (B *ᵥ h) + l ⬝ᵥ h) := by
    rw [← key]
    push_cast
    ring
  have hle : ‖((‖S‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (Fintype.card (m → ZMod q) : ℝ) *
        (Finset.univ.filter (fun h : m → ZMod q ↦ (B + B) *ᵥ h = 0)).card := by
    rw [hnorm, norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    simp
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hle

/-- The conductor-uniform form: when `B + B` is the reduction of a nonsingular integral matrix, the
squared modulus is bounded by `q^n |det H|^n`, with the determinant factor independent of `q`. -/
theorem norm_sq_sum_char_affineQuadratic_le_det_pow [Fintype m] [DecidableEq m] [NeZero q]
    {psi : AddChar (ZMod q) ℂ} (hpsi : Function.Injective psi)
    {B : Matrix m m (ZMod q)} (hB : B.IsSymm) (l : m → ZMod q) (c : ZMod q)
    {H : Matrix m m ℤ} (hdet : H.det ≠ 0) (hH : B + B = H.map (Int.cast : ℤ → ZMod q)) :
    ‖∑ w : m → ZMod q, psi (affineQuadratic B l c w)‖ ^ 2 ≤
      (q : ℝ) ^ Fintype.card m * (H.det.natAbs : ℝ) ^ Fintype.card m := by
  classical
  refine (norm_sq_sum_char_affineQuadratic_le hpsi hB l c).trans ?_
  have hker : (Finset.univ.filter (fun h : m → ZMod q ↦ (B + B) *ᵥ h = 0)).card ≤
      H.det.natAbs ^ Fintype.card m := by
    have hcard := card_kernel_le_det_pow (m := m) q H hdet
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
    simpa [hH] using hcard
  have hcardfun : (Fintype.card (m → ZMod q) : ℝ) = (q : ℝ) ^ Fintype.card m := by
    rw [Fintype.card_fun, ZMod.card]
    push_cast
    ring
  rw [hcardfun]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast hker

end SMSFormula.FiniteQuadraticSum
