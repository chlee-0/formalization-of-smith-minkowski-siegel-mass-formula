import SMSFormula.SkewSymmetricMatrixBasis
import Mathlib.Algebra.BigOperators.Fin

/-!
# Products over strict upper pairs

Every vertex of the complete graph on `Fin n` occurs in exactly `n - 1`
strict upper pairs. Consequently, a product of one factor from each endpoint
of every strict pair is the `(n - 1)`st power of the vertex product.

This file does not compute determinant norms or determinant-form actions,
transport a measure, or glue charts.
-/

noncomputable section

open scoped BigOperators

namespace Matrix
namespace StrictUpperPair

/-- Split strict pairs on `Fin (n + 1)` into pairs below the last index and
pairs whose second endpoint is the last index. -/
def succEquiv (n : ℕ) :
    StrictUpperPair (n + 1) ≃ StrictUpperPair n ⊕ Fin n where
  toFun q :=
    if hq : q.1.2 = Fin.last n then
      Sum.inr (q.1.1.castPred (Fin.ne_last_of_lt (hq ▸ q.2)))
    else
      Sum.inl
        ⟨(q.1.1.castPred (Fin.ne_last_of_lt q.2),
            q.1.2.castPred hq),
          Fin.castPred_lt_castPred q.2 hq⟩
  invFun q :=
    match q with
    | Sum.inl r =>
        ⟨(r.1.1.castSucc, r.1.2.castSucc),
          Fin.castSucc_lt_castSucc_iff.mpr r.2⟩
    | Sum.inr i =>
        ⟨(i.castSucc, Fin.last n), Fin.castSucc_lt_last i⟩
  left_inv q := by
    by_cases hq : q.1.2 = Fin.last n
    · simp only [hq, ↓reduceDIte]
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.castSucc_castPred _ _
      · exact hq.symm
    · simp only [hq, ↓reduceDIte]
      apply Subtype.ext
      apply Prod.ext <;> exact Fin.castSucc_castPred _ _
  right_inv q := by
    rcases q with q | i
    · simp only [Fin.castSucc_ne_last, ↓reduceDIte]
      congr
    · simp only [↓reduceDIte]
      congr

theorem prod_endpoint_mul {M : Type*} [CommMonoid M]
    (d : Fin n → M) :
    (∏ q : StrictUpperPair n, d q.1.1 * d q.1.2) =
      (∏ i : Fin n, d i) ^ (n - 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      cases n with
      | zero =>
          simp only [Nat.add_sub_cancel, pow_zero]
          apply Fintype.prod_eq_one
          intro q
          have h : q.1.1 = q.1.2 := by
            apply Fin.ext
            omega
          exact (ne_of_lt q.2 h).elim
      | succ n =>
          let d' : Fin (n + 1) → M := fun i => d i.castSucc
          calc
            (∏ q : StrictUpperPair (n + 2), d q.1.1 * d q.1.2) =
                (∏ q : StrictUpperPair (n + 1),
                    d' q.1.1 * d' q.1.2) *
                  ∏ i : Fin (n + 1), d' i * d (Fin.last (n + 1)) := by
                    rw [Fintype.prod_equiv (succEquiv (n + 1))
                      (fun q : StrictUpperPair (n + 2) =>
                        d q.1.1 * d q.1.2)
                      (fun q : StrictUpperPair (n + 1) ⊕ Fin (n + 1) =>
                        match q with
                        | Sum.inl r => d' r.1.1 * d' r.1.2
                        | Sum.inr i => d' i * d (Fin.last (n + 1)))]
                    · rw [Fintype.prod_sum_type]
                    · intro q
                      by_cases hq : q.1.2 = Fin.last (n + 1)
                      · simp [succEquiv, hq, d']
                      · simp [succEquiv, hq, d']
            _ = (∏ i : Fin (n + 1), d' i) ^ n *
                ((∏ i : Fin (n + 1), d' i) *
                  d (Fin.last (n + 1)) ^ (n + 1)) := by
                    rw [ih d', Finset.prod_mul_distrib, Fin.prod_const]
                    simp only [Nat.add_sub_cancel]
            _ = ((∏ i : Fin (n + 1), d' i) *
                  d (Fin.last (n + 1))) ^ (n + 1) := by
                    rw [mul_pow, pow_succ (∏ i : Fin (n + 1), d' i) n]
                    ac_rfl
            _ = (∏ i : Fin (n + 2), d i) ^ (n + 1) := by
                    congr 1
                    exact (Fin.prod_univ_castSucc d).symm
            _ = (∏ i : Fin (n + 2), d i) ^ (n + 2 - 1) := by
                    congr 1

end StrictUpperPair
end Matrix
