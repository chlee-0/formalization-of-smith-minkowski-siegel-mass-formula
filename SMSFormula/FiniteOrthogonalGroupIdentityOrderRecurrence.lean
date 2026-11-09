import SMSFormula.Product

/-!
# Identity-form finite orthogonal-group order recurrence

This module packages the arbitrary-rank orbit--stabilizer recurrence already
implicit in the general head-vector action and weighted-identity transitivity
theorems.  It is the common induction interface behind the
fixed-rank finite orthogonal-group computations in `Product.lean`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Splitting off the leading coordinate decomposes a quadratic shell for
`diag(c,B)` into the sigma of the corresponding lower-dimensional shells.
This is the dimension-independent shell recurrence needed by the order
induction. -/
noncomputable def finiteGramNormVectorsFinSuccEquivSigma
    {K : Type*} [Field K]
    (c d : K) (B : Matrix (Fin n) (Fin n) K) :
    finiteGramNormVectors (finSuccGramBlock c B) d ≃
      Σ z : K, finiteGramNormVectors B (d - c * z ^ 2) where
  toFun v := ⟨v.1 0, ⟨fun i => v.1 i.succ, by
    have hv := v.2
    simp [gramQuadraticValue, finSuccGramBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two] at hv ⊢
    linear_combination hv⟩⟩
  invFun v := ⟨Fin.cases v.1 v.2.1, by
    have hv := v.2.2
    simp [finiteGramNormVectors, gramQuadraticValue, finSuccGramBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two] at hv ⊢
    linear_combination hv⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv v := by
    rcases v with ⟨z, ⟨w, hw⟩⟩
    rfl

/-- Cardinal form of the general leading-coordinate shell decomposition. -/
theorem natCard_finiteGramNormVectors_finSucc_eq_sum
    {K : Type*} [Field K] [Fintype K]
    (c d : K) (B : Matrix (Fin n) (Fin n) K) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock c B) d) =
      ∑ z : K, Nat.card (finiteGramNormVectors B (d - c * z ^ 2)) := by
  rw [Nat.card_congr (finiteGramNormVectorsFinSuccEquivSigma c d B),
    Nat.card_sigma]

/-- If a lower-dimensional quadratic shell has cardinality `a` at zero and
the constant cardinality `b` at every nonzero value, its contribution to the
next identity norm-one shell is `2a + (|K|-2)b`.  This holds in
arbitrary rank. -/
theorem sum_natCard_finiteGramNormVectors_one_sub_sq_of_constant_nonzero
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2)
    (B : Matrix (Fin n) (Fin n) K) (a b : ℕ)
    (hzero : Nat.card (finiteGramNormVectors B 0) = a)
    (hnonzero : ∀ c : K, c ≠ 0 →
      Nat.card (finiteGramNormVectors B c) = b) :
    ∑ x : K, Nat.card (finiteGramNormVectors B (1 - x ^ 2)) =
      2 * a + (Nat.card K - 2) * b := by
  classical
  let p : K → Prop := fun x => 1 - x ^ 2 = 0
  have hp_card : (Finset.univ.filter p).card = 2 := by
    have hp_eq : Finset.univ.filter p = ({1, -1} : Finset K) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, p]
      rw [sub_eq_zero, eq_comm, pow_two, mul_self_eq_one_iff]
    rw [hp_eq]
    have hone : (1 : K) ≠ -1 :=
      (Ring.neg_one_ne_one_of_char_ne_two hchar).symm
    simp [hone]
  have hnot_card :
      (Finset.univ.filter fun x => ¬p x).card = Nat.card K - 2 := by
    have hpartition :=
      Finset.card_filter_add_card_filter_not (s := Finset.univ) p
    rw [hp_card, Finset.card_univ, ← Nat.card_eq_fintype_card] at hpartition
    omega
  calc
    ∑ x : K, Nat.card (finiteGramNormVectors B (1 - x ^ 2)) =
        (∑ x ∈ Finset.univ.filter p,
          Nat.card (finiteGramNormVectors B (1 - x ^ 2))) +
        ∑ x ∈ Finset.univ.filter (fun x => ¬p x),
          Nat.card (finiteGramNormVectors B (1 - x ^ 2)) := by
      symm
      exact Finset.sum_filter_add_sum_filter_not Finset.univ p _
    _ = (Finset.univ.filter p).card * a +
        (Finset.univ.filter fun x => ¬p x).card * b := by
      rw [Finset.sum_const_nat (fun x hx => by
        have hx0 : 1 - x ^ 2 = 0 := (Finset.mem_filter.mp hx).2
        simpa [hx0] using hzero),
        Finset.sum_const_nat (fun x hx =>
          hnonzero (1 - x ^ 2) (Finset.mem_filter.mp hx).2)]
    _ = 2 * a + (Nat.card K - 2) * b := by rw [hp_card, hnot_card]

/-- Over a finite field of odd characteristic, the order of the orthogonal
group of `diag(d, Iₙ)` is the size of its norm-`d` shell times the order of
the rank-`n` identity orthogonal group. -/
theorem natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
    {K : Type*} [Field K] [Finite K]
    (hchar : ringChar K ≠ 2) (d : K) (hd : d ≠ 0) :
    Nat.card (finiteGramNormVectors
        (finSuccIdentityGramMatrix (n := n) d) d) *
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin n) (Fin n) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := n) d)) := by
  have hrec := natCard_finSuccHeadOrbit_mul_orthogonal_eq
    (n := n) d hd (1 : Matrix (Fin n) (Fin n) K) (by simp)
  change Nat.card (MulAction.orbit
      (finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := n) d))
      (finSuccIdentityHeadNormVector (n := n) d)) *
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin n) (Fin n) K)) =
    Nat.card (finiteGramOrthogonalGroup
      (finSuccIdentityGramMatrix (n := n) d)) at hrec
  rw [finSuccIdentityHeadOrbit_eq_fixedNorm hchar d hd] at hrec
  simpa using hrec

/-- Literal identity-matrix specialization of the arbitrary-rank recurrence:
the norm-one shell in rank `n+1`, times `|Oₙ(K)|`, is `|Oₙ₊₁(K)|`. -/
theorem natCard_identityFixedNorm_mul_identityOrthogonal_eq
    {K : Type*} [Field K] [Finite K]
    (hchar : ringChar K ≠ 2) :
    Nat.card (finiteGramNormVectors
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) 1) *
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin n) (Fin n) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
  simpa [finSuccIdentityGramMatrix] using
    (natCard_finSuccIdentityFixedNorm_mul_identityOrthogonal_eq
      (n := n) hchar (1 : K) one_ne_zero)

/-- The fully expanded identity-form order recurrence.  It isolates the only
remaining counting input: the lower-dimensional shell cardinalities at the
values `1-z²`. -/
theorem sum_natCard_identityFixedNorm_one_sub_sq_mul_orthogonal_eq
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) :
    (∑ z : K, Nat.card (finiteGramNormVectors
        (1 : Matrix (Fin n) (Fin n) K) (1 - z ^ 2))) *
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin n) (Fin n) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
  have hsplit :
      Nat.card (finiteGramNormVectors
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) 1) =
        ∑ z : K, Nat.card (finiteGramNormVectors
          (1 : Matrix (Fin n) (Fin n) K) (1 - z ^ 2)) := by
    simpa using (natCard_finiteGramNormVectors_finSucc_eq_sum
      (n := n) (1 : K) 1 (1 : Matrix (Fin n) (Fin n) K))
  rw [← hsplit]
  exact natCard_identityFixedNorm_mul_identityOrthogonal_eq
    (n := n) hchar

/-- Closed recurrence step when the rank-`n` identity form has one shell
cardinality at zero and another at every nonzero norm. -/
theorem two_mul_zeroShell_add_nonzeroShell_mul_orthogonal_eq
    {K : Type*} [Field K] [Fintype K]
    (hchar : ringChar K ≠ 2) (a b : ℕ)
    (hzero : Nat.card (finiteGramNormVectors
      (1 : Matrix (Fin n) (Fin n) K) 0) = a)
    (hnonzero : ∀ c : K, c ≠ 0 →
      Nat.card (finiteGramNormVectors
        (1 : Matrix (Fin n) (Fin n) K) c) = b) :
    (2 * a + (Nat.card K - 2) * b) *
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin n) (Fin n) K)) =
      Nat.card (finiteGramOrthogonalGroup
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
  rw [← sum_natCard_finiteGramNormVectors_one_sub_sq_of_constant_nonzero
    (n := n) hchar (1 : Matrix (Fin n) (Fin n) K) a b hzero hnonzero]
  exact sum_natCard_identityFixedNorm_one_sub_sq_mul_orthogonal_eq
    (n := n) hchar

end PositiveDefiniteIntegralLattice
