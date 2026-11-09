import SMSFormula.FiniteOrthogonalGroupSquareClassShellSum

/-!
# Even-to-odd quadratic-shell state transition

An even-dimensional shell family is recorded by its value at zero and its
uniform value away from zero.  Splitting off a leading square gives a single
balanced identity involving the number of square roots of the target.  The
two possible orientations of the zero/nonzero difference then produce the
root-affine and complementary root-affine odd-dimensional states without
natural subtraction.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Shell data with one cardinality at zero and a uniform cardinality at every
nonzero target. -/
def ZeroNonzeroShellCardinality
    {K : Type*} [Field K] [Finite K]
    (B : Matrix (Fin n) (Fin n) K) (zeroCard nonzeroCard : ℕ) : Prop :=
  Nat.card (finiteGramNormVectors B 0) = zeroCard ∧
    ∀ c : K, c ≠ 0 → Nat.card (finiteGramNormVectors B c) = nonzeroCard

/-- The leading-coordinate values whose residual target is zero. -/
def squareShiftZeroFiber
    (K : Type*) [CommRing K] (c : K) :=
  {x : K // c - x ^ 2 = 0}

/-- Vanishing of `c-x²` is literally the square-root fiber over `c`. -/
noncomputable def squareShiftZeroFiberEquivSquareRootFiber
    {K : Type*} [Field K] (c : K) :
    squareShiftZeroFiber K c ≃ squareRootFiber K c where
  toFun x := ⟨x.1, (sub_eq_zero.mp x.2).symm⟩
  invFun x := ⟨x.1, sub_eq_zero.mpr x.2.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

lemma natCard_squareShiftZeroFiber
    {K : Type*} [Field K] [Finite K] (c : K) :
    Nat.card (squareShiftZeroFiber K c) =
      Nat.card (squareRootFiber K c) :=
  Nat.card_congr (squareShiftZeroFiberEquivSquareRootFiber c)

/-- The subtraction-free balanced shell recurrence.  If the tail shell has
cardinality `z` at zero and `u` away from zero, then the next shell `S(c)`
satisfies

`S(c) + (#roots c)u = (#roots c)z + |K|u`.

This retains the complete zero/square/nonsquare information without choosing
a square-class case. -/
theorem natCard_finSuccGramBlock_fixedNorm_add_roots_mul_nonzero_eq
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K) (zeroCard nonzeroCard : ℕ)
    (h : ZeroNonzeroShellCardinality B zeroCard nonzeroCard) (c : K) :
    Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
        Nat.card (squareRootFiber K c) * nonzeroCard =
      Nat.card (squareRootFiber K c) * zeroCard +
        Nat.card K * nonzeroCard := by
  classical
  let p : K → Prop := fun x => c - x ^ 2 = 0
  have hp_card :
      (Finset.univ.filter p).card = Nat.card (squareRootFiber K c) := by
    letI : Finite (squareShiftZeroFiber K c) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype (squareShiftZeroFiber K c) := Fintype.ofFinite _
    let e : ↥(Finset.univ.filter p) ≃
        squareShiftZeroFiber K c :=
      { toFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
        invFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    calc
      (Finset.univ.filter p).card =
          Fintype.card ↥(Finset.univ.filter p) :=
        (Fintype.card_coe _).symm
      _ = Fintype.card (squareShiftZeroFiber K c) := Fintype.card_congr e
      _ = Nat.card (squareShiftZeroFiber K c) := Nat.card_eq_fintype_card.symm
      _ = Nat.card (squareRootFiber K c) := natCard_squareShiftZeroFiber c
  have hpartition :
      (Finset.univ.filter p).card +
          (Finset.univ.filter fun x => ¬p x).card = Nat.card K := by
    simpa [Finset.card_univ, Nat.card_eq_fintype_card] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) p)
  have hsum :
      ∑ x : K, Nat.card (finiteGramNormVectors B (c - x ^ 2)) =
        (Finset.univ.filter p).card * zeroCard +
          (Finset.univ.filter fun x => ¬p x).card * nonzeroCard := by
    calc
      ∑ x : K, Nat.card (finiteGramNormVectors B (c - x ^ 2)) =
          (∑ x ∈ Finset.univ.filter p,
            Nat.card (finiteGramNormVectors B (c - x ^ 2))) +
          ∑ x ∈ Finset.univ.filter (fun x => ¬p x),
            Nat.card (finiteGramNormVectors B (c - x ^ 2)) := by
        symm
        exact Finset.sum_filter_add_sum_filter_not Finset.univ p _
      _ = (Finset.univ.filter p).card * zeroCard +
          (Finset.univ.filter fun x => ¬p x).card * nonzeroCard := by
        rw [Finset.sum_const_nat (fun x hx => by
          have hx0 : c - x ^ 2 = 0 := (Finset.mem_filter.mp hx).2
          simpa [hx0] using h.1),
          Finset.sum_const_nat (fun x hx =>
            h.2 (c - x ^ 2) (Finset.mem_filter.mp hx).2)]
  rw [natCard_finiteGramNormVectors_finSucc_eq_sum]
  simp only [one_mul]
  rw [hsum, ← hp_card, ← hpartition, Nat.add_mul]
  ac_rfl

/-- If the zero shell exceeds the uniform nonzero shell by `correction`, the
next shell family is root-affine. -/
theorem rootAffineShellCardinality_finSuccGramBlock_of_zero_eq_nonzero_add
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K)
    (zeroCard nonzeroCard correction : ℕ)
    (h : ZeroNonzeroShellCardinality B zeroCard nonzeroCard)
    (hdiff : zeroCard = nonzeroCard + correction) :
    RootAffineShellCardinality (finSuccGramBlock 1 B) 1
      (Nat.card K * nonzeroCard) correction := by
  intro c
  simp only [one_mul]
  have hbalanced :=
    natCard_finSuccGramBlock_fixedNorm_add_roots_mul_nonzero_eq
      B zeroCard nonzeroCard h c
  have hcancel :
      Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
          Nat.card (squareRootFiber K c) * nonzeroCard =
        (Nat.card K * nonzeroCard +
            correction * Nat.card (squareRootFiber K c)) +
          Nat.card (squareRootFiber K c) * nonzeroCard := by
    calc
      _ = Nat.card (squareRootFiber K c) * zeroCard +
          Nat.card K * nonzeroCard := hbalanced
      _ = _ := by rw [hdiff]; ring
  exact Nat.add_right_cancel hcancel

/-- If the uniform nonzero shell exceeds the zero shell by `correction`, the
next shell family is root-coaffine. -/
theorem rootCoaffineShellCardinality_finSuccGramBlock_of_nonzero_eq_zero_add
    {K : Type*} [Field K] [Fintype K]
    (B : Matrix (Fin n) (Fin n) K)
    (zeroCard nonzeroCard correction : ℕ)
    (h : ZeroNonzeroShellCardinality B zeroCard nonzeroCard)
    (hdiff : nonzeroCard = zeroCard + correction) :
    RootCoaffineShellCardinality (finSuccGramBlock 1 B) 1
      (Nat.card K * nonzeroCard) correction := by
  intro c
  simp only [one_mul]
  have hbalanced :=
    natCard_finSuccGramBlock_fixedNorm_add_roots_mul_nonzero_eq
      B zeroCard nonzeroCard h c
  have hcancel :
      Nat.card (squareRootFiber K c) * zeroCard +
          (Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
            correction * Nat.card (squareRootFiber K c)) =
        Nat.card (squareRootFiber K c) * zeroCard +
          Nat.card K * nonzeroCard := by
    calc
      _ = Nat.card (finiteGramNormVectors (finSuccGramBlock 1 B) c) +
          Nat.card (squareRootFiber K c) * nonzeroCard := by
        rw [hdiff]
        ring
      _ = _ := hbalanced
  exact Nat.add_left_cancel hcancel

end PositiveDefiniteIntegralLattice
