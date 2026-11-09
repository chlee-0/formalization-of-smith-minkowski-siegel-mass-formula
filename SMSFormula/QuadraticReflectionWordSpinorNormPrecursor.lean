import SMSFormula.QuadraticCartanDieudonneParity
import SMSFormula.RationalSquareClassLocalGlobal

/-!
# Reflection-word precursor for the spinor norm

This file attaches to a certified reflection word the product, modulo squares,
of the quadratic values of its reflection vectors.  The construction is
purely presentation-level: it proves the list and reflection-pair formulas and
shows that every determinant-one isometry has a bounded pair presentation
carrying such a square class.

The needed mathematical theorem is stated as the hypothesis
`SpinorNormFactorizationIndependent`: two reflection words evaluating to the
same isometry must have the same square-class product.  Conditional on that
statement, the chosen value is independent of the word, preserves the
identity, and is multiplicative for composition.
-/

noncomputable section

open Module

namespace QuadraticMap.ReflectionWord

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable (Q : QuadraticForm K M)

/-- The square class of the nonzero quadratic value of an anisotropic
reflection vector. -/
def quadraticValueSquareClass (x : Q.AnisotropicVector) : Rat.SquareClass K :=
  ((Units.mk0 (Q x) x.property : Kˣ) : Rat.SquareClass K)

/-- The product of the quadratic-value square classes in a reflection word. -/
def squareClassProduct (xs : Q.ReflectionWord) : Rat.SquareClass K :=
  (xs.map (quadraticValueSquareClass Q)).prod

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem squareClassProduct_nil : squareClassProduct Q [] = 1 :=
  rfl

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem squareClassProduct_cons (x : Q.AnisotropicVector)
    (xs : Q.ReflectionWord) :
    squareClassProduct Q (x :: xs) =
      quadraticValueSquareClass Q x * squareClassProduct Q xs :=
  rfl

omit [CharZero K] [FiniteDimensional K M] in
theorem squareClassProduct_append (xs ys : Q.ReflectionWord) :
    squareClassProduct Q (xs ++ ys) =
      squareClassProduct Q xs * squareClassProduct Q ys := by
  simp [squareClassProduct]

/-- The two-factor square-class contribution of a reflection pair. -/
def reflectionPairSquareClass (p : ReflectionPair Q) : Rat.SquareClass K :=
  quadraticValueSquareClass Q p.1 * quadraticValueSquareClass Q p.2

/-- The square-class product of a list of consecutive reflection pairs. -/
def reflectionPairSquareClassProduct (ps : List (ReflectionPair Q)) :
    Rat.SquareClass K :=
  (ps.map (reflectionPairSquareClass Q)).prod

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem reflectionPairSquareClassProduct_nil :
    reflectionPairSquareClassProduct Q [] = 1 :=
  rfl

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem reflectionPairSquareClassProduct_cons (p : ReflectionPair Q)
    (ps : List (ReflectionPair Q)) :
    reflectionPairSquareClassProduct Q (p :: ps) =
      reflectionPairSquareClass Q p *
        reflectionPairSquareClassProduct Q ps :=
  rfl

omit [CharZero K] [FiniteDimensional K M] in
/-- Flattening reflection pairs does not change their quadratic-value
square-class product. -/
theorem squareClassProduct_flattenPairs (ps : List (ReflectionPair Q)) :
    squareClassProduct Q (flattenPairs Q ps) =
      reflectionPairSquareClassProduct Q ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [flattenPairs_cons, squareClassProduct_cons,
        reflectionPairSquareClassProduct_cons, reflectionPairSquareClass, ih]
      rw [mul_assoc]

/-- Square classes supplied by arbitrary reflection-word presentations of an
isometry.  This set is nonempty by Cartan--Dieudonne; this file does not prove
that it is a singleton. -/
def squareClassValues (g : Q.IsometryEquiv Q) : Set (Rat.SquareClass K) :=
  {c | ∃ xs : Q.ReflectionWord,
    eval Q xs = g ∧ squareClassProduct Q xs = c}

/-- Square classes supplied by consecutive-pair presentations of an
isometry. -/
def reflectionPairSquareClassValues (g : Q.IsometryEquiv Q) :
    Set (Rat.SquareClass K) :=
  {c | ∃ ps : List (ReflectionPair Q),
    eval Q (flattenPairs Q ps) = g ∧
      reflectionPairSquareClassProduct Q ps = c}

/-- Every isometry has at least one reflection-word square-class value. -/
theorem squareClassValues_nonempty
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q) :
    (squareClassValues Q g).Nonempty := by
  obtain ⟨xs, hxs, -⟩ := exists_reflectionWord_eval_eq Q hQ g
  exact ⟨squareClassProduct Q xs, xs, hxs, rfl⟩

omit [CharZero K] [FiniteDimensional K M] in
/-- A bounded reflection-pair value is in particular a reflection-word
value. -/
theorem reflectionPairSquareClassValues_subset_squareClassValues
    (g : Q.IsometryEquiv Q) :
    reflectionPairSquareClassValues Q g ⊆ squareClassValues Q g := by
  intro c hc
  obtain ⟨ps, hps, hc⟩ := hc
  refine ⟨flattenPairs Q ps, hps, ?_⟩
  rw [squareClassProduct_flattenPairs, hc]

/-- Every determinant-one isometry of a nondegenerate finite-dimensional form
has a bounded reflection-pair square-class representative. -/
theorem reflectionPairSquareClassValues_nonempty_of_det_eq_one
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q)
    (hdet : LinearMap.det g.toLinearEquiv.toLinearMap = 1) :
    (reflectionPairSquareClassValues Q g).Nonempty := by
  obtain ⟨ps, hps, hlen⟩ := exists_reflectionPairs_eval_eq Q hQ g hdet
  exact ⟨reflectionPairSquareClassProduct Q ps, ps, hps, rfl⟩

/-- The determinant-one representative can be chosen with at most the ambient
finrank many reflection pairs. -/
theorem exists_bounded_reflectionPairs_squareClassValue
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q)
    (hdet : LinearMap.det g.toLinearEquiv.toLinearMap = 1) :
    ∃ ps : List (ReflectionPair Q),
      eval Q (flattenPairs Q ps) = g ∧
        ps.length ≤ finrank K M ∧
          reflectionPairSquareClassProduct Q ps ∈
            reflectionPairSquareClassValues Q g := by
  obtain ⟨ps, hps, hlen⟩ := exists_reflectionPairs_eval_eq Q hQ g hdet
  exact ⟨ps, hps, hlen, ps, hps, rfl⟩

/-- The exact independence statement needed for the determinant-one
reflection-pair construction used on `SO`. -/
def ReflectionPairSpinorNormFactorizationIndependent : Prop :=
  ∀ ps qs : List (ReflectionPair Q),
    eval Q (flattenPairs Q ps) = eval Q (flattenPairs Q qs) →
      reflectionPairSquareClassProduct Q ps =
        reflectionPairSquareClassProduct Q qs

omit [CharZero K] [FiniteDimensional K M] in
/-- Pair-factorization independence is exactly singleton-valuedness of every
pair-presentation fiber. -/
theorem reflectionPairSpinorNormFactorizationIndependent_iff_subsingleton_values :
    ReflectionPairSpinorNormFactorizationIndependent Q ↔
      ∀ g : Q.IsometryEquiv Q,
        (reflectionPairSquareClassValues Q g).Subsingleton := by
  constructor
  · intro h g a ha b hb
    obtain ⟨ps, hps, hpa⟩ := ha
    obtain ⟨qs, hqs, hqb⟩ := hb
    rw [← hpa, ← hqb]
    exact h ps qs (hps.trans hqs.symm)
  · intro h ps qs hpq
    apply h (eval Q (flattenPairs Q ps))
    · exact ⟨ps, rfl, rfl⟩
    · exact ⟨qs, hpq.symm, rfl⟩

/-- The exact independence-of-factorization statement needed to descend the
reflection-word product to the isometry group. -/
def SpinorNormFactorizationIndependent : Prop :=
  ∀ xs ys : Q.ReflectionWord,
    eval Q xs = eval Q ys →
      squareClassProduct Q xs = squareClassProduct Q ys

omit [CharZero K] [FiniteDimensional K M] in
/-- Full reflection-word independence implies the minimal pair independence
needed on determinant-one isometries. -/
theorem SpinorNormFactorizationIndependent.reflectionPairs
    (hind : SpinorNormFactorizationIndependent Q) :
    ReflectionPairSpinorNormFactorizationIndependent Q := by
  intro ps qs hpq
  rw [← squareClassProduct_flattenPairs, ← squareClassProduct_flattenPairs]
  exact hind _ _ hpq

omit [CharZero K] [FiniteDimensional K M] in
/-- Factorization independence is exactly singleton-valuedness of every
presentation fiber. -/
theorem spinorNormFactorizationIndependent_iff_subsingleton_values :
    SpinorNormFactorizationIndependent Q ↔
      ∀ g : Q.IsometryEquiv Q, (squareClassValues Q g).Subsingleton := by
  constructor
  · intro h g a ha b hb
    obtain ⟨xs, hxs, hxa⟩ := ha
    obtain ⟨ys, hys, hyb⟩ := hb
    rw [← hxa, ← hyb]
    exact h xs ys (hxs.trans hys.symm)
  · intro h xs ys hxy
    apply h (eval Q xs)
    · exact ⟨xs, rfl, rfl⟩
    · exact ⟨ys, hxy.symm, rfl⟩

/-- A choice of reflection word for each isometry.  Its associated value is
canonical only after factorization independence is supplied. -/
noncomputable def chosenReflectionWord
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q) :
    Q.ReflectionWord :=
  Classical.choose (exists_reflectionWord_eval_eq Q hQ g)

theorem eval_chosenReflectionWord
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q) :
    eval Q (chosenReflectionWord Q hQ g) = g :=
  (Classical.choose_spec (exists_reflectionWord_eval_eq Q hQ g)).1

/-- The chosen reflection-word square class. -/
noncomputable def spinorNormCandidate
    (hQ : Q.associated.Nondegenerate) (g : Q.IsometryEquiv Q) :
    Rat.SquareClass K :=
  squareClassProduct Q (chosenReflectionWord Q hQ g)

/-- Under factorization independence, the chosen candidate agrees with every
reflection-word presentation. -/
theorem spinorNormCandidate_eq_squareClassProduct
    (hQ : Q.associated.Nondegenerate)
    (hind : SpinorNormFactorizationIndependent Q)
    (g : Q.IsometryEquiv Q) (xs : Q.ReflectionWord)
    (hxs : eval Q xs = g) :
    spinorNormCandidate Q hQ g = squareClassProduct Q xs := by
  exact hind _ _ ((eval_chosenReflectionWord Q hQ g).trans hxs.symm)

/-- Under factorization independence, the candidate sends the identity
isometry to the trivial square class. -/
theorem spinorNormCandidate_refl
    (hQ : Q.associated.Nondegenerate)
    (hind : SpinorNormFactorizationIndependent Q) :
    spinorNormCandidate Q hQ (.refl Q) = 1 := by
  rw [spinorNormCandidate_eq_squareClassProduct Q hQ hind (.refl Q) [] rfl]
  exact squareClassProduct_nil Q

/-- Under factorization independence, the candidate is multiplicative for
composition of quadratic isometries.  This is the homomorphism law before
transporting `IsometryEquiv.trans` to a concrete orthogonal matrix group. -/
theorem spinorNormCandidate_trans
    (hQ : Q.associated.Nondegenerate)
    (hind : SpinorNormFactorizationIndependent Q)
    (g h : Q.IsometryEquiv Q) :
    spinorNormCandidate Q hQ (g.trans h) =
      spinorNormCandidate Q hQ g * spinorNormCandidate Q hQ h := by
  rw [spinorNormCandidate_eq_squareClassProduct Q hQ hind (g.trans h)
    (chosenReflectionWord Q hQ g ++ chosenReflectionWord Q hQ h)]
  · exact squareClassProduct_append Q _ _
  · rw [eval_append, eval_chosenReflectionWord, eval_chosenReflectionWord]

/-- Under factorization independence, a determinant-one isometry has a
bounded reflection-pair presentation computing its chosen spinor-norm
candidate. -/
theorem exists_reflectionPairs_spinorNormCandidate_eq
    (hQ : Q.associated.Nondegenerate)
    (hind : SpinorNormFactorizationIndependent Q)
    (g : Q.IsometryEquiv Q)
    (hdet : LinearMap.det g.toLinearEquiv.toLinearMap = 1) :
    ∃ ps : List (ReflectionPair Q),
      eval Q (flattenPairs Q ps) = g ∧
        ps.length ≤ finrank K M ∧
          spinorNormCandidate Q hQ g =
            reflectionPairSquareClassProduct Q ps := by
  obtain ⟨ps, hps, hlen⟩ := exists_reflectionPairs_eval_eq Q hQ g hdet
  refine ⟨ps, hps, hlen, ?_⟩
  rw [spinorNormCandidate_eq_squareClassProduct Q hQ hind g
    (flattenPairs Q ps) hps, squareClassProduct_flattenPairs]

end QuadraticMap.ReflectionWord
