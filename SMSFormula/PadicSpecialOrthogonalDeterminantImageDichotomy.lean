import SMSFormula.PadicSpecialOrthogonalDeterminantImageTransport

/-!
# The intrinsic p-adic orientation-image dichotomy

Every value of the integral p-adic stabilizer determinant character has
square one, hence is `1` or `-1`.  Its actual image is therefore finite of
cardinality at most two.  The cardinal is two exactly when an integral local
stabilizer element of determinant `-1` exists, and is one exactly when every
integral local stabilizer determinant is one.

These are criteria, not an assertion that either case holds for a particular
lattice.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix Matrix.Norms.Operator NNReal Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The two p-adic integral unit signs are distinct. -/
theorem neg_one_ne_one_padicIntUnits (p : ℕ) [Fact (Nat.Prime p)] :
    (-1 : ℤ_[p]ˣ) ≠ 1 := by
  intro h
  have hval := congrArg Units.val h
  norm_num at hval

/-- Every element of the actual integral p-adic determinant image is one of
the two signs. -/
theorem localPadicLatticeStabilizerDeterminantRange_eq_one_or_neg_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (u : (L.localPadicLatticeStabilizerDeterminant p).range) :
    (u : ℤ_[p]ˣ) = 1 ∨ (u : ℤ_[p]ˣ) = -1 := by
  rcases u.2 with ⟨g, hg⟩
  have hsq :=
    congrArg Units.val
      (L.localPadicLatticeStabilizerDeterminant_sq p g)
  rcases sq_eq_one_iff.mp hsq with hone | hneg
  · left
    exact hg.symm.trans (Units.ext hone)
  · right
    exact hg.symm.trans (Units.ext hneg)

/-- If `-1` does not occur in the actual determinant image, every image
element is one. -/
theorem localPadicLatticeStabilizerDeterminantRange_eq_one_of_neg_one_not_mem
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hneg :
      (-1 : ℤ_[p]ˣ) ∉
        (L.localPadicLatticeStabilizerDeterminant p).range)
    (u : (L.localPadicLatticeStabilizerDeterminant p).range) :
    u = 1 := by
  rcases
      L.localPadicLatticeStabilizerDeterminantRange_eq_one_or_neg_one p u with
    hu | hu
  · exact Subtype.ext hu
  · exfalso
    apply hneg
    rw [← hu]
    exact u.property

/-- If both signs occur, the actual determinant image is equivalent to
`Bool`. -/
def localPadicLatticeStabilizerDeterminantRangeEquivBool
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hneg :
      (-1 : ℤ_[p]ˣ) ∈
        (L.localPadicLatticeStabilizerDeterminant p).range) :
    (L.localPadicLatticeStabilizerDeterminant p).range ≃ Bool := by
  classical
  let neg :
      (L.localPadicLatticeStabilizerDeterminant p).range :=
    ⟨-1, hneg⟩
  have hne : neg ≠ 1 := by
    intro h
    apply neg_one_ne_one_padicIntUnits p
    simpa [neg] using congrArg Subtype.val h
  refine
    { toFun := fun u => if u = 1 then false else true
      invFun := fun b => if b then neg else 1
      left_inv := ?_
      right_inv := ?_ }
  · intro u
    rcases
        L.localPadicLatticeStabilizerDeterminantRange_eq_one_or_neg_one p u with
      hu | hu
    · have huSub : u = 1 := Subtype.ext hu
      subst u
      simp
    · have huSub : u = neg := by
        apply Subtype.ext
        simpa [neg] using hu
      subst u
      simp [hne]
  · intro b
    cases b <;> simp [hne]

/-- If the negative sign does not occur, the actual determinant image is
equivalent to a singleton. -/
def localPadicLatticeStabilizerDeterminantRangeEquivUnit
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hneg :
      (-1 : ℤ_[p]ˣ) ∉
        (L.localPadicLatticeStabilizerDeterminant p).range) :
    (L.localPadicLatticeStabilizerDeterminant p).range ≃ Unit where
  toFun _ := ()
  invFun _ := 1
  left_inv u :=
    (L.localPadicLatticeStabilizerDeterminantRange_eq_one_of_neg_one_not_mem
      p hneg u).symm
  right_inv b := by
    cases b
    rfl

/-- The intrinsic integral p-adic determinant image is finite. -/
noncomputable instance localPadicLatticeStabilizerDeterminantRange_fintype
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Fintype (L.localPadicLatticeStabilizerDeterminant p).range := by
  classical
  by_cases hneg :
      (-1 : ℤ_[p]ˣ) ∈
        (L.localPadicLatticeStabilizerDeterminant p).range
  · exact Fintype.ofEquiv Bool
      (L.localPadicLatticeStabilizerDeterminantRangeEquivBool p hneg).symm
  · exact Fintype.ofEquiv Unit
      (L.localPadicLatticeStabilizerDeterminantRangeEquivUnit p hneg).symm

/-- If `-1` occurs, the intrinsic determinant image has cardinality two. -/
theorem natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_of_neg_one_mem
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hneg :
      (-1 : ℤ_[p]ˣ) ∈
        (L.localPadicLatticeStabilizerDeterminant p).range) :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 2 := by
  calc
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range =
        Nat.card Bool :=
      Nat.card_congr
        (L.localPadicLatticeStabilizerDeterminantRangeEquivBool p hneg)
    _ = 2 := by simp

/-- If `-1` does not occur, the intrinsic determinant image has cardinality
one. -/
theorem natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_of_neg_one_not_mem
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hneg :
      (-1 : ℤ_[p]ˣ) ∉
        (L.localPadicLatticeStabilizerDeterminant p).range) :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 1 := by
  calc
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range =
        Nat.card Unit :=
      Nat.card_congr
        (L.localPadicLatticeStabilizerDeterminantRangeEquivUnit p hneg)
    _ = 1 := by simp

/-- The intrinsic determinant image has cardinality at most two. -/
theorem natCard_localPadicLatticeStabilizerDeterminant_range_le_two
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range ≤ 2 := by
  classical
  by_cases hneg :
      (-1 : ℤ_[p]ˣ) ∈
        (L.localPadicLatticeStabilizerDeterminant p).range
  · rw [
      L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_of_neg_one_mem
        p hneg]
  · rw [
      L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_of_neg_one_not_mem
        p hneg]
    omega

/-- The intrinsic determinant image has cardinality two exactly when it
contains the negative sign. -/
theorem natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 2 ↔
      (-1 : ℤ_[p]ˣ) ∈
        (L.localPadicLatticeStabilizerDeterminant p).range := by
  classical
  constructor
  · intro hcard
    by_contra hneg
    have hone :=
      L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_of_neg_one_not_mem
        p hneg
    omega
  · exact
      L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_of_neg_one_mem
        p

/-- The intrinsic determinant image has cardinality one exactly when it does
not contain the negative sign. -/
theorem natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 1 ↔
      (-1 : ℤ_[p]ˣ) ∉
        (L.localPadicLatticeStabilizerDeterminant p).range := by
  classical
  constructor
  · intro hcard hneg
    have htwo :=
      L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_of_neg_one_mem
        p hneg
    omega
  · exact
      L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_of_neg_one_not_mem
        p

/-- Membership of `-1` in the actual image is the literal existence of an
integral local stabilizer element of determinant `-1`. -/
theorem neg_one_mem_localPadicLatticeStabilizerDeterminant_range_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (-1 : ℤ_[p]ˣ) ∈
        (L.localPadicLatticeStabilizerDeterminant p).range ↔
      ∃ g : L.localPadicLatticeStabilizerSubgroup p,
        L.localPadicLatticeStabilizerDeterminant p g = -1 :=
  MonoidHom.mem_range

/-- The intrinsic determinant image has cardinality two exactly when an
orientation-reversing integral local stabilizer exists. -/
theorem
    natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_iff_exists_det_neg_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 2 ↔
      ∃ g : L.localPadicLatticeStabilizerSubgroup p,
        L.localPadicLatticeStabilizerDeterminant p g = -1 :=
  (L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_two_iff p).trans
    (L.neg_one_mem_localPadicLatticeStabilizerDeterminant_range_iff p)

/-- Absence of the negative sign is equivalent to every integral local
stabilizer determinant being one. -/
theorem neg_one_not_mem_localPadicLatticeStabilizerDeterminant_range_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (-1 : ℤ_[p]ˣ) ∉
        (L.localPadicLatticeStabilizerDeterminant p).range ↔
      ∀ g : L.localPadicLatticeStabilizerSubgroup p,
        L.localPadicLatticeStabilizerDeterminant p g = 1 := by
  constructor
  · intro hneg g
    have hsq :=
      congrArg Units.val
        (L.localPadicLatticeStabilizerDeterminant_sq p g)
    rcases sq_eq_one_iff.mp hsq with hone | hminus
    · exact Units.ext hone
    · exfalso
      apply hneg
      exact ⟨g, Units.ext hminus⟩
  · intro hall hneg
    rcases hneg with ⟨g, hg⟩
    exact neg_one_ne_one_padicIntUnits p (hg.symm.trans (hall g))

/-- The intrinsic determinant image has cardinality one exactly when every
integral local stabilizer determinant is one. -/
theorem
    natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_iff_forall_det_one
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerDeterminant p).range = 1 ↔
      ∀ g : L.localPadicLatticeStabilizerSubgroup p,
        L.localPadicLatticeStabilizerDeterminant p g = 1 :=
  (L.natCard_localPadicLatticeStabilizerDeterminant_range_eq_one_iff p).trans
    (L.neg_one_not_mem_localPadicLatticeStabilizerDeterminant_range_iff p)

end PositiveDefiniteIntegralLattice
