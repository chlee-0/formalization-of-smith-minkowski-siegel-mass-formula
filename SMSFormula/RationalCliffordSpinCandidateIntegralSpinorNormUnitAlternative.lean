import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange

/-!
# The unit alternative in integral reflection alignment

For an odd prime, two integral vectors of the same unit norm in a symmetric
`p`-adic lattice have a unit-norm difference or a unit-norm sum.  Consequently
one of those two vectors supplies the certified integral reflection used in
the elementary integral Cartan--Dieudonne alignment step.

This is the first arithmetic step toward
`CliffordSpinCandidateIntegralSpinorNormUnitValuedAt`.  It does not carry
out induction on the integral orthogonal complement and makes no use of
integral Spin lifting, the covering degree, or Haar comparison.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The quadratic value of an integral vector for the displayed p-adic form
matrix. -/
def localPadicIntegralFormValue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) : ℤ_[p] :=
  x ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) x

/-- The displayed integral quadratic value becomes the existing field-valued
Gram quadratic value after scalar extension. -/
theorem coe_localPadicIntegralFormValue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x : Fin n → ℤ_[p]) :
    ((L.localPadicIntegralFormValue p x : ℤ_[p]) : ℚ_[p]) =
      gramQuadraticValue (L.pairingMatrix_padicField p)
        (fun i ↦ (x i : ℚ_[p])) := by
  simp [localPadicIntegralFormValue, gramQuadraticValue,
    pairingMatrix_padicField, Matrix.mulVec, dotProduct]

/-- In a local ring, a unit sum has a unit summand. -/
theorem isUnit_left_or_right_of_isUnit_add
    {R : Type*} [CommRing R] [IsLocalRing R]
    {a b : R} (hab : IsUnit (a + b)) :
    IsUnit a ∨ IsUnit b := by
  by_contra h
  push_neg at h
  have ha : a ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact h.1
  have hb : b ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact h.2
  have hab' : a + b ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).add_mem ha hb
  rw [IsLocalRing.mem_maximalIdeal] at hab'
  exact hab' hab

/-- The difference and sum quadratic values add to four times the common
value.  This is the integral Gram-matrix form of the alignment identity. -/
theorem localPadicIntegralFormValue_sub_add_sum_of_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (x y : Fin n → ℤ_[p])
    (hxy : L.localPadicIntegralFormValue p y =
      L.localPadicIntegralFormValue p x) :
    L.localPadicIntegralFormValue p (y - x) +
        L.localPadicIntegralFormValue p (y + x) =
      4 * L.localPadicIntegralFormValue p x := by
  let A := L.pairingMatrix_padic p
  have hA : A.IsSymm := L.form_symm.map (Int.castRingHom ℤ_[p])
  have hbilin :
      x ⬝ᵥ Matrix.mulVec A y = y ⬝ᵥ Matrix.mulVec A x := by
    rw [Matrix.dotProduct_mulVec]
    have hvec : Matrix.vecMul x A = Matrix.mulVec A x := by
      funext i
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hA.apply i j]
      ring
    rw [hvec, dotProduct_comm]
  change
    y ⬝ᵥ Matrix.mulVec A y = x ⬝ᵥ Matrix.mulVec A x at hxy
  change
    ((y - x) ⬝ᵥ Matrix.mulVec A (y - x)) +
        ((y + x) ⬝ᵥ Matrix.mulVec A (y + x)) =
      4 * (x ⬝ᵥ Matrix.mulVec A x)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub,
    sub_dotProduct, dotProduct_add, add_dotProduct]
  rw [hbilin, hxy]
  ring

/-- At an odd prime, equal unit norms force the difference norm or the sum
norm to be a unit. -/
theorem isUnit_localPadicIntegralFormValue_sub_or_add_of_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2)
    (x y : Fin n → ℤ_[p])
    (hxy : L.localPadicIntegralFormValue p y =
      L.localPadicIntegralFormValue p x)
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    IsUnit (L.localPadicIntegralFormValue p (y - x)) ∨
      IsUnit (L.localPadicIntegralFormValue p (y + x)) := by
  have htwo : IsUnit (2 : ℤ_[p]) :=
    two_isUnit_padicInt_of_ne_two p hpodd
  have hfour : IsUnit (4 : ℤ_[p]) := by
    convert htwo.mul htwo using 1
    norm_num
  have hsum : IsUnit
      (L.localPadicIntegralFormValue p (y - x) +
        L.localPadicIntegralFormValue p (y + x)) := by
    rw [L.localPadicIntegralFormValue_sub_add_sum_of_eq p x y hxy]
    exact hfour.mul hx
  exact isUnit_left_or_right_of_isUnit_add hsum

/-- The unit alternative immediately produces a certified integral
reflection in the difference or in the sum vector. -/
theorem exists_localPadicIntegralReflectionData_sub_or_add_of_same_unit_norm
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2)
    (x y : Fin n → ℤ_[p])
    (hxy : L.localPadicIntegralFormValue p y =
      L.localPadicIntegralFormValue p x)
    (hx : IsUnit (L.localPadicIntegralFormValue p x)) :
    (∃ d : LocalPadicIntegralReflectionData L p,
        d.vector = y - x ∧
          IsUnit (L.localPadicIntegralFormValue p d.vector)) ∨
      (∃ d : LocalPadicIntegralReflectionData L p,
        d.vector = y + x ∧
          IsUnit (L.localPadicIntegralFormValue p d.vector)) := by
  rcases L.isUnit_localPadicIntegralFormValue_sub_or_add_of_eq
      p hpodd x y hxy hx with hsub | hadd
  · left
    let d := LocalPadicIntegralReflectionData.ofNormIsUnit L p (y - x) hsub
    exact ⟨d, rfl, hsub⟩
  · right
    let d := LocalPadicIntegralReflectionData.ofNormIsUnit L p (y + x) hadd
    exact ⟨d, rfl, hadd⟩

end PositiveDefiniteIntegralLattice
