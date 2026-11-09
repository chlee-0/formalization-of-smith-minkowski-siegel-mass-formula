import SMSFormula.Applications.Unimodular.Dyadic
import SMSFormula.Applications.Unimodular.Seeds

/-!
# E8 dyadic local-factor bridge

This file specializes the native depth-three dyadic bridge to the concrete E8
seed.  It does not evaluate the finite quotient count; it only isolates the
exact count value needed to obtain the proposed native local factor.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The integral quadratic polynomial `Q_E8` with `2 * Q_E8 = q_E8`.
It is defined over an arbitrary commutative ring so that the same expression can
be used over `ℤ`, `ZMod 2`, and `ZMod 4` without dividing by two in a residue
ring. -/
def e8QuadraticPolynomial {R : Type*} [CommRing R] (x : Fin 8 → R) : R :=
  x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 - x 1 * x 2 + x 2 ^ 2 -
    x 2 * x 3 - x 2 * x 7 + x 3 ^ 2 - x 3 * x 4 + x 4 ^ 2 -
    x 4 * x 5 + x 5 ^ 2 - x 5 * x 6 + x 6 ^ 2 + x 7 ^ 2

/-- Ring maps commute with the E8 quadratic polynomial. -/
theorem map_e8QuadraticPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Fin 8 → R) :
    f (e8QuadraticPolynomial x) = e8QuadraticPolynomial (fun i => f (x i)) := by
  simp [e8QuadraticPolynomial]

/-- The polar bilinear form attached to `Q_E8` over `𝔽₂`.  The square terms of
`Q_E8` do not contribute in characteristic two, so this records only the seven
E8 edge terms. -/
def e8PolarBilinear (v w : Fin 8 → ZMod 2) : ZMod 2 :=
  v 0 * w 1 + v 1 * w 0 + v 1 * w 2 + v 2 * w 1 +
  v 2 * w 3 + v 3 * w 2 + v 2 * w 7 + v 7 * w 2 +
  v 3 * w 4 + v 4 * w 3 + v 4 * w 5 + v 5 * w 4 +
  v 5 * w 6 + v 6 * w 5

/-- The E8 polar form is the polarization of `Q_E8` over `𝔽₂`. -/
theorem e8PolarBilinear_eq_quadratic_add
    (v w : Fin 8 → ZMod 2) :
    e8PolarBilinear v w =
      e8QuadraticPolynomial (v + w) +
        e8QuadraticPolynomial v + e8QuadraticPolynomial w := by
  simp only [e8PolarBilinear, e8QuadraticPolynomial, Pi.add_apply]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hneg (entry : ZMod 2) : -entry = entry := by
    fin_cases entry <;> decide
  simp [h2, sub_eq_add_neg, hneg]

/-- The standard split quadratic polynomial on four hyperbolic planes in
characteristic two. -/
def e8SplitQuadraticPolynomial {R : Type*} [CommRing R] (x : Fin 8 → R) : R :=
  x 0 * x 1 + x 2 * x 3 + x 4 * x 5 + x 6 * x 7

/-- Ring maps commute with the standard split quadratic polynomial. -/
theorem map_e8SplitQuadraticPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Fin 8 → R) :
    f (e8SplitQuadraticPolynomial x) =
      e8SplitQuadraticPolynomial (fun i => f (x i)) := by
  simp [e8SplitQuadraticPolynomial]

/-- The explicit hyperbolic-basis certificate matrix for the E8 seed.
Its columns are the basis vectors in seed coordinates. -/
def e8HyperbolicBasisMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 1, 0, 1, 1, 0, 1, 1;
    0, 0, 1, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 1, 1;
    0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 1, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

/-- The hyperbolic-basis matrix reduced modulo two. -/
def e8HyperbolicBasisMatrixModTwo : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  e8HyperbolicBasisMatrix.map (Int.castRingHom (ZMod 2))

/-- An explicit inverse over `𝔽₂` for the hyperbolic-basis matrix. -/
def e8HyperbolicBasisMatrixInvModTwo : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 1, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1;
    1, 1, 1, 1, 0, 1, 0, 0;
    1, 0, 1, 1, 0, 1, 0, 0;
    0, 1, 0, 0, 1, 1, 1, 1;
    0, 1, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

/-- The explicit inverse is a right inverse for the E8 hyperbolic-basis matrix
over `𝔽₂`. -/
theorem e8HyperbolicBasisMatrix_mul_inv_zmod_two :
    e8HyperbolicBasisMatrixModTwo * e8HyperbolicBasisMatrixInvModTwo = 1 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8HyperbolicBasisMatrixModTwo, e8HyperbolicBasisMatrix,
      e8HyperbolicBasisMatrixInvModTwo, Matrix.mul_apply, Fin.sum_univ_eight, h11]

/-- The explicit inverse is a left inverse for the E8 hyperbolic-basis matrix
over `𝔽₂`. -/
theorem e8HyperbolicBasisMatrix_inv_mul_zmod_two :
    e8HyperbolicBasisMatrixInvModTwo * e8HyperbolicBasisMatrixModTwo = 1 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8HyperbolicBasisMatrixModTwo, e8HyperbolicBasisMatrix,
      e8HyperbolicBasisMatrixInvModTwo, Matrix.mul_apply, Fin.sum_univ_eight, h11]

/-- The hyperbolic-basis certificate: over `𝔽₂`, the explicit matrix
transports the E8 polynomial `Q_E8` to the standard split polynomial
`x₀x₁ + x₂x₃ + x₄x₅ + x₆x₇`. -/
theorem e8QuadraticPolynomial_hyperbolicBasis_mulVec_zmod_two
    (x : Fin 8 → ZMod 2) :
    e8QuadraticPolynomial
        (e8HyperbolicBasisMatrixModTwo.mulVec x) =
      e8SplitQuadraticPolynomial x := by
  have hvec :
      e8HyperbolicBasisMatrixModTwo.mulVec x =
        fun i : Fin 8 =>
          match i with
          | 0 => x 0 + x 1 + x 3 + x 4 + x 6 + x 7
          | 1 => x 2 + x 3
          | 2 => x 0 + x 5 + x 6 + x 7
          | 3 => x 1 + x 7
          | 4 => x 2 + x 3 + x 5 + x 6 + x 7
          | 5 => x 4 + x 5 + x 7
          | 6 => x 6 + x 7
          | 7 => x 7 := by
    funext i
    fin_cases i <;>
      simp [e8HyperbolicBasisMatrixModTwo, e8HyperbolicBasisMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_eight]
  rw [hvec]
  have hsquare (a : ZMod 2) : a ^ 2 = a := by
    fin_cases a <;> decide
  simp only [e8QuadraticPolynomial, e8SplitQuadraticPolynomial]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (3 : ZMod 2) = 1 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  simp [hsquare, h2, h3, h4]

/-- The inverse hyperbolic-basis matrix rewrites the E8 polynomial as
the split polynomial over `𝔽₂`. -/
theorem e8QuadraticPolynomial_eq_split_hyperbolicBasisInv_mulVec_zmod_two
    (x : Fin 8 → ZMod 2) :
    e8QuadraticPolynomial x =
      e8SplitQuadraticPolynomial (e8HyperbolicBasisMatrixInvModTwo.mulVec x) := by
  have hvec :
      e8HyperbolicBasisMatrixInvModTwo.mulVec x =
        fun i : Fin 8 =>
          match i with
          | 0 => x 1 + x 2 + x 4
          | 1 => x 3 + x 7
          | 2 => x 0 + x 1 + x 2 + x 3 + x 5
          | 3 => x 0 + x 2 + x 3 + x 5
          | 4 => x 1 + x 4 + x 5 + x 6 + x 7
          | 5 => x 1 + x 4 + x 6
          | 6 => x 6 + x 7
          | 7 => x 7 := by
    funext i
    fin_cases i <;>
      simp [e8HyperbolicBasisMatrixInvModTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  rw [hvec]
  have hsquare (a : ZMod 2) : a ^ 2 = a := by
    fin_cases a <;> decide
  simp only [e8QuadraticPolynomial, e8SplitQuadraticPolynomial]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (3 : ZMod 2) = 1 := by decide
  have hneg (a : ZMod 2) : -a = a := by
    fin_cases a <;> decide
  simp [sub_eq_add_neg, hsquare, h2, h3, hneg] <;> ring_nf

/-- The stored E8 quadratic form is twice the integral polynomial `Q_E8`. -/
theorem e8Lattice_quadForm_eq_two_mul_e8QuadraticPolynomial (x : Fin 8 → ℤ) :
    e8Lattice.quadForm x = 2 * e8QuadraticPolynomial x := by
  rw [e8Lattice.quadForm_eq_dotProduct]
  simp [Fin.sum_univ_eight, e8QuadraticPolynomial, e8Lattice, e8CartanMatrix,
    dotProduct, Matrix.mulVec]
  ring

/-- Cancelling the visible factor `2` in a mod-`8` equality gives the
corresponding mod-`4` equality for integral representatives. -/
theorem zmod_four_intCast_eq_of_two_mul_eq_zmod_eight (a b : ℤ)
    (h : ((2 * a : ℤ) : ZMod 8) = ((2 * b : ℤ) : ZMod 8)) :
    ((a : ℤ) : ZMod 4) = ((b : ℤ) : ZMod 4) := by
  rw [ZMod.intCast_eq_intCast_iff] at h ⊢
  rw [Int.modEq_iff_dvd] at h ⊢
  change (8 : ℤ) ∣ (2 * b - 2 * a) at h
  change (4 : ℤ) ∣ (b - a)
  rw [← mul_sub] at h
  rcases h with ⟨c, hc⟩
  use c
  nlinarith

/-- Multiplying a mod-`4` equality by the visible factor `2` gives the
corresponding mod-`8` equality. -/
theorem two_mul_eq_zmod_eight_of_zmod_four_intCast_eq (a b : ℤ)
    (h : ((a : ℤ) : ZMod 4) = ((b : ℤ) : ZMod 4)) :
    ((2 * a : ℤ) : ZMod 8) = ((2 * b : ℤ) : ZMod 8) := by
  rw [ZMod.intCast_eq_intCast_iff] at h ⊢
  rw [Int.modEq_iff_dvd] at h ⊢
  change (4 : ℤ) ∣ (b - a) at h
  change (8 : ℤ) ∣ (2 * b - 2 * a)
  rcases h with ⟨c, hc⟩
  use c
  nlinarith

/-- A matrix over `𝔽₂` preserving the E8 quadratic polynomial modulo two.
This is the corrected base target for the E8 dyadic count; it is not the
bilinear Gram-congruence target, which is trivial modulo two. -/
abbrev e8QuadraticIsometryModTwo : Type :=
  {Y : Matrix (Fin 8) (Fin 8) (ZMod 2) //
    ∀ v : Fin 8 → ZMod 2,
      e8QuadraticPolynomial (Y.mulVec v) = e8QuadraticPolynomial v}

noncomputable instance : Fintype e8QuadraticIsometryModTwo := by
  classical
  unfold e8QuadraticIsometryModTwo
  infer_instance

/-- A matrix over `𝔽₂` preserving the split four-hyperbolic-plane quadratic
polynomial. -/
abbrev e8SplitQuadraticIsometryModTwo : Type :=
  {Y : Matrix (Fin 8) (Fin 8) (ZMod 2) //
    ∀ v : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial (Y.mulVec v) = e8SplitQuadraticPolynomial v}

noncomputable instance : Fintype e8SplitQuadraticIsometryModTwo := by
  classical
  unfold e8SplitQuadraticIsometryModTwo
  infer_instance

/-- Matrix-level conjugation from the E8 `Q_E8` model to the split
hyperbolic model over `𝔽₂`. -/
def e8QuadraticIsometryModTwoToSplitMatrix
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  e8HyperbolicBasisMatrixInvModTwo * Y * e8HyperbolicBasisMatrixModTwo

/-- Matrix-level conjugation from the split hyperbolic model back to the E8
`Q_E8` model over `𝔽₂`. -/
def e8SplitQuadraticIsometryModTwoToE8Matrix
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  e8HyperbolicBasisMatrixModTwo * Y * e8HyperbolicBasisMatrixInvModTwo

/-- Cancelling the hyperbolic-basis conjugation on the left side of the
E8-to-split matrix map. -/
theorem e8HyperbolicBasisMatrixModTwo_mul_toSplitMatrix
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8HyperbolicBasisMatrixModTwo * e8QuadraticIsometryModTwoToSplitMatrix Y =
      Y * e8HyperbolicBasisMatrixModTwo := by
  calc
    e8HyperbolicBasisMatrixModTwo * e8QuadraticIsometryModTwoToSplitMatrix Y =
        e8HyperbolicBasisMatrixModTwo *
          (e8HyperbolicBasisMatrixInvModTwo * Y * e8HyperbolicBasisMatrixModTwo) := rfl
    _ = (e8HyperbolicBasisMatrixModTwo * (e8HyperbolicBasisMatrixInvModTwo * Y)) *
          e8HyperbolicBasisMatrixModTwo := by
        exact (Matrix.mul_assoc e8HyperbolicBasisMatrixModTwo
          (e8HyperbolicBasisMatrixInvModTwo * Y) e8HyperbolicBasisMatrixModTwo).symm
    _ = ((e8HyperbolicBasisMatrixModTwo * e8HyperbolicBasisMatrixInvModTwo) * Y) *
          e8HyperbolicBasisMatrixModTwo := by
        rw [← Matrix.mul_assoc]
    _ = Y * e8HyperbolicBasisMatrixModTwo := by
        rw [e8HyperbolicBasisMatrix_mul_inv_zmod_two, Matrix.one_mul]

/-- Cancelling the hyperbolic-basis conjugation on the left side of the
split-to-E8 matrix map. -/
theorem e8HyperbolicBasisMatrixInvModTwo_mul_toE8Matrix
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8HyperbolicBasisMatrixInvModTwo * e8SplitQuadraticIsometryModTwoToE8Matrix Y =
      Y * e8HyperbolicBasisMatrixInvModTwo := by
  calc
    e8HyperbolicBasisMatrixInvModTwo * e8SplitQuadraticIsometryModTwoToE8Matrix Y =
        e8HyperbolicBasisMatrixInvModTwo *
          (e8HyperbolicBasisMatrixModTwo * Y * e8HyperbolicBasisMatrixInvModTwo) := rfl
    _ = (e8HyperbolicBasisMatrixInvModTwo * (e8HyperbolicBasisMatrixModTwo * Y)) *
          e8HyperbolicBasisMatrixInvModTwo := by
        exact (Matrix.mul_assoc e8HyperbolicBasisMatrixInvModTwo
          (e8HyperbolicBasisMatrixModTwo * Y) e8HyperbolicBasisMatrixInvModTwo).symm
    _ = ((e8HyperbolicBasisMatrixInvModTwo * e8HyperbolicBasisMatrixModTwo) * Y) *
          e8HyperbolicBasisMatrixInvModTwo := by
        rw [← Matrix.mul_assoc]
    _ = Y * e8HyperbolicBasisMatrixInvModTwo := by
        rw [e8HyperbolicBasisMatrix_inv_mul_zmod_two, Matrix.one_mul]

/-- Conjugating from E8 to split and back is the identity at matrix level. -/
theorem e8SplitQuadraticIsometryModTwoToE8Matrix_toSplitMatrix
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8SplitQuadraticIsometryModTwoToE8Matrix
        (e8QuadraticIsometryModTwoToSplitMatrix Y) = Y := by
  calc
    e8SplitQuadraticIsometryModTwoToE8Matrix
        (e8QuadraticIsometryModTwoToSplitMatrix Y) =
        e8HyperbolicBasisMatrixModTwo *
          (e8QuadraticIsometryModTwoToSplitMatrix Y) *
          e8HyperbolicBasisMatrixInvModTwo := rfl
    _ = (Y * e8HyperbolicBasisMatrixModTwo) *
          e8HyperbolicBasisMatrixInvModTwo := by
        rw [e8HyperbolicBasisMatrixModTwo_mul_toSplitMatrix]
    _ = Y := by
        rw [Matrix.mul_assoc, e8HyperbolicBasisMatrix_mul_inv_zmod_two, Matrix.mul_one]

/-- Conjugating from split to E8 and back is the identity at matrix level. -/
theorem e8QuadraticIsometryModTwoToSplitMatrix_toE8Matrix
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8QuadraticIsometryModTwoToSplitMatrix
        (e8SplitQuadraticIsometryModTwoToE8Matrix Y) = Y := by
  calc
    e8QuadraticIsometryModTwoToSplitMatrix
        (e8SplitQuadraticIsometryModTwoToE8Matrix Y) =
        e8HyperbolicBasisMatrixInvModTwo *
          (e8SplitQuadraticIsometryModTwoToE8Matrix Y) *
          e8HyperbolicBasisMatrixModTwo := rfl
    _ = (Y * e8HyperbolicBasisMatrixInvModTwo) *
          e8HyperbolicBasisMatrixModTwo := by
        rw [e8HyperbolicBasisMatrixInvModTwo_mul_toE8Matrix]
    _ = Y := by
        rw [Matrix.mul_assoc, e8HyperbolicBasisMatrix_inv_mul_zmod_two, Matrix.mul_one]

/-- Conjugating an E8 quadratic isometry by the hyperbolic basis gives
a split quadratic isometry. -/
theorem e8QuadraticIsometryModTwoToSplit_mem
    (Y : e8QuadraticIsometryModTwo) :
    ∀ v : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial
          ((e8QuadraticIsometryModTwoToSplitMatrix Y.1).mulVec v) =
        e8SplitQuadraticPolynomial v := by
  intro v
  have hmiddle :
      e8HyperbolicBasisMatrixModTwo.mulVec
          ((e8QuadraticIsometryModTwoToSplitMatrix Y.1).mulVec v) =
        Y.1.mulVec (e8HyperbolicBasisMatrixModTwo.mulVec v) := by
    rw [Matrix.mulVec_mulVec, e8HyperbolicBasisMatrixModTwo_mul_toSplitMatrix,
      Matrix.mulVec_mulVec]
  calc
    e8SplitQuadraticPolynomial
        ((e8QuadraticIsometryModTwoToSplitMatrix Y.1).mulVec v)
        = e8QuadraticPolynomial
            (e8HyperbolicBasisMatrixModTwo.mulVec
              ((e8QuadraticIsometryModTwoToSplitMatrix Y.1).mulVec v)) := by
          exact (e8QuadraticPolynomial_hyperbolicBasis_mulVec_zmod_two
            ((e8QuadraticIsometryModTwoToSplitMatrix Y.1).mulVec v)).symm
    _ = e8QuadraticPolynomial
          (Y.1.mulVec (e8HyperbolicBasisMatrixModTwo.mulVec v)) := by
          rw [hmiddle]
    _ = e8QuadraticPolynomial (e8HyperbolicBasisMatrixModTwo.mulVec v) :=
          Y.2 (e8HyperbolicBasisMatrixModTwo.mulVec v)
    _ = e8SplitQuadraticPolynomial v := by
          exact e8QuadraticPolynomial_hyperbolicBasis_mulVec_zmod_two v

/-- The subtype map from the E8 `Q_E8` model to the split model. -/
def e8QuadraticIsometryModTwoToSplit
    (Y : e8QuadraticIsometryModTwo) : e8SplitQuadraticIsometryModTwo :=
  ⟨e8QuadraticIsometryModTwoToSplitMatrix Y.1, e8QuadraticIsometryModTwoToSplit_mem Y⟩

/-- Conjugating a split quadratic isometry back by the hyperbolic basis
gives an E8 quadratic isometry. -/
theorem e8SplitQuadraticIsometryModTwoToE8_mem
    (Y : e8SplitQuadraticIsometryModTwo) :
    ∀ v : Fin 8 → ZMod 2,
      e8QuadraticPolynomial
          ((e8SplitQuadraticIsometryModTwoToE8Matrix Y.1).mulVec v) =
        e8QuadraticPolynomial v := by
  intro v
  have hmiddle :
      e8HyperbolicBasisMatrixInvModTwo.mulVec
          ((e8SplitQuadraticIsometryModTwoToE8Matrix Y.1).mulVec v) =
        Y.1.mulVec (e8HyperbolicBasisMatrixInvModTwo.mulVec v) := by
    rw [Matrix.mulVec_mulVec, e8HyperbolicBasisMatrixInvModTwo_mul_toE8Matrix,
      Matrix.mulVec_mulVec]
  calc
    e8QuadraticPolynomial
        ((e8SplitQuadraticIsometryModTwoToE8Matrix Y.1).mulVec v)
        = e8SplitQuadraticPolynomial
            (e8HyperbolicBasisMatrixInvModTwo.mulVec
              ((e8SplitQuadraticIsometryModTwoToE8Matrix Y.1).mulVec v)) := by
          exact e8QuadraticPolynomial_eq_split_hyperbolicBasisInv_mulVec_zmod_two
            ((e8SplitQuadraticIsometryModTwoToE8Matrix Y.1).mulVec v)
    _ = e8SplitQuadraticPolynomial
          (Y.1.mulVec (e8HyperbolicBasisMatrixInvModTwo.mulVec v)) := by
          rw [hmiddle]
    _ = e8SplitQuadraticPolynomial (e8HyperbolicBasisMatrixInvModTwo.mulVec v) :=
          Y.2 (e8HyperbolicBasisMatrixInvModTwo.mulVec v)
    _ = e8QuadraticPolynomial v := by
          exact (e8QuadraticPolynomial_eq_split_hyperbolicBasisInv_mulVec_zmod_two v).symm

/-- The subtype map from the split model back to the E8 `Q_E8` model. -/
def e8SplitQuadraticIsometryModTwoToE8
    (Y : e8SplitQuadraticIsometryModTwo) : e8QuadraticIsometryModTwo :=
  ⟨e8SplitQuadraticIsometryModTwoToE8Matrix Y.1, e8SplitQuadraticIsometryModTwoToE8_mem Y⟩

/-- The corrected E8 mod-two quadratic-isometry target is equivalent to the
split four-hyperbolic-plane quadratic-isometry target. -/
def e8QuadraticIsometryModTwoEquivSplit :
    e8QuadraticIsometryModTwo ≃ e8SplitQuadraticIsometryModTwo where
  toFun := e8QuadraticIsometryModTwoToSplit
  invFun := e8SplitQuadraticIsometryModTwoToE8
  left_inv := by
    intro Y
    apply Subtype.ext
    exact e8SplitQuadraticIsometryModTwoToE8Matrix_toSplitMatrix Y.1
  right_inv := by
    intro Y
    apply Subtype.ext
    exact e8QuadraticIsometryModTwoToSplitMatrix_toE8Matrix Y.1

/-- The E8 quadratic target and the split target have the same cardinality. -/
theorem e8QuadraticIsometryModTwo_natCard_eq_split :
    Nat.card e8QuadraticIsometryModTwo = Nat.card e8SplitQuadraticIsometryModTwo := by
  exact Nat.card_congr e8QuadraticIsometryModTwoEquivSplit

/-- The identity matrix is an E8 quadratic isometry modulo two. -/
def e8QuadraticIsometryModTwoIdentity : e8QuadraticIsometryModTwo :=
  ⟨1, by intro v; simp⟩

/-- The split four-hyperbolic-plane finite-field target as a filtered finite set. -/
noncomputable def e8SplitQuadraticIsometryModTwoMatrices :
    Finset (Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  classical
  exact Finset.univ.filter fun Y =>
    ∀ v : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial (Y.mulVec v) = e8SplitQuadraticPolynomial v

/-- Membership in the split four-hyperbolic-plane mod-two quadratic-isometry target. -/
theorem mem_e8SplitQuadraticIsometryModTwoMatrices_iff
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Y ∈ e8SplitQuadraticIsometryModTwoMatrices ↔
      ∀ v : Fin 8 → ZMod 2,
        e8SplitQuadraticPolynomial (Y.mulVec v) = e8SplitQuadraticPolynomial v := by
  simp [e8SplitQuadraticIsometryModTwoMatrices]

/-- The finite-set and subtype presentations of the split mod-two
quadratic-isometry target have the same cardinality. -/
theorem e8SplitQuadraticIsometryModTwoMatrices_card :
    e8SplitQuadraticIsometryModTwoMatrices.card = Nat.card e8SplitQuadraticIsometryModTwo := by
  classical
  rw [Nat.card_eq_fintype_card]
  change e8SplitQuadraticIsometryModTwoMatrices.card =
    Fintype.card {Y : Matrix (Fin 8) (Fin 8) (ZMod 2) //
      ∀ v : Fin 8 → ZMod 2,
        e8SplitQuadraticPolynomial (Y.mulVec v) = e8SplitQuadraticPolynomial v}
  rw [e8SplitQuadraticIsometryModTwoMatrices]
  exact (Fintype.card_subtype (fun Y : Matrix (Fin 8) (Fin 8) (ZMod 2) =>
    ∀ v : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial (Y.mulVec v) = e8SplitQuadraticPolynomial v)).symm

/-- The corrected E8 target cardinality is the split-model filtered-set cardinality. -/
theorem e8QuadraticIsometryModTwo_natCard_eq_splitMatrices :
    Nat.card e8QuadraticIsometryModTwo = e8SplitQuadraticIsometryModTwoMatrices.card := by
  rw [e8QuadraticIsometryModTwo_natCard_eq_split, e8SplitQuadraticIsometryModTwoMatrices_card]

/-- The polar form attached to the split four-hyperbolic-plane quadratic
polynomial over `𝔽₂`. -/
noncomputable def e8SplitPolarBilinear (v w : Fin 8 → ZMod 2) : ZMod 2 :=
  v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2 +
  v 4 * w 5 + v 5 * w 4 + v 6 * w 7 + v 7 * w 6

/-- The singular vectors for the split four-hyperbolic-plane model over `𝔽₂`. -/
noncomputable def e8SplitSingularVectors : Finset (Fin 8 → ZMod 2) := by
  classical
  exact Finset.univ.filter fun v => e8SplitQuadraticPolynomial v = 0

/-- The nonzero singular vectors for the split four-hyperbolic-plane model. -/
noncomputable def e8SplitNonzeroSingularVectors : Finset (Fin 8 → ZMod 2) := by
  classical
  exact e8SplitSingularVectors.filter fun v => v ≠ 0

/-- The split singular partners of a vector, i.e. singular vectors pairing to
`1` with it under the split polar form. -/
noncomputable def e8SplitSingularPartners (v : Fin 8 → ZMod 2) :
    Finset (Fin 8 → ZMod 2) := by
  classical
  exact e8SplitSingularVectors.filter fun w => e8SplitPolarBilinear v w = 1

set_option maxRecDepth 100000

/-- The split four-hyperbolic-plane model has `136` singular vectors over
`𝔽₂`, including zero.  This is the first finite-field count in the
base-count recurrence. -/
theorem e8SplitSingularVectors_card :
    e8SplitSingularVectors.card = 136 := by
  decide

/-- The split four-hyperbolic-plane model has `135` nonzero singular vectors
over `𝔽₂`. -/
theorem e8SplitNonzeroSingularVectors_card :
    e8SplitNonzeroSingularVectors.card = 135 := by
  decide

/-- A fixed nonzero singular vector in the first split hyperbolic plane. -/
def e8SplitFirstBasisVector : Fin 8 → ZMod 2 :=
  fun i => if i = 0 then 1 else 0

/-- The fixed first split basis vector is a nonzero singular vector. -/
theorem e8SplitFirstBasisVector_mem_nonzeroSingular :
    e8SplitFirstBasisVector ∈ e8SplitNonzeroSingularVectors := by
  decide

/-- The second basis vector in the first split hyperbolic plane. -/
def e8SplitSecondBasisVector : Fin 8 → ZMod 2 :=
  fun i => if i = 1 then 1 else 0

/-- The second split basis vector is a singular partner of the first one. -/
theorem e8SplitSecondBasisVector_mem_singularPartners_firstBasisVector :
    e8SplitSecondBasisVector ∈ e8SplitSingularPartners e8SplitFirstBasisVector := by
  decide

/-- The fixed first split basis vector has exactly `64` singular partners.
This is the base finite-field count for the later uniform partner-count
argument in the split four-hyperbolic-plane model. -/
theorem e8SplitSingularPartners_firstBasisVector_card :
    (e8SplitSingularPartners e8SplitFirstBasisVector).card = 64 := by
  decide

/-- The split polar form is the polarization of the split quadratic
polynomial over `𝔽₂`. -/
theorem e8SplitPolarBilinear_eq_quadratic_add
    (v w : Fin 8 → ZMod 2) :
    e8SplitPolarBilinear v w =
      e8SplitQuadraticPolynomial (v + w) +
        e8SplitQuadraticPolynomial v + e8SplitQuadraticPolynomial w := by
  simp only [e8SplitPolarBilinear, e8SplitQuadraticPolynomial, Pi.add_apply]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [h2]

/-- The split polar form is symmetric. -/
theorem e8SplitPolarBilinear_comm
    (v w : Fin 8 → ZMod 2) :
    e8SplitPolarBilinear v w = e8SplitPolarBilinear w v := by
  simp only [e8SplitPolarBilinear]
  ring_nf

/-- Split quadratic isometries preserve the associated polar form. -/
theorem e8SplitQuadraticIsometryModTwo_preserves_polar
    (Y : e8SplitQuadraticIsometryModTwo) (v w : Fin 8 → ZMod 2) :
    e8SplitPolarBilinear (Y.1.mulVec v) (Y.1.mulVec w) =
      e8SplitPolarBilinear v w := by
  rw [e8SplitPolarBilinear_eq_quadratic_add,
    e8SplitPolarBilinear_eq_quadratic_add]
  rw [← Matrix.mulVec_add]
  rw [Y.2 (v + w), Y.2 v, Y.2 w]

/-- The split polar form has zero left kernel. -/
theorem e8SplitPolarBilinear_left_kernel_eq_zero
    (v : Fin 8 → ZMod 2)
    (h : ∀ w : Fin 8 → ZMod 2, e8SplitPolarBilinear v w = 0) :
    v = 0 := by
  funext i
  fin_cases i <;>
    first
    | simpa [e8SplitPolarBilinear] using h (Pi.single (1 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (0 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (3 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (2 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (5 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (4 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (7 : Fin 8) (1 : ZMod 2))
    | simpa [e8SplitPolarBilinear] using h (Pi.single (6 : Fin 8) (1 : ZMod 2))

/-- A split quadratic isometry has trivial kernel.  Although
`e8SplitQuadraticIsometryModTwo` is stated only as preservation of the
quadratic polynomial, nondegeneracy of the associated polar form implies
invertibility over the finite vector space. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_eq_zero_iff
    (Y : e8SplitQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) :
    Y.1.mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    apply e8SplitPolarBilinear_left_kernel_eq_zero v
    intro w
    rw [← e8SplitQuadraticIsometryModTwo_preserves_polar Y v w, hv]
    simp [e8SplitPolarBilinear]
  · intro hv
    rw [hv, Matrix.mulVec_zero]

/-- A split quadratic isometry is injective on vectors. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_injective
    (Y : e8SplitQuadraticIsometryModTwo) :
    Function.Injective Y.1.mulVec := by
  intro v w h
  have hker : Y.1.mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hz := (e8SplitQuadraticIsometryModTwo_mulVec_eq_zero_iff Y (v - w)).mp hker
  exact sub_eq_zero.mp hz

/-- A split quadratic isometry sends nonzero vectors to nonzero vectors. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_ne_zero
    (Y : e8SplitQuadraticIsometryModTwo) {v : Fin 8 → ZMod 2} (hv : v ≠ 0) :
    Y.1.mulVec v ≠ 0 := by
  intro hzero
  exact hv ((e8SplitQuadraticIsometryModTwo_mulVec_eq_zero_iff Y v).mp hzero)

/-- A split quadratic isometry sends nonzero singular vectors to nonzero
singular vectors. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_mem_nonzeroSingular
    (Y : e8SplitQuadraticIsometryModTwo) {v : Fin 8 → ZMod 2}
    (hv : v ∈ e8SplitNonzeroSingularVectors) :
    Y.1.mulVec v ∈ e8SplitNonzeroSingularVectors := by
  simp [e8SplitNonzeroSingularVectors, e8SplitSingularVectors] at hv ⊢
  exact ⟨by rw [Y.2 v, hv.1], e8SplitQuadraticIsometryModTwo_mulVec_ne_zero Y hv.2⟩

/-- A split quadratic isometry sends singular partners to singular partners. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_mem_singularPartners
    (Y : e8SplitQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) {w : Fin 8 → ZMod 2}
    (hw : w ∈ e8SplitSingularPartners v) :
    Y.1.mulVec w ∈ e8SplitSingularPartners (Y.1.mulVec v) := by
  simp [e8SplitSingularPartners, e8SplitSingularVectors] at hw ⊢
  exact ⟨by rw [Y.2 w, hw.1],
    by rw [e8SplitQuadraticIsometryModTwo_preserves_polar Y v w, hw.2]⟩

/-- A split quadratic isometry is surjective on vectors. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_surjective
    (Y : e8SplitQuadraticIsometryModTwo) :
    Function.Surjective Y.1.mulVec := by
  exact Finite.surjective_of_injective (e8SplitQuadraticIsometryModTwo_mulVec_injective Y)

/-- Membership in a partner set can be pulled back through a split quadratic
isometry. -/
theorem e8SplitQuadraticIsometryModTwo_preimage_mem_singularPartners
    (Y : e8SplitQuadraticIsometryModTwo) (v z w : Fin 8 → ZMod 2)
    (hw : Y.1.mulVec w = z) (hz : z ∈ e8SplitSingularPartners (Y.1.mulVec v)) :
    w ∈ e8SplitSingularPartners v := by
  simp [e8SplitSingularPartners, e8SplitSingularVectors] at hz ⊢
  constructor
  · have hQ := Y.2 w
    rw [hw] at hQ
    exact hQ.symm.trans hz.1
  · have hpolar := e8SplitQuadraticIsometryModTwo_preserves_polar Y v w
    rw [hw, hz.2] at hpolar
    exact hpolar.symm

/-- A split quadratic isometry bijects the singular-partner set of `v` with
that of its image. -/
noncomputable def e8SplitQuadraticIsometryModTwo_singularPartnersEquiv
    (Y : e8SplitQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) :
    (e8SplitSingularPartners v : Type) ≃
      (e8SplitSingularPartners (Y.1.mulVec v) : Type) where
  toFun w := ⟨Y.1.mulVec w.1,
    e8SplitQuadraticIsometryModTwo_mulVec_mem_singularPartners Y v w.2⟩
  invFun z := by
    let w : Fin 8 → ZMod 2 :=
      Classical.choose (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y z.1)
    exact ⟨w, e8SplitQuadraticIsometryModTwo_preimage_mem_singularPartners Y v z.1 w
      (Classical.choose_spec (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y z.1)) z.2⟩
  left_inv w := by
    apply Subtype.ext
    dsimp
    exact (e8SplitQuadraticIsometryModTwo_mulVec_injective Y)
      (Classical.choose_spec
        (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y (Y.1.mulVec w.1)))
  right_inv z := by
    apply Subtype.ext
    dsimp
    exact Classical.choose_spec (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y z.1)

/-- Split quadratic isometries preserve singular-partner cardinalities. -/
theorem e8SplitQuadraticIsometryModTwo_singularPartners_card_image
    (Y : e8SplitQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) :
    (e8SplitSingularPartners (Y.1.mulVec v)).card =
      (e8SplitSingularPartners v).card := by
  classical
  rw [← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard]
  exact (Nat.card_congr
    (e8SplitQuadraticIsometryModTwo_singularPartnersEquiv Y v)).symm

/-- The identity matrix is a split quadratic isometry. -/
def e8SplitQuadraticIsometryModTwoIdentity : e8SplitQuadraticIsometryModTwo :=
  ⟨1, by intro v; simp⟩

/-- Split quadratic isometries are closed under matrix composition. -/
def e8SplitQuadraticIsometryModTwoComp
    (Y Z : e8SplitQuadraticIsometryModTwo) : e8SplitQuadraticIsometryModTwo :=
  ⟨Y.1 * Z.1, by
    intro v
    rw [← Matrix.mulVec_mulVec v Y.1 Z.1]
    rw [Y.2 (Z.1.mulVec v), Z.2 v]⟩

/-- A split quadratic isometry as a permutation of the underlying finite vector
space.  This packages the injectivity and surjectivity results as an
equivalence for group actions. -/
noncomputable def e8SplitQuadraticIsometryModTwoVectorEquiv
    (Y : e8SplitQuadraticIsometryModTwo) :
    (Fin 8 → ZMod 2) ≃ (Fin 8 → ZMod 2) :=
  Equiv.ofBijective Y.1.mulVec
    ⟨e8SplitQuadraticIsometryModTwo_mulVec_injective Y,
      e8SplitQuadraticIsometryModTwo_mulVec_surjective Y⟩

/-- Evaluation at the fixed first basis vector, as a map into the nonzero
singular vectors. -/
noncomputable def e8SplitQuadraticIsometryModTwoFirstVectorMap :
    e8SplitQuadraticIsometryModTwo → e8SplitNonzeroSingularVectors := fun Y =>
  ⟨Y.1.mulVec e8SplitFirstBasisVector,
    e8SplitQuadraticIsometryModTwo_mulVec_mem_nonzeroSingular Y
      e8SplitFirstBasisVector_mem_nonzeroSingular⟩

/-- Uniform fibers of the first-vector map give the split isometry count.
This is the finite orbit-stabilizer counting interface for the later
transitivity and stabilizer computation. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_nonzeroSingular_mul_of_firstVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ v : e8SplitNonzeroSingularVectors,
      Nat.card {Y : e8SplitQuadraticIsometryModTwo //
        e8SplitQuadraticIsometryModTwoFirstVectorMap Y = v} = c) :
    Nat.card e8SplitQuadraticIsometryModTwo = Nat.card e8SplitNonzeroSingularVectors * c := by
  exact nat_card_eq_mul_of_fiber_card e8SplitQuadraticIsometryModTwoFirstVectorMap c hfiber

/-- With the known `135` nonzero singular vectors, uniform first-vector fibers
give a compact count. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_135_mul_of_firstVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ v : e8SplitNonzeroSingularVectors,
      Nat.card {Y : e8SplitQuadraticIsometryModTwo //
        e8SplitQuadraticIsometryModTwoFirstVectorMap Y = v} = c) :
    Nat.card e8SplitQuadraticIsometryModTwo = 135 * c := by
  rw [e8SplitQuadraticIsometryModTwo_natCard_eq_nonzeroSingular_mul_of_firstVector_fiber_card
    c hfiber]
  rw [Nat.card_eq_finsetCard e8SplitNonzeroSingularVectors, e8SplitNonzeroSingularVectors_card]

/-- The stabilizer of the fixed first basis vector inside the split quadratic
isometry monoid.  This is the first stabilizer in the finite orbit-stabilizer
recurrence for the split E8 base count. -/
abbrev e8SplitQuadraticIsometryModTwoFirstVectorStabilizer : Type :=
  {Y : e8SplitQuadraticIsometryModTwo //
    Y.1.mulVec e8SplitFirstBasisVector = e8SplitFirstBasisVector}

noncomputable instance :
    Fintype e8SplitQuadraticIsometryModTwoFirstVectorStabilizer := by
  unfold e8SplitQuadraticIsometryModTwoFirstVectorStabilizer
  infer_instance

/-- The fiber of the first-vector map over the fixed first vector is exactly the
first-vector stabilizer. -/
noncomputable def e8SplitQuadraticIsometryModTwo_firstVectorFiberEquivStabilizer :
    {Y : e8SplitQuadraticIsometryModTwo //
      e8SplitQuadraticIsometryModTwoFirstVectorMap Y =
        ⟨e8SplitFirstBasisVector, e8SplitFirstBasisVector_mem_nonzeroSingular⟩} ≃
      e8SplitQuadraticIsometryModTwoFirstVectorStabilizer where
  toFun Y := by
    refine ⟨Y.1, ?_⟩
    have h := congrArg Subtype.val Y.2
    simpa [e8SplitQuadraticIsometryModTwoFirstVectorMap] using h
  invFun Y := by
    refine ⟨Y.1, ?_⟩
    apply Subtype.ext
    exact Y.2
  left_inv Y := by
    apply Subtype.ext
    rfl
  right_inv Y := by
    apply Subtype.ext
    rfl

/-- Cardinality form of the equivalence between the fixed first-vector fiber and
the first-vector stabilizer. -/
theorem e8SplitQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer :
    Nat.card {Y : e8SplitQuadraticIsometryModTwo //
      e8SplitQuadraticIsometryModTwoFirstVectorMap Y =
        ⟨e8SplitFirstBasisVector, e8SplitFirstBasisVector_mem_nonzeroSingular⟩} =
      Nat.card e8SplitQuadraticIsometryModTwoFirstVectorStabilizer := by
  exact Nat.card_congr e8SplitQuadraticIsometryModTwo_firstVectorFiberEquivStabilizer

/-- Evaluation at the second basis vector maps the first-vector stabilizer to
the `64` singular partners of the fixed first basis vector. -/
noncomputable def
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap :
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizer →
      (e8SplitSingularPartners e8SplitFirstBasisVector : Type) := fun Y =>
  ⟨Y.1.1.mulVec e8SplitSecondBasisVector, by
    have hmem :=
      e8SplitQuadraticIsometryModTwo_mulVec_mem_singularPartners Y.1
        e8SplitFirstBasisVector
        e8SplitSecondBasisVector_mem_singularPartners_firstBasisVector
    simpa [Y.2] using hmem⟩

/-- Uniform fibers of the second-vector map give the cardinality of the
first-vector stabilizer.  This is the next finite orbit-stabilizer interface:
the remaining stabilizer-size recurrence is isolated in the common fiber
cardinality `c`. -/
theorem
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizer_natCard_eq_64_mul_of_secondVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type),
      Nat.card {Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitQuadraticIsometryModTwoFirstVectorStabilizer = 64 * c := by
  rw [nat_card_eq_mul_of_fiber_card
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap c hfiber]
  rw [Nat.card_eq_finsetCard (e8SplitSingularPartners e8SplitFirstBasisVector),
    e8SplitSingularPartners_firstBasisVector_card]

/-- Combining the first-vector and second-vector recurrence interfaces reduces
the split E8 base count to one stabilizer fiber cardinality. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_8640_mul_of_secondVector_fiber_card
    (c : ℕ)
    (hfirst : ∀ v : e8SplitNonzeroSingularVectors,
      Nat.card {Y : e8SplitQuadraticIsometryModTwo //
        e8SplitQuadraticIsometryModTwoFirstVectorMap Y = v} =
          Nat.card e8SplitQuadraticIsometryModTwoFirstVectorStabilizer)
    (hsecond : ∀ w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type),
      Nat.card {Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitQuadraticIsometryModTwo = 8640 * c := by
  rw [e8SplitQuadraticIsometryModTwo_natCard_eq_135_mul_of_firstVector_fiber_card
    (Nat.card e8SplitQuadraticIsometryModTwoFirstVectorStabilizer) hfirst]
  rw [e8SplitQuadraticIsometryModTwoFirstVectorStabilizer_natCard_eq_64_mul_of_secondVector_fiber_card
    c hsecond]
  rw [← Nat.mul_assoc]

/-- The coordinate vector dual to `a` for the split polar form, so that
`e8SplitPolarBilinear x a` is the dot product of `x` with this vector. -/
def e8SplitPolarDualVector (a : Fin 8 → ZMod 2) : Fin 8 → ZMod 2
  | 0 => a 1
  | 1 => a 0
  | 2 => a 3
  | 3 => a 2
  | 4 => a 5
  | 5 => a 4
  | 6 => a 7
  | 7 => a 6

/-- The characteristic-two orthogonal symmetry attached to a vector `a`.
When `Q(a)=1`, this matrix sends `x` to `x + B(x,a) a` and preserves the split
quadratic polynomial. -/
def e8SplitSymmetryMatrix (a : Fin 8 → ZMod 2) :
    Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => (1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) i j +
    a i * e8SplitPolarDualVector a j

set_option maxHeartbeats 800000 in
/-- The matrix formula for the characteristic-two split symmetry. -/
theorem e8SplitSymmetryMatrix_mulVec
    (a x : Fin 8 → ZMod 2) :
    (e8SplitSymmetryMatrix a).mulVec x =
      fun i => x i + e8SplitPolarBilinear x a * a i := by
  ext i
  fin_cases i <;>
    simp [e8SplitSymmetryMatrix, e8SplitPolarDualVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_eight, e8SplitPolarBilinear, Matrix.one_apply]
  <;> ring_nf

/-- Quadratic expansion for the split polynomial along a scalar multiple of a
vector. -/
theorem e8SplitQuadraticPolynomial_add_smul
    (x a : Fin 8 → ZMod 2) (c : ZMod 2) :
    e8SplitQuadraticPolynomial (fun i => x i + c * a i) =
      e8SplitQuadraticPolynomial x + c^2 * e8SplitQuadraticPolynomial a +
        c * e8SplitPolarBilinear x a := by
  simp only [e8SplitQuadraticPolynomial, e8SplitPolarBilinear]
  ring_nf

/-- If `Q(a)=1`, the characteristic-two symmetry attached to `a` preserves the
split quadratic polynomial. -/
theorem e8SplitQuadraticPolynomial_symmetry_apply
    (a x : Fin 8 → ZMod 2) (ha : e8SplitQuadraticPolynomial a = 1) :
    e8SplitQuadraticPolynomial (fun i => x i + e8SplitPolarBilinear x a * a i) =
      e8SplitQuadraticPolynomial x := by
  rw [e8SplitQuadraticPolynomial_add_smul]
  rw [ha]
  rw [mul_one]
  let b : ZMod 2 := e8SplitPolarBilinear x a
  change e8SplitQuadraticPolynomial x + b ^ 2 + b * b = e8SplitQuadraticPolynomial x
  have hsquare (z : ZMod 2) : z ^ 2 = z := by
    fin_cases z <;> decide
  have hbsq : b ^ 2 = b := hsquare b
  have hbmul : b * b = b := by
    simpa [pow_two] using hsquare b
  rw [hbsq, hbmul]
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  calc
    e8SplitQuadraticPolynomial x + b + b =
        e8SplitQuadraticPolynomial x + (b + b) := by rw [add_assoc]
    _ = e8SplitQuadraticPolynomial x := by rw [hdouble, add_zero]

/-- The characteristic-two symmetry as a split quadratic isometry, under the
condition `Q(a)=1`. -/
def e8SplitSymmetry
    (a : Fin 8 → ZMod 2) (ha : e8SplitQuadraticPolynomial a = 1) :
    e8SplitQuadraticIsometryModTwo :=
  ⟨e8SplitSymmetryMatrix a, by
    intro x
    rw [e8SplitSymmetryMatrix_mulVec]
    exact e8SplitQuadraticPolynomial_symmetry_apply a x ha⟩

/-- If two singular vectors pair to `1`, their sum has split norm `1`. -/
theorem e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair
    {u v : Fin 8 → ZMod 2}
    (hu : e8SplitQuadraticPolynomial u = 0)
    (hv : e8SplitQuadraticPolynomial v = 0)
    (hpair : e8SplitPolarBilinear u v = 1) :
    e8SplitQuadraticPolynomial (u + v) = 1 := by
  have hpol := e8SplitPolarBilinear_eq_quadratic_add u v
  rw [hpol, hu, hv] at hpair
  simpa using hpair

/-- If two singular vectors pair to `1`, the characteristic-two symmetry
attached to their sum sends the first vector to the second. -/
theorem e8SplitSymmetry_mulVec_of_singular_pair
    {u v : Fin 8 → ZMod 2}
    (hu : e8SplitQuadraticPolynomial u = 0)
    (hv : e8SplitQuadraticPolynomial v = 0)
    (hpair : e8SplitPolarBilinear u v = 1) :
    (e8SplitSymmetry (u + v)
      (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hu hv hpair)).1.mulVec u = v := by
  change (e8SplitSymmetryMatrix (u + v)).mulVec u = v
  rw [e8SplitSymmetryMatrix_mulVec]
  have hpolar : e8SplitPolarBilinear u (u + v) = 1 := by
    simp [e8SplitPolarBilinear, Pi.add_apply] at hpair ⊢
    ring_nf at hpair ⊢
    have h2 : (2 : ZMod 2) = 0 := by decide
    simpa [h2] using hpair
  funext i
  rw [hpolar]
  simp only [one_mul, Pi.add_apply]
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [← add_assoc, hdouble, zero_add]

/-- The first-vector orbit contains every nonzero singular vector that pairs to
`1` with the fixed first basis vector.  This is the direct transvection case of
the split-model transitivity proof. -/
theorem e8SplitQuadraticIsometryModTwoFirstVectorMap_exists_of_pair_one
    (v : e8SplitNonzeroSingularVectors)
    (hpair : e8SplitPolarBilinear e8SplitFirstBasisVector v.1 = 1) :
    ∃ Y : e8SplitQuadraticIsometryModTwo,
      e8SplitQuadraticIsometryModTwoFirstVectorMap Y = v := by
  have hfirstQ : e8SplitQuadraticPolynomial e8SplitFirstBasisVector = 0 := by
    have hmem : e8SplitFirstBasisVector ∈ e8SplitNonzeroSingularVectors :=
      e8SplitFirstBasisVector_mem_nonzeroSingular
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hvQ : e8SplitQuadraticPolynomial v.1 = 0 := by
    have hmem : v.1 ∈ e8SplitNonzeroSingularVectors := v.2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  let Y : e8SplitQuadraticIsometryModTwo :=
    e8SplitSymmetry (e8SplitFirstBasisVector + v.1)
      (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hfirstQ hvQ hpair)
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  exact e8SplitSymmetry_mulVec_of_singular_pair hfirstQ hvQ hpair

set_option maxHeartbeats 2000000 in
/-- If a nonzero singular vector is orthogonal to the fixed first vector and is
not the first vector itself, then it has a singular common partner with the
fixed first vector.  This finite-field lemma is the only remaining geometric
case split needed for first-vector transitivity in the split model. -/
theorem e8SplitFirstBasisCommonSingularPartner_exists
    (v : e8SplitNonzeroSingularVectors)
    (horth : e8SplitPolarBilinear e8SplitFirstBasisVector v.1 = 0)
    (hne : v.1 ≠ e8SplitFirstBasisVector) :
    ∃ w : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial w = 0 ∧
        e8SplitPolarBilinear e8SplitFirstBasisVector w = 1 ∧
          e8SplitPolarBilinear v.1 w = 1 := by
  decide +revert

/-- The first-vector map from split quadratic isometries to nonzero singular
vectors is surjective.  If the target vector pairs to `1` with the fixed first
vector, one characteristic-two symmetry suffices; otherwise a finite-field
common partner gives a two-symmetry composition. -/
theorem e8SplitQuadraticIsometryModTwoFirstVectorMap_surjective :
    Function.Surjective e8SplitQuadraticIsometryModTwoFirstVectorMap := by
  intro v
  have hfirstQ : e8SplitQuadraticPolynomial e8SplitFirstBasisVector = 0 := by
    have hmem : e8SplitFirstBasisVector ∈ e8SplitNonzeroSingularVectors :=
      e8SplitFirstBasisVector_mem_nonzeroSingular
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hvQ : e8SplitQuadraticPolynomial v.1 = 0 := by
    have hmem : v.1 ∈ e8SplitNonzeroSingularVectors := v.2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  by_cases hvfirst : v.1 = e8SplitFirstBasisVector
  · refine ⟨e8SplitQuadraticIsometryModTwoIdentity, ?_⟩
    apply Subtype.ext
    simp [e8SplitQuadraticIsometryModTwoFirstVectorMap,
      e8SplitQuadraticIsometryModTwoIdentity, hvfirst]
  · by_cases hpair : e8SplitPolarBilinear e8SplitFirstBasisVector v.1 = 1
    · exact e8SplitQuadraticIsometryModTwoFirstVectorMap_exists_of_pair_one v hpair
    · have horth : e8SplitPolarBilinear e8SplitFirstBasisVector v.1 = 0 := by
        decide +revert
      rcases e8SplitFirstBasisCommonSingularPartner_exists v horth hvfirst with
        ⟨w, hwQ, hfirstw, hvw⟩
      have hwv : e8SplitPolarBilinear w v.1 = 1 := by
        rw [e8SplitPolarBilinear_comm]
        exact hvw
      let Y₁ : e8SplitQuadraticIsometryModTwo :=
        e8SplitSymmetry (e8SplitFirstBasisVector + w)
          (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hfirstQ hwQ hfirstw)
      let Y₂ : e8SplitQuadraticIsometryModTwo :=
        e8SplitSymmetry (w + v.1)
          (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hwQ hvQ hwv)
      refine ⟨e8SplitQuadraticIsometryModTwoComp Y₂ Y₁, ?_⟩
      apply Subtype.ext
      change ((Y₂.1 * Y₁.1).mulVec e8SplitFirstBasisVector) = v.1
      rw [← Matrix.mulVec_mulVec e8SplitFirstBasisVector Y₂.1 Y₁.1]
      have hY₁ : Y₁.1.mulVec e8SplitFirstBasisVector = w := by
        exact e8SplitSymmetry_mulVec_of_singular_pair hfirstQ hwQ hfirstw
      have hY₂ : Y₂.1.mulVec w = v.1 := by
        exact e8SplitSymmetry_mulVec_of_singular_pair hwQ hvQ hwv
      rw [hY₁, hY₂]

/-- If the vector defining a split symmetry is polar-orthogonal to `u`, then
the symmetry fixes `u`. -/
theorem e8SplitSymmetry_mulVec_of_polar_zero
    (a u : Fin 8 → ZMod 2) (ha : e8SplitQuadraticPolynomial a = 1)
    (hpolar : e8SplitPolarBilinear u a = 0) :
    (e8SplitSymmetry a ha).1.mulVec u = u := by
  change (e8SplitSymmetryMatrix a).mulVec u = u
  rw [e8SplitSymmetryMatrix_mulVec]
  rw [hpolar]
  simp

/-- In the first-vector partner set, if a target partner is orthogonal to the
fixed second basis vector and is not the fixed second basis vector, then there
is a common partner pairing to `1` with both.  This finite-field lemma supplies
the two-symmetry case for transitivity of the first-vector stabilizer on its
partner set. -/
theorem e8SplitSecondBasisPartnerCommonPartner_exists
    (w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type))
    (horth : e8SplitPolarBilinear e8SplitSecondBasisVector w.1 = 0)
    (hne : w.1 ≠ e8SplitSecondBasisVector) :
    ∃ z : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial z = 0 ∧
        e8SplitPolarBilinear e8SplitFirstBasisVector z = 1 ∧
          e8SplitPolarBilinear e8SplitSecondBasisVector z = 1 ∧
            e8SplitPolarBilinear w.1 z = 1 := by
  decide +revert

/-- The first-vector stabilizer can send the fixed second basis vector to any
partner that pairs to `1` with it. -/
theorem e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_exists_of_pair_one
    (w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type))
    (hpair : e8SplitPolarBilinear e8SplitSecondBasisVector w.1 = 1) :
    ∃ Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer,
      e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w := by
  have hsecondQ : e8SplitQuadraticPolynomial e8SplitSecondBasisVector = 0 := by decide
  have hwQ : e8SplitQuadraticPolynomial w.1 = 0 := by
    have hwmem : w.1 ∈ e8SplitSingularPartners e8SplitFirstBasisVector := w.2
    have hsing : w.1 ∈ e8SplitSingularVectors := (Finset.mem_filter.mp hwmem).1
    exact (Finset.mem_filter.mp hsing).2
  have hfirstw : e8SplitPolarBilinear e8SplitFirstBasisVector w.1 = 1 := by
    have hwmem : w.1 ∈ e8SplitSingularPartners e8SplitFirstBasisVector := w.2
    exact (Finset.mem_filter.mp hwmem).2
  let Y : e8SplitQuadraticIsometryModTwo :=
    e8SplitSymmetry (e8SplitSecondBasisVector + w.1)
      (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hwQ hpair)
  have hfix : Y.1.mulVec e8SplitFirstBasisVector = e8SplitFirstBasisVector := by
    have horth : e8SplitPolarBilinear e8SplitFirstBasisVector
        (e8SplitSecondBasisVector + w.1) = 0 := by
      simp [e8SplitPolarBilinear, e8SplitFirstBasisVector, e8SplitSecondBasisVector,
        Pi.add_apply] at hfirstw ⊢
      rw [hfirstw]
      decide
    exact e8SplitSymmetry_mulVec_of_polar_zero (e8SplitSecondBasisVector + w.1)
      e8SplitFirstBasisVector
      (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hwQ hpair) horth
  refine ⟨⟨Y, hfix⟩, ?_⟩
  apply Subtype.ext
  exact e8SplitSymmetry_mulVec_of_singular_pair hsecondQ hwQ hpair

/-- The second-vector map from the fixed first-vector stabilizer onto the
`64` singular partners of the fixed first basis vector is surjective. -/
theorem e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective :
    Function.Surjective
      e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap := by
  intro w
  by_cases hwsecond : w.1 = e8SplitSecondBasisVector
  · refine ⟨⟨e8SplitQuadraticIsometryModTwoIdentity, ?_⟩, ?_⟩
    · simp [e8SplitQuadraticIsometryModTwoIdentity]
    · apply Subtype.ext
      simp [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap,
        e8SplitQuadraticIsometryModTwoIdentity, hwsecond]
  · by_cases hpair : e8SplitPolarBilinear e8SplitSecondBasisVector w.1 = 1
    · exact
        e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_exists_of_pair_one
          w hpair
    · have horth : e8SplitPolarBilinear e8SplitSecondBasisVector w.1 = 0 := by
        decide +revert
      rcases e8SplitSecondBasisPartnerCommonPartner_exists w horth hwsecond with
        ⟨z, hzQ, hfirstz, hsecondz, hwz⟩
      have hsecondQ : e8SplitQuadraticPolynomial e8SplitSecondBasisVector = 0 := by decide
      have hwQ : e8SplitQuadraticPolynomial w.1 = 0 := by
        have hwmem : w.1 ∈ e8SplitSingularPartners e8SplitFirstBasisVector := w.2
        have hsing : w.1 ∈ e8SplitSingularVectors := (Finset.mem_filter.mp hwmem).1
        exact (Finset.mem_filter.mp hsing).2
      have hzw : e8SplitPolarBilinear z w.1 = 1 := by
        rw [e8SplitPolarBilinear_comm]
        exact hwz
      let Y₁ : e8SplitQuadraticIsometryModTwo :=
        e8SplitSymmetry (e8SplitSecondBasisVector + z)
          (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hzQ hsecondz)
      let Y₂ : e8SplitQuadraticIsometryModTwo :=
        e8SplitSymmetry (z + w.1)
          (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hzQ hwQ hzw)
      have hY₁fix : Y₁.1.mulVec e8SplitFirstBasisVector = e8SplitFirstBasisVector := by
        have horth₁ : e8SplitPolarBilinear e8SplitFirstBasisVector
            (e8SplitSecondBasisVector + z) = 0 := by
          simp [e8SplitPolarBilinear, e8SplitFirstBasisVector, e8SplitSecondBasisVector,
            Pi.add_apply] at hfirstz ⊢
          rw [hfirstz]
          decide
        exact e8SplitSymmetry_mulVec_of_polar_zero (e8SplitSecondBasisVector + z)
          e8SplitFirstBasisVector
          (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hzQ hsecondz)
          horth₁
      have hY₂fix : Y₂.1.mulVec e8SplitFirstBasisVector = e8SplitFirstBasisVector := by
        have hfirstw : e8SplitPolarBilinear e8SplitFirstBasisVector w.1 = 1 := by
          have hwmem : w.1 ∈ e8SplitSingularPartners e8SplitFirstBasisVector := w.2
          exact (Finset.mem_filter.mp hwmem).2
        have horth₂ : e8SplitPolarBilinear e8SplitFirstBasisVector (z + w.1) = 0 := by
          simp [e8SplitPolarBilinear, e8SplitFirstBasisVector, Pi.add_apply] at hfirstz hfirstw ⊢
          rw [hfirstz, hfirstw]
          decide
        exact e8SplitSymmetry_mulVec_of_polar_zero (z + w.1) e8SplitFirstBasisVector
          (e8SplitQuadraticPolynomial_add_eq_one_of_singular_pair hzQ hwQ hzw) horth₂
      refine ⟨⟨e8SplitQuadraticIsometryModTwoComp Y₂ Y₁, ?_⟩, ?_⟩
      · change ((Y₂.1 * Y₁.1).mulVec e8SplitFirstBasisVector) = e8SplitFirstBasisVector
        rw [← Matrix.mulVec_mulVec, hY₁fix, hY₂fix]
      · apply Subtype.ext
        change ((Y₂.1 * Y₁.1).mulVec e8SplitSecondBasisVector) = w.1
        rw [← Matrix.mulVec_mulVec]
        have hY₁ : Y₁.1.mulVec e8SplitSecondBasisVector = z := by
          exact e8SplitSymmetry_mulVec_of_singular_pair hsecondQ hzQ hsecondz
        have hY₂ : Y₂.1.mulVec z = w.1 := by
          exact e8SplitSymmetry_mulVec_of_singular_pair hzQ hwQ hzw
        rw [hY₁, hY₂]

/-- A concrete right-inverse matrix for a split quadratic isometry, obtained by
choosing a preimage of each standard basis vector. -/
noncomputable def e8SplitQuadraticIsometryModTwoRightInverseMatrix
    (Y : e8SplitQuadraticIsometryModTwo) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j =>
    (Classical.choose
      (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2)))) i

/-- The chosen right-inverse matrix sends the `j`th standard basis vector to
the chosen preimage of that vector. -/
theorem e8SplitQuadraticIsometryModTwoRightInverseMatrix_mulVec_single
    (Y : e8SplitQuadraticIsometryModTwo) (j : Fin 8) :
    (e8SplitQuadraticIsometryModTwoRightInverseMatrix Y).mulVec (Pi.single j (1 : ZMod 2)) =
      Classical.choose
        (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2))) := by
  ext i
  simp [e8SplitQuadraticIsometryModTwoRightInverseMatrix, Matrix.mulVec, dotProduct,
    Pi.single_apply]

/-- The chosen matrix is a right inverse for the underlying matrix of a split
quadratic isometry. -/
theorem e8SplitQuadraticIsometryModTwo_mul_rightInverseMatrix
    (Y : e8SplitQuadraticIsometryModTwo) :
    Y.1 * e8SplitQuadraticIsometryModTwoRightInverseMatrix Y = 1 := by
  ext i j
  have hcol : (Y.1 * e8SplitQuadraticIsometryModTwoRightInverseMatrix Y).mulVec
      (Pi.single j (1 : ZMod 2)) = Pi.single j 1 := by
    rw [← Matrix.mulVec_mulVec]
    rw [e8SplitQuadraticIsometryModTwoRightInverseMatrix_mulVec_single]
    exact Classical.choose_spec
      (e8SplitQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2)))
  have hentry := congrFun hcol i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hentry

/-- Over the finite matrix monoid, the chosen right inverse is also a left
inverse. -/
theorem e8SplitQuadraticIsometryModTwo_rightInverseMatrix_mul
    (Y : e8SplitQuadraticIsometryModTwo) :
    e8SplitQuadraticIsometryModTwoRightInverseMatrix Y * Y.1 = 1 := by
  rw [← mul_eq_one_comm]
  exact e8SplitQuadraticIsometryModTwo_mul_rightInverseMatrix Y

/-- The inverse of a split quadratic isometry, packaged again as a split
quadratic isometry. -/
noncomputable def e8SplitQuadraticIsometryModTwoInverse
    (Y : e8SplitQuadraticIsometryModTwo) : e8SplitQuadraticIsometryModTwo :=
  ⟨e8SplitQuadraticIsometryModTwoRightInverseMatrix Y, by
    intro v
    have hY := Y.2 ((e8SplitQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v)
    have hmul :
        Y.1.mulVec ((e8SplitQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, e8SplitQuadraticIsometryModTwo_mul_rightInverseMatrix]
      simp
    rw [hmul] at hY
    exact hY.symm⟩

/-- Applying a split quadratic isometry and then its packaged inverse gives the
original vector. -/
theorem e8SplitQuadraticIsometryModTwo_inverse_mulVec
    (Y : e8SplitQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) :
    (e8SplitQuadraticIsometryModTwoInverse Y).1.mulVec (Y.1.mulVec v) = v := by
  change (e8SplitQuadraticIsometryModTwoRightInverseMatrix Y).mulVec (Y.1.mulVec v) = v
  rw [Matrix.mulVec_mulVec, e8SplitQuadraticIsometryModTwo_rightInverseMatrix_mul]
  simp

/-- Applying the packaged inverse and then the original split quadratic isometry
gives the original vector. -/
theorem e8SplitQuadraticIsometryModTwo_mulVec_inverse
    (Y : e8SplitQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) :
    Y.1.mulVec ((e8SplitQuadraticIsometryModTwoInverse Y).1.mulVec v) = v := by
  change Y.1.mulVec ((e8SplitQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v) = v
  rw [Matrix.mulVec_mulVec, e8SplitQuadraticIsometryModTwo_mul_rightInverseMatrix]
  simp

/-- Any first-vector fiber is equivalent to the fixed first-vector stabilizer.
This is the orbit-stabilizer transport supplied by first-vector transitivity and
the packaged inverse isometry. -/
noncomputable def e8SplitQuadraticIsometryModTwoFirstVectorFiberEquivStabilizer
    (v : e8SplitNonzeroSingularVectors) :
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizer ≃
      {Y : e8SplitQuadraticIsometryModTwo //
        e8SplitQuadraticIsometryModTwoFirstVectorMap Y = v} := by
  let T : e8SplitQuadraticIsometryModTwo :=
    Classical.choose (e8SplitQuadraticIsometryModTwoFirstVectorMap_surjective v)
  have hT : e8SplitQuadraticIsometryModTwoFirstVectorMap T = v :=
    Classical.choose_spec (e8SplitQuadraticIsometryModTwoFirstVectorMap_surjective v)
  refine
    { toFun := fun H => ?_
      invFun := fun K => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨e8SplitQuadraticIsometryModTwoComp T H.1, ?_⟩
    apply Subtype.ext
    change ((T.1 * H.1.1).mulVec e8SplitFirstBasisVector) = v.1
    rw [← Matrix.mulVec_mulVec, H.2]
    have hTval := congrArg Subtype.val hT
    simpa [e8SplitQuadraticIsometryModTwoFirstVectorMap] using hTval
  · refine ⟨e8SplitQuadraticIsometryModTwoComp (e8SplitQuadraticIsometryModTwoInverse T) K.1, ?_⟩
    change (((e8SplitQuadraticIsometryModTwoInverse T).1 * K.1.1).mulVec
        e8SplitFirstBasisVector) = e8SplitFirstBasisVector
    rw [← Matrix.mulVec_mulVec]
    have hKval := congrArg Subtype.val K.2
    have hKfirst : K.1.1.mulVec e8SplitFirstBasisVector = v.1 := by
      simpa [e8SplitQuadraticIsometryModTwoFirstVectorMap] using hKval
    rw [hKfirst]
    have hTval := congrArg Subtype.val hT
    have hTfirst : T.1.mulVec e8SplitFirstBasisVector = v.1 := by
      simpa [e8SplitQuadraticIsometryModTwoFirstVectorMap] using hTval
    rw [← hTfirst]
    exact e8SplitQuadraticIsometryModTwo_inverse_mulVec T e8SplitFirstBasisVector
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    change ((e8SplitQuadraticIsometryModTwoInverse T).1 * (T.1 * H.1.1)) = H.1.1
    rw [← Matrix.mul_assoc]
    change (e8SplitQuadraticIsometryModTwoRightInverseMatrix T * T.1) * H.1.1 = H.1.1
    rw [e8SplitQuadraticIsometryModTwo_rightInverseMatrix_mul, Matrix.one_mul]
  · intro K
    apply Subtype.ext
    apply Subtype.ext
    change (T.1 * ((e8SplitQuadraticIsometryModTwoInverse T).1 * K.1.1)) = K.1.1
    rw [← Matrix.mul_assoc]
    change (T.1 * e8SplitQuadraticIsometryModTwoRightInverseMatrix T) * K.1.1 = K.1.1
    rw [e8SplitQuadraticIsometryModTwo_mul_rightInverseMatrix, Matrix.one_mul]

/-- All first-vector fibers have the cardinality of the fixed first-vector
stabilizer. -/
theorem e8SplitQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer_at
    (v : e8SplitNonzeroSingularVectors) :
    Nat.card {Y : e8SplitQuadraticIsometryModTwo //
      e8SplitQuadraticIsometryModTwoFirstVectorMap Y = v} =
        Nat.card e8SplitQuadraticIsometryModTwoFirstVectorStabilizer := by
  exact (Nat.card_congr
    (e8SplitQuadraticIsometryModTwoFirstVectorFiberEquivStabilizer v)).symm

/-- The first-vector fibers are uniform, so the split E8 base count reduces
to the remaining second-vector stabilizer fiber cardinality. -/
theorem
    e8SplitQuadraticIsometryModTwo_natCard_eq_8640_mul_of_stabilizerSecondVector_fiber_card
    (c : ℕ)
    (hsecond : ∀ w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type),
      Nat.card {Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitQuadraticIsometryModTwo = 8640 * c :=
  e8SplitQuadraticIsometryModTwo_natCard_eq_8640_mul_of_secondVector_fiber_card c
    (fun v => e8SplitQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer_at v)
    hsecond

/-- Composition inside the fixed first-vector stabilizer. -/
def e8SplitQuadraticIsometryModTwoFirstVectorStabilizerComp
    (Y Z : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer) :
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizer :=
  ⟨e8SplitQuadraticIsometryModTwoComp Y.1 Z.1, by
    change ((Y.1.1 * Z.1.1).mulVec e8SplitFirstBasisVector) = e8SplitFirstBasisVector
    rw [← Matrix.mulVec_mulVec, Z.2, Y.2]⟩

/-- The packaged inverse of a first-vector stabilizer again fixes the first
basis vector. -/
noncomputable def e8SplitQuadraticIsometryModTwoFirstVectorStabilizerInverse
    (Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer) :
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizer :=
  ⟨e8SplitQuadraticIsometryModTwoInverse Y.1, by
    have h := e8SplitQuadraticIsometryModTwo_inverse_mulVec Y.1 e8SplitFirstBasisVector
    rw [Y.2] at h
    exact h⟩

/-- The stabilizer of the fixed hyperbolic pair `(e₀,e₁)` inside the split
quadratic isometry group.  Its order is the remaining group-order factor in the
split E8 base count. -/
abbrev e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer : Type :=
  {Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer //
    e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y =
      ⟨e8SplitSecondBasisVector, e8SplitSecondBasisVector_mem_singularPartners_firstBasisVector⟩}

noncomputable instance :
    Fintype e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  unfold e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer
  infer_instance

/-- Any second-vector fiber of the first-vector stabilizer is equivalent to the
fixed hyperbolic-pair stabilizer. -/
noncomputable def
    e8SplitQuadraticIsometryModTwoSecondVectorFiberEquivFirstSecondStabilizer
    (w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type)) :
    e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer ≃
      {Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} := by
  let T : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer :=
    Classical.choose
      (e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective w)
  have hT : e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap T = w :=
    Classical.choose_spec
      (e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective w)
  refine
    { toFun := fun H => ?_
      invFun := fun K => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨e8SplitQuadraticIsometryModTwoFirstVectorStabilizerComp T H.1, ?_⟩
    apply Subtype.ext
    change ((T.1.1 * H.1.1.1).mulVec e8SplitSecondBasisVector) = w.1
    rw [← Matrix.mulVec_mulVec]
    have hHsecond := congrArg Subtype.val H.2
    have hHsecond' : H.1.1.1.mulVec e8SplitSecondBasisVector = e8SplitSecondBasisVector := by
      simpa [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap]
        using hHsecond
    rw [hHsecond']
    have hTval := congrArg Subtype.val hT
    simpa [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hTval
  · refine ⟨e8SplitQuadraticIsometryModTwoFirstVectorStabilizerComp
        (e8SplitQuadraticIsometryModTwoFirstVectorStabilizerInverse T) K.1, ?_⟩
    apply Subtype.ext
    change (((e8SplitQuadraticIsometryModTwoFirstVectorStabilizerInverse T).1.1 * K.1.1.1).mulVec
        e8SplitSecondBasisVector) = e8SplitSecondBasisVector
    rw [← Matrix.mulVec_mulVec]
    have hKval := congrArg Subtype.val K.2
    have hKsecond : K.1.1.1.mulVec e8SplitSecondBasisVector = w.1 := by
      simpa [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hKval
    rw [hKsecond]
    have hTval := congrArg Subtype.val hT
    have hTsecond : T.1.1.mulVec e8SplitSecondBasisVector = w.1 := by
      simpa [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hTval
    rw [← hTsecond]
    exact e8SplitQuadraticIsometryModTwo_inverse_mulVec T.1 e8SplitSecondBasisVector
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change ((e8SplitQuadraticIsometryModTwoInverse T.1).1 * (T.1.1 * H.1.1.1)) = H.1.1.1
    rw [← Matrix.mul_assoc]
    change (e8SplitQuadraticIsometryModTwoRightInverseMatrix T.1 * T.1.1) * H.1.1.1 = H.1.1.1
    rw [e8SplitQuadraticIsometryModTwo_rightInverseMatrix_mul, Matrix.one_mul]
  · intro K
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (T.1.1 * ((e8SplitQuadraticIsometryModTwoInverse T.1).1 * K.1.1.1)) = K.1.1.1
    rw [← Matrix.mul_assoc]
    change (T.1.1 * e8SplitQuadraticIsometryModTwoRightInverseMatrix T.1) * K.1.1.1 = K.1.1.1
    rw [e8SplitQuadraticIsometryModTwo_mul_rightInverseMatrix, Matrix.one_mul]

/-- All second-vector fibers have the cardinality of the fixed hyperbolic-pair
stabilizer. -/
theorem e8SplitQuadraticIsometryModTwo_secondVectorFiber_natCard_eq_firstSecondStabilizer_at
    (w : (e8SplitSingularPartners e8SplitFirstBasisVector : Type)) :
    Nat.card {Y : e8SplitQuadraticIsometryModTwoFirstVectorStabilizer //
      e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} =
        Nat.card e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  exact (Nat.card_congr
    (e8SplitQuadraticIsometryModTwoSecondVectorFiberEquivFirstSecondStabilizer w)).symm

/-- The split E8 base count is reduced to the order of the fixed hyperbolic-pair
stabilizer. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_8640_mul_firstSecondStabilizer :
    Nat.card e8SplitQuadraticIsometryModTwo =
      8640 * Nat.card e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer :=
  e8SplitQuadraticIsometryModTwo_natCard_eq_8640_mul_of_stabilizerSecondVector_fiber_card
    (Nat.card e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    (fun w =>
      e8SplitQuadraticIsometryModTwo_secondVectorFiber_natCard_eq_firstSecondStabilizer_at w)

/-- Pairing with the fixed first basis vector reads the second coordinate. -/
theorem e8SplitPolarBilinear_firstBasis_eq_coord_one (v : Fin 8 → ZMod 2) :
    e8SplitPolarBilinear e8SplitFirstBasisVector v = v 1 := by
  simp [e8SplitPolarBilinear, e8SplitFirstBasisVector]

/-- Pairing with the fixed second basis vector reads the first coordinate. -/
theorem e8SplitPolarBilinear_secondBasis_eq_coord_zero (v : Fin 8 → ZMod 2) :
    e8SplitPolarBilinear e8SplitSecondBasisVector v = v 0 := by
  simp [e8SplitPolarBilinear, e8SplitSecondBasisVector]

/-- The fixed hyperbolic-pair stabilizer preserves the polar-orthogonal
complement of that pair.  This is the structural input for replacing the
remaining pair-stabilizer order by a six-dimensional split-isometry count. -/
theorem e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer_preserves_pairComplement
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    {v : Fin 8 → ZMod 2}
    (hfirst : e8SplitPolarBilinear e8SplitFirstBasisVector v = 0)
    (hsecond : e8SplitPolarBilinear e8SplitSecondBasisVector v = 0) :
    e8SplitPolarBilinear e8SplitFirstBasisVector (Y.1.1.1.mulVec v) = 0 ∧
      e8SplitPolarBilinear e8SplitSecondBasisVector (Y.1.1.1.mulVec v) = 0 := by
  have hYfirst : Y.1.1.1.mulVec e8SplitFirstBasisVector = e8SplitFirstBasisVector :=
    Y.1.2
  have hYsecond : Y.1.1.1.mulVec e8SplitSecondBasisVector = e8SplitSecondBasisVector := by
    have hval := congrArg Subtype.val Y.2
    simpa [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hval
  constructor
  · have hpolar :=
      e8SplitQuadraticIsometryModTwo_preserves_polar Y.1.1 e8SplitFirstBasisVector v
    rw [hYfirst, hfirst] at hpolar
    exact hpolar
  · have hpolar :=
      e8SplitQuadraticIsometryModTwo_preserves_polar Y.1.1 e8SplitSecondBasisVector v
    rw [hYsecond, hsecond] at hpolar
    exact hpolar

/-- Coordinate form of complement preservation for vectors with zero first two
coordinates. -/
theorem e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    {v : Fin 8 → ZMod 2} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    (Y.1.1.1.mulVec v) 0 = 0 ∧ (Y.1.1.1.mulVec v) 1 = 0 := by
  have hcomp :=
    e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer_preserves_pairComplement Y
      (by simpa [e8SplitPolarBilinear_firstBasis_eq_coord_one] using h1)
      (by simpa [e8SplitPolarBilinear_secondBasis_eq_coord_zero] using h0)
  constructor
  · simpa [e8SplitPolarBilinear_secondBasis_eq_coord_zero] using hcomp.2
  · simpa [e8SplitPolarBilinear_firstBasis_eq_coord_one] using hcomp.1

/-- Once the fixed hyperbolic-pair stabilizer has order `40320`, the split E8
quadratic-isometry base count is `348364800`. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_348364800_of_firstSecondStabilizer_card
    (hcard : Nat.card e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer = 40320) :
    Nat.card e8SplitQuadraticIsometryModTwo = 348364800 := by
  rw [e8SplitQuadraticIsometryModTwo_natCard_eq_8640_mul_firstSecondStabilizer, hcard]

/-- The tail index embedding for the six-dimensional complement of the fixed
hyperbolic plane. -/
def e8SplitTailIndex : Fin 6 → Fin 8
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 7

/-- The split quadratic polynomial on the six-dimensional complement of the
fixed hyperbolic plane. -/
def e8SplitTailQuadraticPolynomial (x : Fin 6 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 3 + x 4 * x 5

/-- Embed a six-dimensional complement vector into the full split E8 space. -/
def e8SplitTailVector (x : Fin 6 → ZMod 2) : Fin 8 → ZMod 2
  | 0 => 0
  | 1 => 0
  | 2 => x 0
  | 3 => x 1
  | 4 => x 2
  | 5 => x 3
  | 6 => x 4
  | 7 => x 5

/-- Extract the six complement coordinates from a full split E8 vector. -/
def e8SplitTailCoordinates (v : Fin 8 → ZMod 2) : Fin 6 → ZMod 2
  | 0 => v 2
  | 1 => v 3
  | 2 => v 4
  | 3 => v 5
  | 4 => v 6
  | 5 => v 7

/-- Tail-coordinate extraction is inverse to tail-vector embedding. -/
theorem e8SplitTailCoordinates_tailVector (x : Fin 6 → ZMod 2) :
    e8SplitTailCoordinates (e8SplitTailVector x) = x := by
  funext i
  fin_cases i <;> rfl

/-- A full vector with zero first two coordinates is recovered from its tail
coordinates. -/
theorem e8SplitTailVector_tailCoordinates_of_zero
    {v : Fin 8 → ZMod 2} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    e8SplitTailVector (e8SplitTailCoordinates v) = v := by
  funext i
  fin_cases i <;> simp [e8SplitTailVector, e8SplitTailCoordinates, h0, h1]

/-- The full split polynomial restricts to the six-dimensional tail polynomial
on the complement of the fixed hyperbolic plane. -/
theorem e8SplitQuadraticPolynomial_tailVector (x : Fin 6 → ZMod 2) :
    e8SplitQuadraticPolynomial (e8SplitTailVector x) =
      e8SplitTailQuadraticPolynomial x := by
  simp [e8SplitQuadraticPolynomial, e8SplitTailQuadraticPolynomial, e8SplitTailVector]

/-- A matrix over `ZMod 2` preserving the split quadratic polynomial on the
six-dimensional complement. -/
abbrev e8SplitTailQuadraticIsometryModTwo : Type :=
  {Y : Matrix (Fin 6) (Fin 6) (ZMod 2) //
    ∀ v : Fin 6 → ZMod 2,
      e8SplitTailQuadraticPolynomial (Y.mulVec v) = e8SplitTailQuadraticPolynomial v}

noncomputable instance : Fintype e8SplitTailQuadraticIsometryModTwo := by
  unfold e8SplitTailQuadraticIsometryModTwo
  infer_instance

/-- The polar form attached to the six-dimensional tail split quadratic
polynomial over `𝔽₂`. -/
noncomputable def e8SplitTailPolarBilinear (v w : Fin 6 → ZMod 2) : ZMod 2 :=
  v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2 + v 4 * w 5 + v 5 * w 4

/-- The singular vectors for the six-dimensional tail split model over `𝔽₂`. -/
noncomputable def e8SplitTailSingularVectors : Finset (Fin 6 → ZMod 2) := by
  classical
  exact Finset.univ.filter fun v => e8SplitTailQuadraticPolynomial v = 0

/-- The nonzero singular vectors for the six-dimensional tail split model. -/
noncomputable def e8SplitTailNonzeroSingularVectors : Finset (Fin 6 → ZMod 2) := by
  classical
  exact e8SplitTailSingularVectors.filter fun v => v ≠ 0

/-- The tail singular partners of a vector, i.e. singular vectors pairing to `1`
with it under the tail polar form. -/
noncomputable def e8SplitTailSingularPartners (v : Fin 6 → ZMod 2) :
    Finset (Fin 6 → ZMod 2) := by
  classical
  exact e8SplitTailSingularVectors.filter fun w => e8SplitTailPolarBilinear v w = 1

/-- The six-dimensional tail model has `36` singular vectors over `𝔽₂`, including zero. -/
theorem e8SplitTailSingularVectors_card :
    e8SplitTailSingularVectors.card = 36 := by
  decide

/-- The six-dimensional tail model has `35` nonzero singular vectors over `𝔽₂`. -/
theorem e8SplitTailNonzeroSingularVectors_card :
    e8SplitTailNonzeroSingularVectors.card = 35 := by
  decide

/-- A fixed nonzero singular vector in the first tail hyperbolic plane. -/
def e8SplitTailFirstBasisVector : Fin 6 → ZMod 2 :=
  fun i => if i = 0 then 1 else 0

/-- The fixed first tail basis vector is a nonzero singular vector. -/
theorem e8SplitTailFirstBasisVector_mem_nonzeroSingular :
    e8SplitTailFirstBasisVector ∈ e8SplitTailNonzeroSingularVectors := by
  decide

/-- The second basis vector in the first tail hyperbolic plane. -/
def e8SplitTailSecondBasisVector : Fin 6 → ZMod 2 :=
  fun i => if i = 1 then 1 else 0

/-- The second tail basis vector is a singular partner of the first one. -/
theorem e8SplitTailSecondBasisVector_mem_singularPartners_firstBasisVector :
    e8SplitTailSecondBasisVector ∈ e8SplitTailSingularPartners e8SplitTailFirstBasisVector := by
  decide

/-- The fixed first tail basis vector has exactly `16` singular partners. -/
theorem e8SplitTailSingularPartners_firstBasisVector_card :
    (e8SplitTailSingularPartners e8SplitTailFirstBasisVector).card = 16 := by
  decide

/-- The tail polar form is the polarization of the tail split quadratic polynomial over `𝔽₂`. -/
theorem e8SplitTailPolarBilinear_eq_quadratic_add (v w : Fin 6 → ZMod 2) :
    e8SplitTailPolarBilinear v w =
      e8SplitTailQuadraticPolynomial (v + w) +
        e8SplitTailQuadraticPolynomial v + e8SplitTailQuadraticPolynomial w := by
  simp only [e8SplitTailPolarBilinear, e8SplitTailQuadraticPolynomial, Pi.add_apply]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [h2]

/-- Tail quadratic isometries preserve the associated polar form. -/
theorem e8SplitTailQuadraticIsometryModTwo_preserves_polar
    (Y : e8SplitTailQuadraticIsometryModTwo) (v w : Fin 6 → ZMod 2) :
    e8SplitTailPolarBilinear (Y.1.mulVec v) (Y.1.mulVec w) =
      e8SplitTailPolarBilinear v w := by
  rw [e8SplitTailPolarBilinear_eq_quadratic_add,
    e8SplitTailPolarBilinear_eq_quadratic_add]
  rw [← Matrix.mulVec_add]
  rw [Y.2 (v + w), Y.2 v, Y.2 w]

/-- The tail polar form has zero left kernel. -/
theorem e8SplitTailPolarBilinear_left_kernel_eq_zero
    (v : Fin 6 → ZMod 2)
    (h : ∀ w : Fin 6 → ZMod 2, e8SplitTailPolarBilinear v w = 0) :
    v = 0 := by
  funext i
  fin_cases i <;>
    first
    | simpa [e8SplitTailPolarBilinear] using h (Pi.single (1 : Fin 6) (1 : ZMod 2))
    | simpa [e8SplitTailPolarBilinear] using h (Pi.single (0 : Fin 6) (1 : ZMod 2))
    | simpa [e8SplitTailPolarBilinear] using h (Pi.single (3 : Fin 6) (1 : ZMod 2))
    | simpa [e8SplitTailPolarBilinear] using h (Pi.single (2 : Fin 6) (1 : ZMod 2))
    | simpa [e8SplitTailPolarBilinear] using h (Pi.single (5 : Fin 6) (1 : ZMod 2))
    | simpa [e8SplitTailPolarBilinear] using h (Pi.single (4 : Fin 6) (1 : ZMod 2))

/-- A tail quadratic isometry has trivial kernel. -/
theorem e8SplitTailQuadraticIsometryModTwo_mulVec_eq_zero_iff
    (Y : e8SplitTailQuadraticIsometryModTwo) (v : Fin 6 → ZMod 2) :
    Y.1.mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    apply e8SplitTailPolarBilinear_left_kernel_eq_zero v
    intro w
    rw [← e8SplitTailQuadraticIsometryModTwo_preserves_polar Y v w, hv]
    simp [e8SplitTailPolarBilinear]
  · intro hv
    rw [hv, Matrix.mulVec_zero]

/-- A tail quadratic isometry is injective on vectors. -/
theorem e8SplitTailQuadraticIsometryModTwo_mulVec_injective
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    Function.Injective Y.1.mulVec := by
  intro v w h
  have hker : Y.1.mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hz := (e8SplitTailQuadraticIsometryModTwo_mulVec_eq_zero_iff Y (v - w)).mp hker
  exact sub_eq_zero.mp hz

/-- A tail quadratic isometry is surjective on vectors. -/
theorem e8SplitTailQuadraticIsometryModTwo_mulVec_surjective
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    Function.Surjective Y.1.mulVec := by
  exact Finite.surjective_of_injective (e8SplitTailQuadraticIsometryModTwo_mulVec_injective Y)

/-- A tail quadratic isometry sends nonzero singular vectors to nonzero singular vectors. -/
theorem e8SplitTailQuadraticIsometryModTwo_mulVec_mem_nonzeroSingular
    (Y : e8SplitTailQuadraticIsometryModTwo) {v : Fin 6 → ZMod 2}
    (hv : v ∈ e8SplitTailNonzeroSingularVectors) :
    Y.1.mulVec v ∈ e8SplitTailNonzeroSingularVectors := by
  simp [e8SplitTailNonzeroSingularVectors, e8SplitTailSingularVectors] at hv ⊢
  exact ⟨by rw [Y.2 v, hv.1], fun hzero => hv.2
    ((e8SplitTailQuadraticIsometryModTwo_mulVec_eq_zero_iff Y v).mp hzero)⟩

/-- The identity matrix is a tail quadratic isometry. -/
def e8SplitTailQuadraticIsometryModTwoIdentity : e8SplitTailQuadraticIsometryModTwo :=
  ⟨1, by intro v; simp⟩

/-- Tail quadratic isometries are closed under matrix composition. -/
def e8SplitTailQuadraticIsometryModTwoComp
    (Y Z : e8SplitTailQuadraticIsometryModTwo) : e8SplitTailQuadraticIsometryModTwo :=
  ⟨Y.1 * Z.1, by
    intro v
    rw [← Matrix.mulVec_mulVec v Y.1 Z.1]
    rw [Y.2 (Z.1.mulVec v), Z.2 v]⟩

/-- Evaluation at the fixed first tail basis vector, as a map into tail nonzero singular vectors. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoFirstVectorMap :
    e8SplitTailQuadraticIsometryModTwo → e8SplitTailNonzeroSingularVectors := fun Y =>
  ⟨Y.1.mulVec e8SplitTailFirstBasisVector,
    e8SplitTailQuadraticIsometryModTwo_mulVec_mem_nonzeroSingular Y
      e8SplitTailFirstBasisVector_mem_nonzeroSingular⟩

/-- Uniform fibers of the tail first-vector map give the tail isometry count. -/
theorem e8SplitTailQuadraticIsometryModTwo_natCard_eq_nonzeroSingular_mul_of_firstVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ v : e8SplitTailNonzeroSingularVectors,
      Nat.card {Y : e8SplitTailQuadraticIsometryModTwo //
        e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y = v} = c) :
    Nat.card e8SplitTailQuadraticIsometryModTwo =
      Nat.card e8SplitTailNonzeroSingularVectors * c := by
  exact nat_card_eq_mul_of_fiber_card e8SplitTailQuadraticIsometryModTwoFirstVectorMap c hfiber

/-- With the known `35` tail nonzero singular vectors, uniform first-vector fibers give a compact count. -/
theorem e8SplitTailQuadraticIsometryModTwo_natCard_eq_35_mul_of_firstVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ v : e8SplitTailNonzeroSingularVectors,
      Nat.card {Y : e8SplitTailQuadraticIsometryModTwo //
        e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y = v} = c) :
    Nat.card e8SplitTailQuadraticIsometryModTwo = 35 * c := by
  rw [e8SplitTailQuadraticIsometryModTwo_natCard_eq_nonzeroSingular_mul_of_firstVector_fiber_card
    c hfiber]
  rw [Nat.card_eq_finsetCard e8SplitTailNonzeroSingularVectors,
    e8SplitTailNonzeroSingularVectors_card]

/-- The stabilizer of the fixed first tail basis vector inside the tail isometry type. -/
abbrev e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer : Type :=
  {Y : e8SplitTailQuadraticIsometryModTwo //
    Y.1.mulVec e8SplitTailFirstBasisVector = e8SplitTailFirstBasisVector}

noncomputable instance :
    Fintype e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer := by
  unfold e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer
  infer_instance

/-- The fiber of the tail first-vector map over the fixed first vector is exactly the tail first-vector stabilizer. -/
noncomputable def e8SplitTailQuadraticIsometryModTwo_firstVectorFiberEquivStabilizer :
    {Y : e8SplitTailQuadraticIsometryModTwo //
      e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y =
        ⟨e8SplitTailFirstBasisVector, e8SplitTailFirstBasisVector_mem_nonzeroSingular⟩} ≃
      e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer where
  toFun Y := by
    refine ⟨Y.1, ?_⟩
    have h := congrArg Subtype.val Y.2
    simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorMap] using h
  invFun Y := by
    refine ⟨Y.1, ?_⟩
    apply Subtype.ext
    exact Y.2
  left_inv Y := by
    apply Subtype.ext
    rfl
  right_inv Y := by
    apply Subtype.ext
    rfl

/-- Cardinality form of the equivalence between the fixed tail first-vector fiber and stabilizer. -/
theorem e8SplitTailQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer :
    Nat.card {Y : e8SplitTailQuadraticIsometryModTwo //
      e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y =
        ⟨e8SplitTailFirstBasisVector, e8SplitTailFirstBasisVector_mem_nonzeroSingular⟩} =
      Nat.card e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer := by
  exact Nat.card_congr e8SplitTailQuadraticIsometryModTwo_firstVectorFiberEquivStabilizer

/-- The tail polar form is symmetric. -/
theorem e8SplitTailPolarBilinear_comm (v w : Fin 6 → ZMod 2) :
    e8SplitTailPolarBilinear v w = e8SplitTailPolarBilinear w v := by
  simp only [e8SplitTailPolarBilinear]
  ring_nf

/-- The coordinate vector dual to `a` for the tail split polar form. -/
def e8SplitTailPolarDualVector (a : Fin 6 → ZMod 2) : Fin 6 → ZMod 2
  | 0 => a 1
  | 1 => a 0
  | 2 => a 3
  | 3 => a 2
  | 4 => a 5
  | 5 => a 4

/-- The characteristic-two orthogonal symmetry attached to a tail vector `a`. -/
def e8SplitTailSymmetryMatrix (a : Fin 6 → ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j => (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j +
    a i * e8SplitTailPolarDualVector a j

/-- The matrix formula for the characteristic-two tail symmetry. -/
theorem e8SplitTailSymmetryMatrix_mulVec
    (a x : Fin 6 → ZMod 2) :
    (e8SplitTailSymmetryMatrix a).mulVec x =
      fun i => x i + e8SplitTailPolarBilinear x a * a i := by
  ext i
  fin_cases i <;>
    simp [e8SplitTailSymmetryMatrix, e8SplitTailPolarDualVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_six, e8SplitTailPolarBilinear, Matrix.one_apply]
  <;> ring_nf

/-- Quadratic expansion for the tail split polynomial along a scalar multiple of a vector. -/
theorem e8SplitTailQuadraticPolynomial_add_smul
    (x a : Fin 6 → ZMod 2) (c : ZMod 2) :
    e8SplitTailQuadraticPolynomial (fun i => x i + c * a i) =
      e8SplitTailQuadraticPolynomial x + c^2 * e8SplitTailQuadraticPolynomial a +
        c * e8SplitTailPolarBilinear x a := by
  simp only [e8SplitTailQuadraticPolynomial, e8SplitTailPolarBilinear]
  ring_nf

/-- If `Q(a)=1`, the characteristic-two tail symmetry preserves the tail split polynomial. -/
theorem e8SplitTailQuadraticPolynomial_symmetry_apply
    (a x : Fin 6 → ZMod 2) (ha : e8SplitTailQuadraticPolynomial a = 1) :
    e8SplitTailQuadraticPolynomial (fun i => x i + e8SplitTailPolarBilinear x a * a i) =
      e8SplitTailQuadraticPolynomial x := by
  rw [e8SplitTailQuadraticPolynomial_add_smul]
  rw [ha]
  rw [mul_one]
  let b : ZMod 2 := e8SplitTailPolarBilinear x a
  change e8SplitTailQuadraticPolynomial x + b ^ 2 + b * b = e8SplitTailQuadraticPolynomial x
  have hsquare (z : ZMod 2) : z ^ 2 = z := by
    fin_cases z <;> decide
  have hbsq : b ^ 2 = b := hsquare b
  have hbmul : b * b = b := by
    simpa [pow_two] using hsquare b
  rw [hbsq, hbmul]
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  calc
    e8SplitTailQuadraticPolynomial x + b + b =
        e8SplitTailQuadraticPolynomial x + (b + b) := by rw [add_assoc]
    _ = e8SplitTailQuadraticPolynomial x := by rw [hdouble, add_zero]

/-- The characteristic-two tail symmetry as a tail quadratic isometry. -/
def e8SplitTailSymmetry
    (a : Fin 6 → ZMod 2) (ha : e8SplitTailQuadraticPolynomial a = 1) :
    e8SplitTailQuadraticIsometryModTwo :=
  ⟨e8SplitTailSymmetryMatrix a, by
    intro x
    rw [e8SplitTailSymmetryMatrix_mulVec]
    exact e8SplitTailQuadraticPolynomial_symmetry_apply a x ha⟩

/-- If two tail singular vectors pair to `1`, their sum has tail norm `1`. -/
theorem e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair
    {u v : Fin 6 → ZMod 2}
    (hu : e8SplitTailQuadraticPolynomial u = 0)
    (hv : e8SplitTailQuadraticPolynomial v = 0)
    (hpair : e8SplitTailPolarBilinear u v = 1) :
    e8SplitTailQuadraticPolynomial (u + v) = 1 := by
  have hpol := e8SplitTailPolarBilinear_eq_quadratic_add u v
  rw [hpol, hu, hv] at hpair
  simpa using hpair

/-- If two tail singular vectors pair to `1`, the attached symmetry sends the first vector to the second. -/
theorem e8SplitTailSymmetry_mulVec_of_singular_pair
    {u v : Fin 6 → ZMod 2}
    (hu : e8SplitTailQuadraticPolynomial u = 0)
    (hv : e8SplitTailQuadraticPolynomial v = 0)
    (hpair : e8SplitTailPolarBilinear u v = 1) :
    (e8SplitTailSymmetry (u + v)
      (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hu hv hpair)).1.mulVec u = v := by
  change (e8SplitTailSymmetryMatrix (u + v)).mulVec u = v
  rw [e8SplitTailSymmetryMatrix_mulVec]
  have hpolar : e8SplitTailPolarBilinear u (u + v) = 1 := by
    simp [e8SplitTailPolarBilinear, Pi.add_apply] at hpair ⊢
    ring_nf at hpair ⊢
    have h2 : (2 : ZMod 2) = 0 := by decide
    simpa [h2] using hpair
  funext i
  rw [hpolar]
  simp only [one_mul, Pi.add_apply]
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [← add_assoc, hdouble, zero_add]

/-- The first-tail-vector orbit contains every nonzero singular vector pairing to `1` with the fixed first tail basis vector. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstVectorMap_exists_of_pair_one
    (v : e8SplitTailNonzeroSingularVectors)
    (hpair : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector v.1 = 1) :
    ∃ Y : e8SplitTailQuadraticIsometryModTwo,
      e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y = v := by
  have hfirstQ : e8SplitTailQuadraticPolynomial e8SplitTailFirstBasisVector = 0 := by
    have hmem : e8SplitTailFirstBasisVector ∈ e8SplitTailNonzeroSingularVectors :=
      e8SplitTailFirstBasisVector_mem_nonzeroSingular
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hvQ : e8SplitTailQuadraticPolynomial v.1 = 0 := by
    have hmem : v.1 ∈ e8SplitTailNonzeroSingularVectors := v.2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  let Y : e8SplitTailQuadraticIsometryModTwo :=
    e8SplitTailSymmetry (e8SplitTailFirstBasisVector + v.1)
      (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hfirstQ hvQ hpair)
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  exact e8SplitTailSymmetry_mulVec_of_singular_pair hfirstQ hvQ hpair

/-- Orthogonal nonzero tail singular vectors have a tail singular common partner. -/
theorem e8SplitTailFirstBasisCommonSingularPartner_exists
    (v : e8SplitTailNonzeroSingularVectors)
    (horth : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector v.1 = 0)
    (hne : v.1 ≠ e8SplitTailFirstBasisVector) :
    ∃ w : Fin 6 → ZMod 2,
      e8SplitTailQuadraticPolynomial w = 0 ∧
        e8SplitTailPolarBilinear e8SplitTailFirstBasisVector w = 1 ∧
          e8SplitTailPolarBilinear v.1 w = 1 := by
  decide +revert

/-- The first-tail-vector map is surjective onto the `35` nonzero singular vectors. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstVectorMap_surjective :
    Function.Surjective e8SplitTailQuadraticIsometryModTwoFirstVectorMap := by
  intro v
  have hfirstQ : e8SplitTailQuadraticPolynomial e8SplitTailFirstBasisVector = 0 := by
    have hmem : e8SplitTailFirstBasisVector ∈ e8SplitTailNonzeroSingularVectors :=
      e8SplitTailFirstBasisVector_mem_nonzeroSingular
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hvQ : e8SplitTailQuadraticPolynomial v.1 = 0 := by
    have hmem : v.1 ∈ e8SplitTailNonzeroSingularVectors := v.2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  by_cases hvfirst : v.1 = e8SplitTailFirstBasisVector
  · refine ⟨e8SplitTailQuadraticIsometryModTwoIdentity, ?_⟩
    apply Subtype.ext
    simp [e8SplitTailQuadraticIsometryModTwoFirstVectorMap,
      e8SplitTailQuadraticIsometryModTwoIdentity, hvfirst]
  · by_cases hpair : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector v.1 = 1
    · exact e8SplitTailQuadraticIsometryModTwoFirstVectorMap_exists_of_pair_one v hpair
    · have horth : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector v.1 = 0 := by
        decide +revert
      rcases e8SplitTailFirstBasisCommonSingularPartner_exists v horth hvfirst with
        ⟨w, hwQ, hfirstw, hvw⟩
      have hwv : e8SplitTailPolarBilinear w v.1 = 1 := by
        rw [e8SplitTailPolarBilinear_comm]
        exact hvw
      let Y₁ : e8SplitTailQuadraticIsometryModTwo :=
        e8SplitTailSymmetry (e8SplitTailFirstBasisVector + w)
          (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hfirstQ hwQ hfirstw)
      let Y₂ : e8SplitTailQuadraticIsometryModTwo :=
        e8SplitTailSymmetry (w + v.1)
          (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hwQ hvQ hwv)
      refine ⟨e8SplitTailQuadraticIsometryModTwoComp Y₂ Y₁, ?_⟩
      apply Subtype.ext
      change ((Y₂.1 * Y₁.1).mulVec e8SplitTailFirstBasisVector) = v.1
      rw [← Matrix.mulVec_mulVec e8SplitTailFirstBasisVector Y₂.1 Y₁.1]
      have hY₁ : Y₁.1.mulVec e8SplitTailFirstBasisVector = w := by
        exact e8SplitTailSymmetry_mulVec_of_singular_pair hfirstQ hwQ hfirstw
      have hY₂ : Y₂.1.mulVec w = v.1 := by
        exact e8SplitTailSymmetry_mulVec_of_singular_pair hwQ hvQ hwv
      rw [hY₁, hY₂]

/-- A concrete right-inverse matrix for a tail quadratic isometry. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoRightInverseMatrix
    (Y : e8SplitTailQuadraticIsometryModTwo) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j =>
    (Classical.choose
      (e8SplitTailQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2)))) i

/-- The chosen right-inverse matrix sends standard basis vectors to their chosen preimages. -/
theorem e8SplitTailQuadraticIsometryModTwoRightInverseMatrix_mulVec_single
    (Y : e8SplitTailQuadraticIsometryModTwo) (j : Fin 6) :
    (e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec (Pi.single j (1 : ZMod 2)) =
      Classical.choose
        (e8SplitTailQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2))) := by
  ext i
  simp [e8SplitTailQuadraticIsometryModTwoRightInverseMatrix, Matrix.mulVec, dotProduct,
    Pi.single_apply]

/-- The chosen matrix is a right inverse for the underlying matrix of a tail isometry. -/
theorem e8SplitTailQuadraticIsometryModTwo_mul_rightInverseMatrix
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    Y.1 * e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y = 1 := by
  ext i j
  have hcol : (Y.1 * e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec
      (Pi.single j (1 : ZMod 2)) = Pi.single j 1 := by
    rw [← Matrix.mulVec_mulVec]
    rw [e8SplitTailQuadraticIsometryModTwoRightInverseMatrix_mulVec_single]
    exact Classical.choose_spec
      (e8SplitTailQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2)))
  have hentry := congrFun hcol i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hentry

/-- Over the finite matrix monoid, the chosen tail right inverse is also a left inverse. -/
theorem e8SplitTailQuadraticIsometryModTwo_rightInverseMatrix_mul
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y * Y.1 = 1 := by
  rw [← mul_eq_one_comm]
  exact e8SplitTailQuadraticIsometryModTwo_mul_rightInverseMatrix Y

/-- The inverse of a tail quadratic isometry, packaged again as a tail quadratic isometry. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoInverse
    (Y : e8SplitTailQuadraticIsometryModTwo) : e8SplitTailQuadraticIsometryModTwo :=
  ⟨e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y, by
    intro v
    have hY := Y.2 ((e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v)
    have hmul :
        Y.1.mulVec ((e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, e8SplitTailQuadraticIsometryModTwo_mul_rightInverseMatrix]
      simp
    rw [hmul] at hY
    exact hY.symm⟩

/-- Applying a tail isometry and then its packaged inverse gives the original vector. -/
theorem e8SplitTailQuadraticIsometryModTwo_inverse_mulVec
    (Y : e8SplitTailQuadraticIsometryModTwo) (v : Fin 6 → ZMod 2) :
    (e8SplitTailQuadraticIsometryModTwoInverse Y).1.mulVec (Y.1.mulVec v) = v := by
  change (e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec (Y.1.mulVec v) = v
  rw [Matrix.mulVec_mulVec, e8SplitTailQuadraticIsometryModTwo_rightInverseMatrix_mul]
  simp

/-- Applying the packaged inverse and then the original tail isometry gives the original vector. -/
theorem e8SplitTailQuadraticIsometryModTwo_mulVec_inverse
    (Y : e8SplitTailQuadraticIsometryModTwo) (v : Fin 6 → ZMod 2) :
    Y.1.mulVec ((e8SplitTailQuadraticIsometryModTwoInverse Y).1.mulVec v) = v := by
  change Y.1.mulVec ((e8SplitTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v) = v
  rw [Matrix.mulVec_mulVec, e8SplitTailQuadraticIsometryModTwo_mul_rightInverseMatrix]
  simp

/-- Any tail first-vector fiber is equivalent to the fixed tail first-vector stabilizer. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoFirstVectorFiberEquivStabilizer
    (v : e8SplitTailNonzeroSingularVectors) :
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer ≃
      {Y : e8SplitTailQuadraticIsometryModTwo //
        e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y = v} := by
  let T : e8SplitTailQuadraticIsometryModTwo :=
    Classical.choose (e8SplitTailQuadraticIsometryModTwoFirstVectorMap_surjective v)
  have hT : e8SplitTailQuadraticIsometryModTwoFirstVectorMap T = v :=
    Classical.choose_spec (e8SplitTailQuadraticIsometryModTwoFirstVectorMap_surjective v)
  refine
    { toFun := fun H => ?_
      invFun := fun K => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨e8SplitTailQuadraticIsometryModTwoComp T H.1, ?_⟩
    apply Subtype.ext
    change ((T.1 * H.1.1).mulVec e8SplitTailFirstBasisVector) = v.1
    rw [← Matrix.mulVec_mulVec, H.2]
    have hTval := congrArg Subtype.val hT
    simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorMap] using hTval
  · refine ⟨e8SplitTailQuadraticIsometryModTwoComp
        (e8SplitTailQuadraticIsometryModTwoInverse T) K.1, ?_⟩
    change (((e8SplitTailQuadraticIsometryModTwoInverse T).1 * K.1.1).mulVec
        e8SplitTailFirstBasisVector) = e8SplitTailFirstBasisVector
    rw [← Matrix.mulVec_mulVec]
    have hKval := congrArg Subtype.val K.2
    have hKfirst : K.1.1.mulVec e8SplitTailFirstBasisVector = v.1 := by
      simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorMap] using hKval
    rw [hKfirst]
    have hTval := congrArg Subtype.val hT
    have hTfirst : T.1.mulVec e8SplitTailFirstBasisVector = v.1 := by
      simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorMap] using hTval
    rw [← hTfirst]
    exact e8SplitTailQuadraticIsometryModTwo_inverse_mulVec T e8SplitTailFirstBasisVector
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    change ((e8SplitTailQuadraticIsometryModTwoInverse T).1 * (T.1 * H.1.1)) = H.1.1
    rw [← Matrix.mul_assoc]
    change (e8SplitTailQuadraticIsometryModTwoRightInverseMatrix T * T.1) * H.1.1 = H.1.1
    rw [e8SplitTailQuadraticIsometryModTwo_rightInverseMatrix_mul, Matrix.one_mul]
  · intro K
    apply Subtype.ext
    apply Subtype.ext
    change (T.1 * ((e8SplitTailQuadraticIsometryModTwoInverse T).1 * K.1.1)) = K.1.1
    rw [← Matrix.mul_assoc]
    change (T.1 * e8SplitTailQuadraticIsometryModTwoRightInverseMatrix T) * K.1.1 = K.1.1
    rw [e8SplitTailQuadraticIsometryModTwo_mul_rightInverseMatrix, Matrix.one_mul]

/-- All tail first-vector fibers have the cardinality of the fixed tail first-vector stabilizer. -/
theorem e8SplitTailQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer_at
    (v : e8SplitTailNonzeroSingularVectors) :
    Nat.card {Y : e8SplitTailQuadraticIsometryModTwo //
      e8SplitTailQuadraticIsometryModTwoFirstVectorMap Y = v} =
        Nat.card e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer := by
  exact (Nat.card_congr
    (e8SplitTailQuadraticIsometryModTwoFirstVectorFiberEquivStabilizer v)).symm

/-- The tail isometry count is reduced to the fixed first-tail-vector stabilizer. -/
theorem e8SplitTailQuadraticIsometryModTwo_natCard_eq_35_mul_firstVectorStabilizer :
    Nat.card e8SplitTailQuadraticIsometryModTwo =
      35 * Nat.card e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer :=
  e8SplitTailQuadraticIsometryModTwo_natCard_eq_35_mul_of_firstVector_fiber_card
    (Nat.card e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer)
    (fun v => e8SplitTailQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer_at v)

/-- A tail quadratic isometry sends singular partners to singular partners. -/
theorem e8SplitTailQuadraticIsometryModTwo_mulVec_mem_singularPartners
    (Y : e8SplitTailQuadraticIsometryModTwo) (v : Fin 6 → ZMod 2) {w : Fin 6 → ZMod 2}
    (hw : w ∈ e8SplitTailSingularPartners v) :
    Y.1.mulVec w ∈ e8SplitTailSingularPartners (Y.1.mulVec v) := by
  simp [e8SplitTailSingularPartners, e8SplitTailSingularVectors] at hw ⊢
  exact ⟨by rw [Y.2 w, hw.1],
    by rw [e8SplitTailQuadraticIsometryModTwo_preserves_polar Y v w, hw.2]⟩

/-- Composition inside the fixed first-tail-vector stabilizer. -/
def e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerComp
    (Y Z : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer) :
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer :=
  ⟨e8SplitTailQuadraticIsometryModTwoComp Y.1 Z.1, by
    change ((Y.1.1 * Z.1.1).mulVec e8SplitTailFirstBasisVector) = e8SplitTailFirstBasisVector
    rw [← Matrix.mulVec_mulVec, Z.2, Y.2]⟩

/-- The packaged inverse of a first-tail-vector stabilizer again fixes the first tail basis vector. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerInverse
    (Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer) :
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer :=
  ⟨e8SplitTailQuadraticIsometryModTwoInverse Y.1, by
    have h := e8SplitTailQuadraticIsometryModTwo_inverse_mulVec Y.1 e8SplitTailFirstBasisVector
    rw [Y.2] at h
    exact h⟩

/-- Evaluation at the second tail basis vector maps the first-tail-vector stabilizer to the `16` fixed partners. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap :
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer →
      (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type) := fun Y =>
  ⟨Y.1.1.mulVec e8SplitTailSecondBasisVector, by
    have hmem :=
      e8SplitTailQuadraticIsometryModTwo_mulVec_mem_singularPartners Y.1
        e8SplitTailFirstBasisVector
        e8SplitTailSecondBasisVector_mem_singularPartners_firstBasisVector
    simpa [Y.2] using hmem⟩

/-- Uniform fibers of the second-tail-vector map give the fixed first-tail stabilizer count. -/
theorem
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer_natCard_eq_16_mul_of_secondVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ w : (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type),
      Nat.card {Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer = 16 * c := by
  rw [nat_card_eq_mul_of_fiber_card
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap c hfiber]
  rw [Nat.card_eq_finsetCard (e8SplitTailSingularPartners e8SplitTailFirstBasisVector),
    e8SplitTailSingularPartners_firstBasisVector_card]

/-- Combining the first-tail and second-tail recurrence interfaces reduces the tail count to one stabilizer fiber. -/
theorem e8SplitTailQuadraticIsometryModTwo_natCard_eq_560_mul_of_secondVector_fiber_card
    (c : ℕ)
    (hsecond : ∀ w : (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type),
      Nat.card {Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitTailQuadraticIsometryModTwo = 560 * c := by
  rw [e8SplitTailQuadraticIsometryModTwo_natCard_eq_35_mul_firstVectorStabilizer]
  rw [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer_natCard_eq_16_mul_of_secondVector_fiber_card
    c hsecond]
  ring

/-- If the vector defining a tail split symmetry is polar-orthogonal to `u`, then the symmetry fixes `u`. -/
theorem e8SplitTailSymmetry_mulVec_of_polar_zero
    (a u : Fin 6 → ZMod 2) (ha : e8SplitTailQuadraticPolynomial a = 1)
    (hpolar : e8SplitTailPolarBilinear u a = 0) :
    (e8SplitTailSymmetry a ha).1.mulVec u = u := by
  change (e8SplitTailSymmetryMatrix a).mulVec u = u
  rw [e8SplitTailSymmetryMatrix_mulVec]
  rw [hpolar]
  simp

/-- In the first-tail partner set, orthogonal non-fixed partners have a common partner. -/
theorem e8SplitTailSecondBasisPartnerCommonPartner_exists
    (w : (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type))
    (horth : e8SplitTailPolarBilinear e8SplitTailSecondBasisVector w.1 = 0)
    (hne : w.1 ≠ e8SplitTailSecondBasisVector) :
    ∃ z : Fin 6 → ZMod 2,
      e8SplitTailQuadraticPolynomial z = 0 ∧
        e8SplitTailPolarBilinear e8SplitTailFirstBasisVector z = 1 ∧
          e8SplitTailPolarBilinear e8SplitTailSecondBasisVector z = 1 ∧
            e8SplitTailPolarBilinear w.1 z = 1 := by
  decide +revert

/-- The first-tail-vector stabilizer can send the fixed second tail basis vector to any partner pairing to `1` with it. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_exists_of_pair_one
    (w : (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type))
    (hpair : e8SplitTailPolarBilinear e8SplitTailSecondBasisVector w.1 = 1) :
    ∃ Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer,
      e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w := by
  have hsecondQ : e8SplitTailQuadraticPolynomial e8SplitTailSecondBasisVector = 0 := by decide
  have hwQ : e8SplitTailQuadraticPolynomial w.1 = 0 := by
    have hwmem : w.1 ∈ e8SplitTailSingularPartners e8SplitTailFirstBasisVector := w.2
    have hsing : w.1 ∈ e8SplitTailSingularVectors := (Finset.mem_filter.mp hwmem).1
    exact (Finset.mem_filter.mp hsing).2
  have hfirstw : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector w.1 = 1 := by
    have hwmem : w.1 ∈ e8SplitTailSingularPartners e8SplitTailFirstBasisVector := w.2
    exact (Finset.mem_filter.mp hwmem).2
  let Y : e8SplitTailQuadraticIsometryModTwo :=
    e8SplitTailSymmetry (e8SplitTailSecondBasisVector + w.1)
      (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hwQ hpair)
  have hfix : Y.1.mulVec e8SplitTailFirstBasisVector = e8SplitTailFirstBasisVector := by
    have horth : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector
        (e8SplitTailSecondBasisVector + w.1) = 0 := by
      simp [e8SplitTailPolarBilinear, e8SplitTailFirstBasisVector, e8SplitTailSecondBasisVector,
        Pi.add_apply] at hfirstw ⊢
      rw [hfirstw]
      decide
    exact e8SplitTailSymmetry_mulVec_of_polar_zero (e8SplitTailSecondBasisVector + w.1)
      e8SplitTailFirstBasisVector
      (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hwQ hpair) horth
  refine ⟨⟨Y, hfix⟩, ?_⟩
  apply Subtype.ext
  exact e8SplitTailSymmetry_mulVec_of_singular_pair hsecondQ hwQ hpair

/-- The second-tail-vector map from the fixed first-tail-vector stabilizer onto the `16` fixed partners is surjective. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective :
    Function.Surjective
      e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap := by
  intro w
  by_cases hwsecond : w.1 = e8SplitTailSecondBasisVector
  · refine ⟨⟨e8SplitTailQuadraticIsometryModTwoIdentity, ?_⟩, ?_⟩
    · simp [e8SplitTailQuadraticIsometryModTwoIdentity]
    · apply Subtype.ext
      simp [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap,
        e8SplitTailQuadraticIsometryModTwoIdentity, hwsecond]
  · by_cases hpair : e8SplitTailPolarBilinear e8SplitTailSecondBasisVector w.1 = 1
    · exact
        e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_exists_of_pair_one
          w hpair
    · have horth : e8SplitTailPolarBilinear e8SplitTailSecondBasisVector w.1 = 0 := by
        decide +revert
      rcases e8SplitTailSecondBasisPartnerCommonPartner_exists w horth hwsecond with
        ⟨z, hzQ, hfirstz, hsecondz, hwz⟩
      have hsecondQ : e8SplitTailQuadraticPolynomial e8SplitTailSecondBasisVector = 0 := by decide
      have hwQ : e8SplitTailQuadraticPolynomial w.1 = 0 := by
        have hwmem : w.1 ∈ e8SplitTailSingularPartners e8SplitTailFirstBasisVector := w.2
        have hsing : w.1 ∈ e8SplitTailSingularVectors := (Finset.mem_filter.mp hwmem).1
        exact (Finset.mem_filter.mp hsing).2
      have hzw : e8SplitTailPolarBilinear z w.1 = 1 := by
        rw [e8SplitTailPolarBilinear_comm]
        exact hwz
      let Y₁ : e8SplitTailQuadraticIsometryModTwo :=
        e8SplitTailSymmetry (e8SplitTailSecondBasisVector + z)
          (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hzQ hsecondz)
      let Y₂ : e8SplitTailQuadraticIsometryModTwo :=
        e8SplitTailSymmetry (z + w.1)
          (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hzQ hwQ hzw)
      have hY₁fix : Y₁.1.mulVec e8SplitTailFirstBasisVector = e8SplitTailFirstBasisVector := by
        have horth₁ : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector
            (e8SplitTailSecondBasisVector + z) = 0 := by
          simp [e8SplitTailPolarBilinear, e8SplitTailFirstBasisVector, e8SplitTailSecondBasisVector,
            Pi.add_apply] at hfirstz ⊢
          rw [hfirstz]
          decide
        exact e8SplitTailSymmetry_mulVec_of_polar_zero (e8SplitTailSecondBasisVector + z)
          e8SplitTailFirstBasisVector
          (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hsecondQ hzQ hsecondz)
          horth₁
      have hY₂fix : Y₂.1.mulVec e8SplitTailFirstBasisVector = e8SplitTailFirstBasisVector := by
        have hfirstw : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector w.1 = 1 := by
          have hwmem : w.1 ∈ e8SplitTailSingularPartners e8SplitTailFirstBasisVector := w.2
          exact (Finset.mem_filter.mp hwmem).2
        have horth₂ : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector (z + w.1) = 0 := by
          simp [e8SplitTailPolarBilinear, e8SplitTailFirstBasisVector, Pi.add_apply] at hfirstz hfirstw ⊢
          rw [hfirstz, hfirstw]
          decide
        exact e8SplitTailSymmetry_mulVec_of_polar_zero (z + w.1) e8SplitTailFirstBasisVector
          (e8SplitTailQuadraticPolynomial_add_eq_one_of_singular_pair hzQ hwQ hzw) horth₂
      refine ⟨⟨e8SplitTailQuadraticIsometryModTwoComp Y₂ Y₁, ?_⟩, ?_⟩
      · change ((Y₂.1 * Y₁.1).mulVec e8SplitTailFirstBasisVector) = e8SplitTailFirstBasisVector
        rw [← Matrix.mulVec_mulVec, hY₁fix, hY₂fix]
      · apply Subtype.ext
        change ((Y₂.1 * Y₁.1).mulVec e8SplitTailSecondBasisVector) = w.1
        rw [← Matrix.mulVec_mulVec]
        have hY₁ : Y₁.1.mulVec e8SplitTailSecondBasisVector = z := by
          exact e8SplitTailSymmetry_mulVec_of_singular_pair hsecondQ hzQ hsecondz
        have hY₂ : Y₂.1.mulVec z = w.1 := by
          exact e8SplitTailSymmetry_mulVec_of_singular_pair hzQ hwQ hzw
        rw [hY₁, hY₂]

/-- The stabilizer of the fixed tail hyperbolic pair `(e₀,e₁)`. -/
abbrev e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer : Type :=
  {Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer //
    e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y =
      ⟨e8SplitTailSecondBasisVector, e8SplitTailSecondBasisVector_mem_singularPartners_firstBasisVector⟩}

noncomputable instance :
    Fintype e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  unfold e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer
  infer_instance

/-- Any second-tail-vector fiber is equivalent to the fixed tail hyperbolic-pair stabilizer. -/
noncomputable def e8SplitTailQuadraticIsometryModTwoSecondVectorFiberEquivFirstSecondStabilizer
    (w : (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type)) :
    e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer ≃
      {Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} := by
  let T : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer :=
    Classical.choose
      (e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective w)
  have hT : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap T = w :=
    Classical.choose_spec
      (e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective w)
  refine
    { toFun := fun H => ?_
      invFun := fun K => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerComp T H.1, ?_⟩
    apply Subtype.ext
    change ((T.1.1 * H.1.1.1).mulVec e8SplitTailSecondBasisVector) = w.1
    rw [← Matrix.mulVec_mulVec]
    have hHsecond := congrArg Subtype.val H.2
    have hHsecond' : H.1.1.1.mulVec e8SplitTailSecondBasisVector = e8SplitTailSecondBasisVector := by
      simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap]
        using hHsecond
    rw [hHsecond']
    have hTval := congrArg Subtype.val hT
    simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hTval
  · refine ⟨e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerComp
        (e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerInverse T) K.1, ?_⟩
    apply Subtype.ext
    change (((e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerInverse T).1.1 * K.1.1.1).mulVec
        e8SplitTailSecondBasisVector) = e8SplitTailSecondBasisVector
    rw [← Matrix.mulVec_mulVec]
    have hKval := congrArg Subtype.val K.2
    have hKsecond : K.1.1.1.mulVec e8SplitTailSecondBasisVector = w.1 := by
      simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hKval
    rw [hKsecond]
    have hTval := congrArg Subtype.val hT
    have hTsecond : T.1.1.mulVec e8SplitTailSecondBasisVector = w.1 := by
      simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hTval
    rw [← hTsecond]
    exact e8SplitTailQuadraticIsometryModTwo_inverse_mulVec T.1 e8SplitTailSecondBasisVector
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change ((e8SplitTailQuadraticIsometryModTwoInverse T.1).1 * (T.1.1 * H.1.1.1)) = H.1.1.1
    rw [← Matrix.mul_assoc]
    change (e8SplitTailQuadraticIsometryModTwoRightInverseMatrix T.1 * T.1.1) * H.1.1.1 = H.1.1.1
    rw [e8SplitTailQuadraticIsometryModTwo_rightInverseMatrix_mul, Matrix.one_mul]
  · intro K
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (T.1.1 * ((e8SplitTailQuadraticIsometryModTwoInverse T.1).1 * K.1.1.1)) = K.1.1.1
    rw [← Matrix.mul_assoc]
    change (T.1.1 * e8SplitTailQuadraticIsometryModTwoRightInverseMatrix T.1) * K.1.1.1 = K.1.1.1
    rw [e8SplitTailQuadraticIsometryModTwo_mul_rightInverseMatrix, Matrix.one_mul]

/-- All second-tail-vector fibers have the cardinality of the fixed tail hyperbolic-pair stabilizer. -/
theorem e8SplitTailQuadraticIsometryModTwo_secondVectorFiber_natCard_eq_firstSecondStabilizer_at
    (w : (e8SplitTailSingularPartners e8SplitTailFirstBasisVector : Type)) :
    Nat.card {Y : e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizer //
      e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} =
        Nat.card e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  exact (Nat.card_congr
    (e8SplitTailQuadraticIsometryModTwoSecondVectorFiberEquivFirstSecondStabilizer w)).symm

/-- The tail isometry count is reduced to the fixed tail hyperbolic-pair stabilizer. -/
theorem e8SplitTailQuadraticIsometryModTwo_natCard_eq_560_mul_firstSecondStabilizer :
    Nat.card e8SplitTailQuadraticIsometryModTwo =
      560 * Nat.card e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer :=
  e8SplitTailQuadraticIsometryModTwo_natCard_eq_560_mul_of_secondVector_fiber_card
    (Nat.card e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    (fun w => e8SplitTailQuadraticIsometryModTwo_secondVectorFiber_natCard_eq_firstSecondStabilizer_at w)

/-- The four-dimensional complement of the fixed tail hyperbolic plane. -/
def e8SplitTailTailIndex : Fin 4 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5

/-- The split quadratic polynomial on the four-dimensional tail complement. -/
def e8SplitTailTailQuadraticPolynomial (x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 3

/-- Embed the four-dimensional tail complement in the six-dimensional tail. -/
def e8SplitTailTailVector (x : Fin 4 → ZMod 2) : Fin 6 → ZMod 2
  | 0 => 0
  | 1 => 0
  | 2 => x 0
  | 3 => x 1
  | 4 => x 2
  | 5 => x 3

/-- Project a six-dimensional tail vector to the four-dimensional complement. -/
def e8SplitTailTailCoordinates (v : Fin 6 → ZMod 2) : Fin 4 → ZMod 2 :=
  fun i => v (e8SplitTailTailIndex i)

/-- Four-dimensional coordinates recover an embedded complement vector. -/
theorem e8SplitTailTailCoordinates_tailTailVector (x : Fin 4 → ZMod 2) :
    e8SplitTailTailCoordinates (e8SplitTailTailVector x) = x := by
  funext i
  fin_cases i <;> rfl

/-- If a six-dimensional tail vector has zero first hyperbolic coordinates, it is
recovered from its four-dimensional complement coordinates. -/
theorem e8SplitTailTailVector_tailTailCoordinates_of_zero
    {v : Fin 6 → ZMod 2} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    e8SplitTailTailVector (e8SplitTailTailCoordinates v) = v := by
  funext i
  fin_cases i <;> simp [e8SplitTailTailVector, e8SplitTailTailCoordinates,
    e8SplitTailTailIndex, h0, h1]

/-- The six-dimensional tail quadratic polynomial restricts to the
four-dimensional split polynomial on the complement. -/
theorem e8SplitTailQuadraticPolynomial_tailTailVector (x : Fin 4 → ZMod 2) :
    e8SplitTailQuadraticPolynomial (e8SplitTailTailVector x) =
      e8SplitTailTailQuadraticPolynomial x := by
  simp [e8SplitTailQuadraticPolynomial, e8SplitTailTailQuadraticPolynomial,
    e8SplitTailTailVector]

/-- A matrix over `𝔽₂` preserving the four-dimensional split quadratic
polynomial. -/
abbrev e8SplitTailTailQuadraticIsometryModTwo : Type :=
  {Y : Matrix (Fin 4) (Fin 4) (ZMod 2) //
    ∀ v : Fin 4 → ZMod 2,
      e8SplitTailTailQuadraticPolynomial (Y.mulVec v) =
        e8SplitTailTailQuadraticPolynomial v}

noncomputable instance : Fintype e8SplitTailTailQuadraticIsometryModTwo := by
  unfold e8SplitTailTailQuadraticIsometryModTwo
  infer_instance

/-- The polar form attached to the four-dimensional split polynomial. -/
noncomputable def e8SplitTailTailPolarBilinear (v w : Fin 4 → ZMod 2) : ZMod 2 :=
  v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2

/-- The four-dimensional singular cone over `𝔽₂`. -/
noncomputable def e8SplitTailTailSingularVectors : Finset (Fin 4 → ZMod 2) := by
  classical
  exact Finset.univ.filter fun v => e8SplitTailTailQuadraticPolynomial v = 0

/-- The nonzero singular vectors in the four-dimensional complement. -/
noncomputable def e8SplitTailTailNonzeroSingularVectors : Finset (Fin 4 → ZMod 2) := by
  classical
  exact e8SplitTailTailSingularVectors.filter fun v => v ≠ 0

/-- Singular partners of a four-dimensional vector. -/
noncomputable def e8SplitTailTailSingularPartners (v : Fin 4 → ZMod 2) :
    Finset (Fin 4 → ZMod 2) := by
  classical
  exact e8SplitTailTailSingularVectors.filter fun w =>
    e8SplitTailTailPolarBilinear v w = 1

/-- The four-dimensional complement has `10` singular vectors over `𝔽₂`. -/
theorem e8SplitTailTailSingularVectors_card :
    e8SplitTailTailSingularVectors.card = 10 := by
  decide

/-- The four-dimensional complement has `9` nonzero singular vectors over `𝔽₂`. -/
theorem e8SplitTailTailNonzeroSingularVectors_card :
    e8SplitTailTailNonzeroSingularVectors.card = 9 := by
  decide

/-- A fixed nonzero singular vector in the first complement hyperbolic plane. -/
def e8SplitTailTailFirstBasisVector : Fin 4 → ZMod 2 :=
  fun i => if i = 0 then 1 else 0

/-- The fixed first complement basis vector is nonzero singular. -/
theorem e8SplitTailTailFirstBasisVector_mem_nonzeroSingular :
    e8SplitTailTailFirstBasisVector ∈ e8SplitTailTailNonzeroSingularVectors := by
  decide

/-- The second basis vector in the first complement hyperbolic plane. -/
def e8SplitTailTailSecondBasisVector : Fin 4 → ZMod 2 :=
  fun i => if i = 1 then 1 else 0

/-- The second complement basis vector is a singular partner of the first one. -/
theorem e8SplitTailTailSecondBasisVector_mem_singularPartners_firstBasisVector :
    e8SplitTailTailSecondBasisVector ∈
      e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector := by
  decide

/-- The fixed first complement basis vector has exactly `4` singular partners. -/
theorem e8SplitTailTailSingularPartners_firstBasisVector_card :
    (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector).card = 4 := by
  decide

/-- The four-dimensional polar form is the polarization of the complement split
quadratic polynomial. -/
theorem e8SplitTailTailPolarBilinear_eq_quadratic_add (v w : Fin 4 → ZMod 2) :
    e8SplitTailTailPolarBilinear v w =
      e8SplitTailTailQuadraticPolynomial (v + w) +
        e8SplitTailTailQuadraticPolynomial v + e8SplitTailTailQuadraticPolynomial w := by
  simp only [e8SplitTailTailPolarBilinear, e8SplitTailTailQuadraticPolynomial, Pi.add_apply]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [h2]

/-- Four-dimensional quadratic isometries preserve the associated polar form. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_preserves_polar
    (Y : e8SplitTailTailQuadraticIsometryModTwo) (v w : Fin 4 → ZMod 2) :
    e8SplitTailTailPolarBilinear (Y.1.mulVec v) (Y.1.mulVec w) =
      e8SplitTailTailPolarBilinear v w := by
  rw [e8SplitTailTailPolarBilinear_eq_quadratic_add,
    e8SplitTailTailPolarBilinear_eq_quadratic_add]
  rw [← Matrix.mulVec_add]
  rw [Y.2 (v + w), Y.2 v, Y.2 w]

/-- The four-dimensional polar form has zero left kernel. -/
theorem e8SplitTailTailPolarBilinear_left_kernel_eq_zero
    (v : Fin 4 → ZMod 2)
    (h : ∀ w : Fin 4 → ZMod 2, e8SplitTailTailPolarBilinear v w = 0) :
    v = 0 := by
  funext i
  fin_cases i <;>
    first
    | simpa [e8SplitTailTailPolarBilinear] using h (Pi.single (1 : Fin 4) (1 : ZMod 2))
    | simpa [e8SplitTailTailPolarBilinear] using h (Pi.single (0 : Fin 4) (1 : ZMod 2))
    | simpa [e8SplitTailTailPolarBilinear] using h (Pi.single (3 : Fin 4) (1 : ZMod 2))
    | simpa [e8SplitTailTailPolarBilinear] using h (Pi.single (2 : Fin 4) (1 : ZMod 2))

/-- A four-dimensional quadratic isometry has trivial kernel. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_mulVec_eq_zero_iff
    (Y : e8SplitTailTailQuadraticIsometryModTwo) (v : Fin 4 → ZMod 2) :
    Y.1.mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    apply e8SplitTailTailPolarBilinear_left_kernel_eq_zero v
    intro w
    rw [← e8SplitTailTailQuadraticIsometryModTwo_preserves_polar Y v w, hv]
    simp [e8SplitTailTailPolarBilinear]
  · intro hv
    rw [hv, Matrix.mulVec_zero]

/-- A four-dimensional quadratic isometry is injective on vectors. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_mulVec_injective
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    Function.Injective Y.1.mulVec := by
  intro v w h
  have hker : Y.1.mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hz := (e8SplitTailTailQuadraticIsometryModTwo_mulVec_eq_zero_iff Y (v - w)).mp hker
  exact sub_eq_zero.mp hz

/-- A four-dimensional quadratic isometry is surjective on vectors. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_mulVec_surjective
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    Function.Surjective Y.1.mulVec := by
  exact Finite.surjective_of_injective (e8SplitTailTailQuadraticIsometryModTwo_mulVec_injective Y)

/-- A four-dimensional quadratic isometry sends nonzero singular vectors to
nonzero singular vectors. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_mulVec_mem_nonzeroSingular
    (Y : e8SplitTailTailQuadraticIsometryModTwo) {v : Fin 4 → ZMod 2}
    (hv : v ∈ e8SplitTailTailNonzeroSingularVectors) :
    Y.1.mulVec v ∈ e8SplitTailTailNonzeroSingularVectors := by
  simp [e8SplitTailTailNonzeroSingularVectors, e8SplitTailTailSingularVectors] at hv ⊢
  exact ⟨by rw [Y.2 v, hv.1], fun hzero => hv.2
    ((e8SplitTailTailQuadraticIsometryModTwo_mulVec_eq_zero_iff Y v).mp hzero)⟩

/-- The identity matrix is a four-dimensional quadratic isometry. -/
def e8SplitTailTailQuadraticIsometryModTwoIdentity : e8SplitTailTailQuadraticIsometryModTwo :=
  ⟨1, by intro v; simp⟩

/-- Four-dimensional quadratic isometries are closed under matrix composition. -/
def e8SplitTailTailQuadraticIsometryModTwoComp
    (Y Z : e8SplitTailTailQuadraticIsometryModTwo) :
    e8SplitTailTailQuadraticIsometryModTwo :=
  ⟨Y.1 * Z.1, by
    intro v
    rw [← Matrix.mulVec_mulVec v Y.1 Z.1]
    rw [Y.2 (Z.1.mulVec v), Z.2 v]⟩

/-- Evaluation at the fixed first complement basis vector, as a map into nonzero
singular vectors. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap :
    e8SplitTailTailQuadraticIsometryModTwo →
      e8SplitTailTailNonzeroSingularVectors := fun Y =>
  ⟨Y.1.mulVec e8SplitTailTailFirstBasisVector,
    e8SplitTailTailQuadraticIsometryModTwo_mulVec_mem_nonzeroSingular Y
      e8SplitTailTailFirstBasisVector_mem_nonzeroSingular⟩

/-- Uniform fibers of the four-dimensional first-vector map give the group count. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_nonzeroSingular_mul_of_firstVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ v : e8SplitTailTailNonzeroSingularVectors,
      Nat.card {Y : e8SplitTailTailQuadraticIsometryModTwo //
        e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap Y = v} = c) :
    Nat.card e8SplitTailTailQuadraticIsometryModTwo =
      Nat.card e8SplitTailTailNonzeroSingularVectors * c := by
  exact nat_card_eq_mul_of_fiber_card e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap c hfiber

/-- With the known `9` nonzero singular vectors, uniform first-vector fibers give
a compact count. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_9_mul_of_firstVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ v : e8SplitTailTailNonzeroSingularVectors,
      Nat.card {Y : e8SplitTailTailQuadraticIsometryModTwo //
        e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap Y = v} = c) :
    Nat.card e8SplitTailTailQuadraticIsometryModTwo = 9 * c := by
  rw [e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_nonzeroSingular_mul_of_firstVector_fiber_card
    c hfiber]
  rw [Nat.card_eq_finsetCard e8SplitTailTailNonzeroSingularVectors,
    e8SplitTailTailNonzeroSingularVectors_card]

/-- The stabilizer of the fixed first complement basis vector. -/
abbrev e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer : Type :=
  {Y : e8SplitTailTailQuadraticIsometryModTwo //
    Y.1.mulVec e8SplitTailTailFirstBasisVector = e8SplitTailTailFirstBasisVector}

noncomputable instance :
    Fintype e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer := by
  unfold e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer
  infer_instance

/-- The fixed four-dimensional first-vector fiber is the first-vector stabilizer. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwo_firstVectorFiberEquivStabilizer :
    {Y : e8SplitTailTailQuadraticIsometryModTwo //
      e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap Y =
        ⟨e8SplitTailTailFirstBasisVector,
          e8SplitTailTailFirstBasisVector_mem_nonzeroSingular⟩} ≃
      e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer where
  toFun Y := by
    refine ⟨Y.1, ?_⟩
    have h := congrArg Subtype.val Y.2
    simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap] using h
  invFun Y := by
    refine ⟨Y.1, ?_⟩
    apply Subtype.ext
    exact Y.2
  left_inv Y := by
    apply Subtype.ext
    rfl
  right_inv Y := by
    apply Subtype.ext
    rfl

/-- The four-dimensional polar form is symmetric. -/
theorem e8SplitTailTailPolarBilinear_comm (v w : Fin 4 → ZMod 2) :
    e8SplitTailTailPolarBilinear v w = e8SplitTailTailPolarBilinear w v := by
  simp only [e8SplitTailTailPolarBilinear]
  ring_nf

/-- The coordinate vector dual to `a` for the four-dimensional split polar form. -/
def e8SplitTailTailPolarDualVector (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2
  | 0 => a 1
  | 1 => a 0
  | 2 => a 3
  | 3 => a 2

/-- The characteristic-two orthogonal symmetry attached to a four-dimensional
vector. -/
def e8SplitTailTailSymmetryMatrix (a : Fin 4 → ZMod 2) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j +
    a i * e8SplitTailTailPolarDualVector a j

/-- The matrix formula for the characteristic-two four-dimensional symmetry. -/
theorem e8SplitTailTailSymmetryMatrix_mulVec
    (a x : Fin 4 → ZMod 2) :
    (e8SplitTailTailSymmetryMatrix a).mulVec x =
      fun i => x i + e8SplitTailTailPolarBilinear x a * a i := by
  ext i
  fin_cases i <;>
    simp [e8SplitTailTailSymmetryMatrix, e8SplitTailTailPolarDualVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four, e8SplitTailTailPolarBilinear, Matrix.one_apply]
  <;> ring_nf

/-- Quadratic expansion for the four-dimensional split polynomial along a scalar
multiple of a vector. -/
theorem e8SplitTailTailQuadraticPolynomial_add_smul
    (x a : Fin 4 → ZMod 2) (c : ZMod 2) :
    e8SplitTailTailQuadraticPolynomial (fun i => x i + c * a i) =
      e8SplitTailTailQuadraticPolynomial x + c^2 * e8SplitTailTailQuadraticPolynomial a +
        c * e8SplitTailTailPolarBilinear x a := by
  simp only [e8SplitTailTailQuadraticPolynomial, e8SplitTailTailPolarBilinear]
  ring_nf

/-- If `Q(a)=1`, the characteristic-two four-dimensional symmetry preserves the
split polynomial. -/
theorem e8SplitTailTailQuadraticPolynomial_symmetry_apply
    (a x : Fin 4 → ZMod 2) (ha : e8SplitTailTailQuadraticPolynomial a = 1) :
    e8SplitTailTailQuadraticPolynomial
        (fun i => x i + e8SplitTailTailPolarBilinear x a * a i) =
      e8SplitTailTailQuadraticPolynomial x := by
  rw [e8SplitTailTailQuadraticPolynomial_add_smul]
  rw [ha]
  rw [mul_one]
  let b : ZMod 2 := e8SplitTailTailPolarBilinear x a
  change e8SplitTailTailQuadraticPolynomial x + b ^ 2 + b * b =
    e8SplitTailTailQuadraticPolynomial x
  have hsquare (z : ZMod 2) : z ^ 2 = z := by
    fin_cases z <;> decide
  have hbsq : b ^ 2 = b := hsquare b
  have hbmul : b * b = b := by
    simpa [pow_two] using hsquare b
  rw [hbsq, hbmul]
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  calc
    e8SplitTailTailQuadraticPolynomial x + b + b =
        e8SplitTailTailQuadraticPolynomial x + (b + b) := by rw [add_assoc]
    _ = e8SplitTailTailQuadraticPolynomial x := by rw [hdouble, add_zero]

/-- The characteristic-two four-dimensional symmetry as a quadratic isometry. -/
def e8SplitTailTailSymmetry
    (a : Fin 4 → ZMod 2) (ha : e8SplitTailTailQuadraticPolynomial a = 1) :
    e8SplitTailTailQuadraticIsometryModTwo :=
  ⟨e8SplitTailTailSymmetryMatrix a, by
    intro x
    rw [e8SplitTailTailSymmetryMatrix_mulVec]
    exact e8SplitTailTailQuadraticPolynomial_symmetry_apply a x ha⟩

/-- If two four-dimensional singular vectors pair to `1`, their sum has norm `1`. -/
theorem e8SplitTailTailQuadraticPolynomial_add_eq_one_of_singular_pair
    {u v : Fin 4 → ZMod 2}
    (hu : e8SplitTailTailQuadraticPolynomial u = 0)
    (hv : e8SplitTailTailQuadraticPolynomial v = 0)
    (hpair : e8SplitTailTailPolarBilinear u v = 1) :
    e8SplitTailTailQuadraticPolynomial (u + v) = 1 := by
  have hpol := e8SplitTailTailPolarBilinear_eq_quadratic_add u v
  rw [hpol, hu, hv] at hpair
  simpa using hpair

/-- If two four-dimensional singular vectors pair to `1`, the attached symmetry
sends the first vector to the second. -/
theorem e8SplitTailTailSymmetry_mulVec_of_singular_pair
    {u v : Fin 4 → ZMod 2}
    (hu : e8SplitTailTailQuadraticPolynomial u = 0)
    (hv : e8SplitTailTailQuadraticPolynomial v = 0)
    (hpair : e8SplitTailTailPolarBilinear u v = 1) :
    (e8SplitTailTailSymmetry (u + v)
      (e8SplitTailTailQuadraticPolynomial_add_eq_one_of_singular_pair hu hv hpair)).1.mulVec u = v := by
  change (e8SplitTailTailSymmetryMatrix (u + v)).mulVec u = v
  rw [e8SplitTailTailSymmetryMatrix_mulVec]
  have hpolar : e8SplitTailTailPolarBilinear u (u + v) = 1 := by
    simp [e8SplitTailTailPolarBilinear, Pi.add_apply] at hpair ⊢
    ring_nf at hpair ⊢
    have h2 : (2 : ZMod 2) = 0 := by decide
    simpa [h2] using hpair
  funext i
  rw [hpolar]
  simp only [one_mul, Pi.add_apply]
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [← add_assoc, hdouble, zero_add]

/-- The first-vector orbit contains every four-dimensional nonzero singular
vector pairing to `1` with the fixed first basis vector. -/
theorem e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap_exists_of_pair_one
    (v : e8SplitTailTailNonzeroSingularVectors)
    (hpair : e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector v.1 = 1) :
    ∃ Y : e8SplitTailTailQuadraticIsometryModTwo,
      e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap Y = v := by
  have hfirstQ : e8SplitTailTailQuadraticPolynomial e8SplitTailTailFirstBasisVector = 0 := by
    have hmem : e8SplitTailTailFirstBasisVector ∈ e8SplitTailTailNonzeroSingularVectors :=
      e8SplitTailTailFirstBasisVector_mem_nonzeroSingular
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hvQ : e8SplitTailTailQuadraticPolynomial v.1 = 0 := by
    have hmem : v.1 ∈ e8SplitTailTailNonzeroSingularVectors := v.2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  let Y : e8SplitTailTailQuadraticIsometryModTwo :=
    e8SplitTailTailSymmetry (e8SplitTailTailFirstBasisVector + v.1)
      (e8SplitTailTailQuadraticPolynomial_add_eq_one_of_singular_pair hfirstQ hvQ hpair)
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  exact e8SplitTailTailSymmetry_mulVec_of_singular_pair hfirstQ hvQ hpair

/-- Orthogonal nonzero four-dimensional singular vectors have a singular common
partner. -/
theorem e8SplitTailTailFirstBasisCommonSingularPartner_exists
    (v : e8SplitTailTailNonzeroSingularVectors)
    (horth : e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector v.1 = 0)
    (hne : v.1 ≠ e8SplitTailTailFirstBasisVector) :
    ∃ w : Fin 4 → ZMod 2,
      e8SplitTailTailQuadraticPolynomial w = 0 ∧
        e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector w = 1 ∧
          e8SplitTailTailPolarBilinear v.1 w = 1 := by
  decide +revert

/-- The first-vector map is surjective onto the `9` nonzero singular vectors. -/
theorem e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap_surjective :
    Function.Surjective e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap := by
  intro v
  have hfirstQ : e8SplitTailTailQuadraticPolynomial e8SplitTailTailFirstBasisVector = 0 := by
    have hmem : e8SplitTailTailFirstBasisVector ∈ e8SplitTailTailNonzeroSingularVectors :=
      e8SplitTailTailFirstBasisVector_mem_nonzeroSingular
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hvQ : e8SplitTailTailQuadraticPolynomial v.1 = 0 := by
    have hmem : v.1 ∈ e8SplitTailTailNonzeroSingularVectors := v.2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  by_cases hvfirst : v.1 = e8SplitTailTailFirstBasisVector
  · refine ⟨e8SplitTailTailQuadraticIsometryModTwoIdentity, ?_⟩
    apply Subtype.ext
    simp [e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap,
      e8SplitTailTailQuadraticIsometryModTwoIdentity, hvfirst]
  · by_cases hpair : e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector v.1 = 1
    · exact e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap_exists_of_pair_one v hpair
    · have horth : e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector v.1 = 0 := by
        decide +revert
      rcases e8SplitTailTailFirstBasisCommonSingularPartner_exists v horth hvfirst with
        ⟨w, hwQ, hfirstw, hvw⟩
      have hwv : e8SplitTailTailPolarBilinear w v.1 = 1 := by
        rw [e8SplitTailTailPolarBilinear_comm]
        exact hvw
      let Y₁ : e8SplitTailTailQuadraticIsometryModTwo :=
        e8SplitTailTailSymmetry (e8SplitTailTailFirstBasisVector + w)
          (e8SplitTailTailQuadraticPolynomial_add_eq_one_of_singular_pair hfirstQ hwQ hfirstw)
      let Y₂ : e8SplitTailTailQuadraticIsometryModTwo :=
        e8SplitTailTailSymmetry (w + v.1)
          (e8SplitTailTailQuadraticPolynomial_add_eq_one_of_singular_pair hwQ hvQ hwv)
      refine ⟨e8SplitTailTailQuadraticIsometryModTwoComp Y₂ Y₁, ?_⟩
      apply Subtype.ext
      change ((Y₂.1 * Y₁.1).mulVec e8SplitTailTailFirstBasisVector) = v.1
      rw [← Matrix.mulVec_mulVec e8SplitTailTailFirstBasisVector Y₂.1 Y₁.1]
      have hY₁ : Y₁.1.mulVec e8SplitTailTailFirstBasisVector = w := by
        exact e8SplitTailTailSymmetry_mulVec_of_singular_pair hfirstQ hwQ hfirstw
      have hY₂ : Y₂.1.mulVec w = v.1 := by
        exact e8SplitTailTailSymmetry_mulVec_of_singular_pair hwQ hvQ hwv
      rw [hY₁, hY₂]

/-- A concrete right-inverse matrix for a four-dimensional quadratic isometry. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix
    (Y : e8SplitTailTailQuadraticIsometryModTwo) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j =>
    (Classical.choose
      (e8SplitTailTailQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2)))) i

/-- The chosen right-inverse matrix sends standard basis vectors to their chosen
preimages. -/
theorem e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix_mulVec_single
    (Y : e8SplitTailTailQuadraticIsometryModTwo) (j : Fin 4) :
    (e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec (Pi.single j (1 : ZMod 2)) =
      Classical.choose
        (e8SplitTailTailQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2))) := by
  ext i
  simp [e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix, Matrix.mulVec, dotProduct,
    Pi.single_apply]

/-- The chosen matrix is a right inverse for the underlying matrix. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_mul_rightInverseMatrix
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    Y.1 * e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y = 1 := by
  ext i j
  have hcol : (Y.1 * e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec
      (Pi.single j (1 : ZMod 2)) = Pi.single j 1 := by
    rw [← Matrix.mulVec_mulVec]
    rw [e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix_mulVec_single]
    exact Classical.choose_spec
      (e8SplitTailTailQuadraticIsometryModTwo_mulVec_surjective Y (Pi.single j (1 : ZMod 2)))
  have hentry := congrFun hcol i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hentry

/-- Over the finite matrix monoid, the chosen right inverse is also a left inverse. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_rightInverseMatrix_mul
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y * Y.1 = 1 := by
  rw [← mul_eq_one_comm]
  exact e8SplitTailTailQuadraticIsometryModTwo_mul_rightInverseMatrix Y

/-- The inverse of a four-dimensional quadratic isometry, packaged again as an
isometry. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoInverse
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    e8SplitTailTailQuadraticIsometryModTwo :=
  ⟨e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y, by
    intro v
    have hY := Y.2 ((e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v)
    have hmul :
        Y.1.mulVec ((e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, e8SplitTailTailQuadraticIsometryModTwo_mul_rightInverseMatrix]
      simp
    rw [hmul] at hY
    exact hY.symm⟩

/-- The packaged inverse undoes the original four-dimensional isometry on
vectors. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_inverse_mulVec
    (Y : e8SplitTailTailQuadraticIsometryModTwo) (v : Fin 4 → ZMod 2) :
    (e8SplitTailTailQuadraticIsometryModTwoInverse Y).1.mulVec (Y.1.mulVec v) = v := by
  change (e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix Y).mulVec (Y.1.mulVec v) = v
  rw [Matrix.mulVec_mulVec, e8SplitTailTailQuadraticIsometryModTwo_rightInverseMatrix_mul]
  simp

/-- Any first-vector fiber is equivalent to the fixed first-vector stabilizer. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoFirstVectorFiberEquivStabilizer
    (v : e8SplitTailTailNonzeroSingularVectors) :
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer ≃
      {Y : e8SplitTailTailQuadraticIsometryModTwo //
        e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap Y = v} := by
  let T : e8SplitTailTailQuadraticIsometryModTwo :=
    Classical.choose (e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap_surjective v)
  have hT : e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap T = v :=
    Classical.choose_spec (e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap_surjective v)
  refine
    { toFun := fun H => ?_
      invFun := fun K => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨e8SplitTailTailQuadraticIsometryModTwoComp T H.1, ?_⟩
    apply Subtype.ext
    change ((T.1 * H.1.1).mulVec e8SplitTailTailFirstBasisVector) = v.1
    rw [← Matrix.mulVec_mulVec, H.2]
    have hTval := congrArg Subtype.val hT
    simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap] using hTval
  · refine ⟨e8SplitTailTailQuadraticIsometryModTwoComp
        (e8SplitTailTailQuadraticIsometryModTwoInverse T) K.1, ?_⟩
    change (((e8SplitTailTailQuadraticIsometryModTwoInverse T).1 * K.1.1).mulVec
      e8SplitTailTailFirstBasisVector) = e8SplitTailTailFirstBasisVector
    rw [← Matrix.mulVec_mulVec]
    have hKval := congrArg Subtype.val K.2
    have hKfirst : K.1.1.mulVec e8SplitTailTailFirstBasisVector = v.1 := by
      simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap] using hKval
    rw [hKfirst]
    have hTval := congrArg Subtype.val hT
    have hTfirst : T.1.mulVec e8SplitTailTailFirstBasisVector = v.1 := by
      simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap] using hTval
    rw [← hTfirst]
    exact e8SplitTailTailQuadraticIsometryModTwo_inverse_mulVec T
      e8SplitTailTailFirstBasisVector
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    change ((e8SplitTailTailQuadraticIsometryModTwoInverse T).1 * (T.1 * H.1.1)) = H.1.1
    rw [← Matrix.mul_assoc]
    change (e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix T * T.1) * H.1.1 = H.1.1
    rw [e8SplitTailTailQuadraticIsometryModTwo_rightInverseMatrix_mul, Matrix.one_mul]
  · intro K
    apply Subtype.ext
    apply Subtype.ext
    change (T.1 * ((e8SplitTailTailQuadraticIsometryModTwoInverse T).1 * K.1.1)) = K.1.1
    rw [← Matrix.mul_assoc]
    change (T.1 * e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix T) * K.1.1 = K.1.1
    rw [e8SplitTailTailQuadraticIsometryModTwo_mul_rightInverseMatrix, Matrix.one_mul]

/-- All four-dimensional first-vector fibers have the cardinality of the fixed
first-vector stabilizer. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer_at
    (v : e8SplitTailTailNonzeroSingularVectors) :
    Nat.card {Y : e8SplitTailTailQuadraticIsometryModTwo //
      e8SplitTailTailQuadraticIsometryModTwoFirstVectorMap Y = v} =
        Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer := by
  exact (Nat.card_congr
    (e8SplitTailTailQuadraticIsometryModTwoFirstVectorFiberEquivStabilizer v)).symm

/-- The four-dimensional group count is reduced to the fixed first-vector
stabilizer. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_9_mul_firstVectorStabilizer :
    Nat.card e8SplitTailTailQuadraticIsometryModTwo =
      9 * Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer :=
  e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_9_mul_of_firstVector_fiber_card
    (Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer)
    (fun v => e8SplitTailTailQuadraticIsometryModTwo_firstVectorFiber_natCard_eq_stabilizer_at v)

/-- A four-dimensional quadratic isometry sends singular partners to singular
partners. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_mulVec_mem_singularPartners
    (Y : e8SplitTailTailQuadraticIsometryModTwo) (v : Fin 4 → ZMod 2) {w : Fin 4 → ZMod 2}
    (hw : w ∈ e8SplitTailTailSingularPartners v) :
    Y.1.mulVec w ∈ e8SplitTailTailSingularPartners (Y.1.mulVec v) := by
  simp [e8SplitTailTailSingularPartners, e8SplitTailTailSingularVectors] at hw ⊢
  exact ⟨by rw [Y.2 w, hw.1],
    by rw [e8SplitTailTailQuadraticIsometryModTwo_preserves_polar Y v w, hw.2]⟩

/-- Composition inside the four-dimensional fixed first-vector stabilizer. -/
def e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerComp
    (Y Z : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer) :
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer :=
  ⟨e8SplitTailTailQuadraticIsometryModTwoComp Y.1 Z.1, by
    change ((Y.1.1 * Z.1.1).mulVec e8SplitTailTailFirstBasisVector) =
      e8SplitTailTailFirstBasisVector
    rw [← Matrix.mulVec_mulVec, Z.2, Y.2]⟩

/-- The packaged inverse of a four-dimensional first-vector stabilizer again
fixes the first basis vector. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerInverse
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer) :
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer :=
  ⟨e8SplitTailTailQuadraticIsometryModTwoInverse Y.1, by
    have h := e8SplitTailTailQuadraticIsometryModTwo_inverse_mulVec Y.1
      e8SplitTailTailFirstBasisVector
    rw [Y.2] at h
    exact h⟩

/-- Evaluation at the second basis vector maps the first-vector stabilizer to
the `4` fixed partners. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap :
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer →
      (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector : Type) := fun Y =>
  ⟨Y.1.1.mulVec e8SplitTailTailSecondBasisVector, by
    have hmem :=
      e8SplitTailTailQuadraticIsometryModTwo_mulVec_mem_singularPartners Y.1
        e8SplitTailTailFirstBasisVector
        e8SplitTailTailSecondBasisVector_mem_singularPartners_firstBasisVector
    simpa [Y.2] using hmem⟩

/-- Uniform fibers of the second-vector map give the four-dimensional
first-vector stabilizer count. -/
theorem
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer_natCard_eq_4_mul_of_secondVector_fiber_card
    (c : ℕ)
    (hfiber : ∀ w : (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector : Type),
      Nat.card {Y : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer = 4 * c := by
  rw [nat_card_eq_mul_of_fiber_card
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap c hfiber]
  rw [Nat.card_eq_finsetCard (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector),
    e8SplitTailTailSingularPartners_firstBasisVector_card]

/-- Combining the first and second vector recurrences reduces the
four-dimensional group count to one pair stabilizer fiber. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_36_mul_of_secondVector_fiber_card
    (c : ℕ)
    (hsecond : ∀ w : (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector : Type),
      Nat.card {Y : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} = c) :
    Nat.card e8SplitTailTailQuadraticIsometryModTwo = 36 * c := by
  rw [e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_9_mul_firstVectorStabilizer]
  rw [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer_natCard_eq_4_mul_of_secondVector_fiber_card
    c hsecond]
  ring

/-- If the vector defining a four-dimensional split symmetry is polar-orthogonal
to `u`, then the symmetry fixes `u`. -/
theorem e8SplitTailTailSymmetry_mulVec_of_polar_zero
    (a u : Fin 4 → ZMod 2) (ha : e8SplitTailTailQuadraticPolynomial a = 1)
    (hpolar : e8SplitTailTailPolarBilinear u a = 0) :
    (e8SplitTailTailSymmetry a ha).1.mulVec u = u := by
  change (e8SplitTailTailSymmetryMatrix a).mulVec u = u
  rw [e8SplitTailTailSymmetryMatrix_mulVec]
  rw [hpolar]
  simp

/-- The second-vector map from the fixed first-vector stabilizer onto the `4`
fixed partners is surjective. -/
theorem e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective :
    Function.Surjective
      e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap := by
  intro w
  fin_cases w <;>
    first
    | exact ⟨⟨⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0], by decide⟩, by decide⟩,
        by apply Subtype.ext; decide⟩
    | exact ⟨⟨⟨!![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 1, 1, 0], by decide⟩, by decide⟩,
        by apply Subtype.ext; decide⟩
    | exact ⟨⟨⟨!![1, 0, 0, 1; 0, 1, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1], by decide⟩, by decide⟩,
        by apply Subtype.ext; decide⟩
    | exact ⟨⟨⟨!![1, 1, 1, 1; 0, 1, 0, 0; 0, 1, 0, 1; 0, 1, 1, 0], by decide⟩, by decide⟩,
        by apply Subtype.ext; decide⟩

/-- The stabilizer of the fixed four-dimensional hyperbolic pair `(e₀,e₁)`. -/
abbrev e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer : Type :=
  {Y : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer //
    e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y =
      ⟨e8SplitTailTailSecondBasisVector,
        e8SplitTailTailSecondBasisVector_mem_singularPartners_firstBasisVector⟩}

noncomputable instance :
    Fintype e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  unfold e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer
  infer_instance

/-- Any four-dimensional second-vector fiber is equivalent to the fixed
hyperbolic-pair stabilizer. -/
noncomputable def e8SplitTailTailQuadraticIsometryModTwoSecondVectorFiberEquivFirstSecondStabilizer
    (w : (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector : Type)) :
    e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer ≃
      {Y : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer //
        e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} := by
  let T : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer :=
    Classical.choose
      (e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective w)
  have hT : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap T = w :=
    Classical.choose_spec
      (e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap_surjective w)
  refine
    { toFun := fun H => ?_
      invFun := fun K => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerComp T H.1, ?_⟩
    apply Subtype.ext
    change ((T.1.1 * H.1.1.1).mulVec e8SplitTailTailSecondBasisVector) = w.1
    rw [← Matrix.mulVec_mulVec]
    have hHsecond := congrArg Subtype.val H.2
    have hHsecond' : H.1.1.1.mulVec e8SplitTailTailSecondBasisVector =
        e8SplitTailTailSecondBasisVector := by
      simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap]
        using hHsecond
    rw [hHsecond']
    have hTval := congrArg Subtype.val hT
    simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hTval
  · refine ⟨e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerComp
        (e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerInverse T) K.1, ?_⟩
    apply Subtype.ext
    change (((e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerInverse T).1.1 *
        K.1.1.1).mulVec e8SplitTailTailSecondBasisVector) = e8SplitTailTailSecondBasisVector
    rw [← Matrix.mulVec_mulVec]
    have hKval := congrArg Subtype.val K.2
    have hKsecond : K.1.1.1.mulVec e8SplitTailTailSecondBasisVector = w.1 := by
      simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hKval
    rw [hKsecond]
    have hTval := congrArg Subtype.val hT
    have hTsecond : T.1.1.mulVec e8SplitTailTailSecondBasisVector = w.1 := by
      simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hTval
    rw [← hTsecond]
    exact e8SplitTailTailQuadraticIsometryModTwo_inverse_mulVec T.1 e8SplitTailTailSecondBasisVector
  · intro H
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change ((e8SplitTailTailQuadraticIsometryModTwoInverse T.1).1 * (T.1.1 * H.1.1.1)) =
      H.1.1.1
    rw [← Matrix.mul_assoc]
    change (e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix T.1 * T.1.1) *
      H.1.1.1 = H.1.1.1
    rw [e8SplitTailTailQuadraticIsometryModTwo_rightInverseMatrix_mul, Matrix.one_mul]
  · intro K
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (T.1.1 * ((e8SplitTailTailQuadraticIsometryModTwoInverse T.1).1 * K.1.1.1)) =
      K.1.1.1
    rw [← Matrix.mul_assoc]
    change (T.1.1 * e8SplitTailTailQuadraticIsometryModTwoRightInverseMatrix T.1) *
      K.1.1.1 = K.1.1.1
    rw [e8SplitTailTailQuadraticIsometryModTwo_mul_rightInverseMatrix, Matrix.one_mul]

/-- All four-dimensional second-vector fibers have the cardinality of the fixed
hyperbolic-pair stabilizer. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_secondVectorFiber_natCard_eq_firstSecondStabilizer_at
    (w : (e8SplitTailTailSingularPartners e8SplitTailTailFirstBasisVector : Type)) :
    Nat.card {Y : e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizer //
      e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap Y = w} =
        Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  exact (Nat.card_congr
    (e8SplitTailTailQuadraticIsometryModTwoSecondVectorFiberEquivFirstSecondStabilizer w)).symm

/-- The four-dimensional group count is reduced to its fixed hyperbolic-pair
stabilizer. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_36_mul_firstSecondStabilizer :
    Nat.card e8SplitTailTailQuadraticIsometryModTwo =
      36 * Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer :=
  e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_36_mul_of_secondVector_fiber_card
    (Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    (fun w => e8SplitTailTailQuadraticIsometryModTwo_secondVectorFiber_natCard_eq_firstSecondStabilizer_at w)

/-- Pairing with the fixed first basis vector in the four-dimensional complement
reads the second coordinate. -/
theorem e8SplitTailTailPolarBilinear_firstBasis_eq_coord_one (v : Fin 4 → ZMod 2) :
    e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector v = v 1 := by
  simp [e8SplitTailTailPolarBilinear, e8SplitTailTailFirstBasisVector]

/-- Pairing with the fixed second basis vector in the four-dimensional complement
reads the first coordinate. -/
theorem e8SplitTailTailPolarBilinear_secondBasis_eq_coord_zero (v : Fin 4 → ZMod 2) :
    e8SplitTailTailPolarBilinear e8SplitTailTailSecondBasisVector v = v 0 := by
  simp [e8SplitTailTailPolarBilinear, e8SplitTailTailSecondBasisVector]

/-- The fixed four-dimensional hyperbolic-pair stabilizer preserves the
polar-orthogonal complement of that pair. -/
theorem e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_preserves_pairComplement
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    {v : Fin 4 → ZMod 2}
    (hfirst : e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector v = 0)
    (hsecond : e8SplitTailTailPolarBilinear e8SplitTailTailSecondBasisVector v = 0) :
    e8SplitTailTailPolarBilinear e8SplitTailTailFirstBasisVector (Y.1.1.1.mulVec v) = 0 ∧
      e8SplitTailTailPolarBilinear e8SplitTailTailSecondBasisVector (Y.1.1.1.mulVec v) = 0 := by
  have hYfirst : Y.1.1.1.mulVec e8SplitTailTailFirstBasisVector =
      e8SplitTailTailFirstBasisVector :=
    Y.1.2
  have hYsecond : Y.1.1.1.mulVec e8SplitTailTailSecondBasisVector =
      e8SplitTailTailSecondBasisVector := by
    have hval := congrArg Subtype.val Y.2
    simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hval
  constructor
  · have hpolar :=
      e8SplitTailTailQuadraticIsometryModTwo_preserves_polar Y.1.1
        e8SplitTailTailFirstBasisVector v
    rw [hYfirst, hfirst] at hpolar
    exact hpolar
  · have hpolar :=
      e8SplitTailTailQuadraticIsometryModTwo_preserves_polar Y.1.1
        e8SplitTailTailSecondBasisVector v
    rw [hYsecond, hsecond] at hpolar
    exact hpolar

/-- Coordinate form of complement preservation for vectors with zero first two
coordinates in the four-dimensional complement. -/
theorem e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    {v : Fin 4 → ZMod 2} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    (Y.1.1.1.mulVec v) 0 = 0 ∧ (Y.1.1.1.mulVec v) 1 = 0 := by
  have hcomp :=
    e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_preserves_pairComplement Y
      (by simpa [e8SplitTailTailPolarBilinear_firstBasis_eq_coord_one] using h1)
      (by simpa [e8SplitTailTailPolarBilinear_secondBasis_eq_coord_zero] using h0)
  constructor
  · simpa [e8SplitTailTailPolarBilinear_secondBasis_eq_coord_zero] using hcomp.2
  · simpa [e8SplitTailTailPolarBilinear_firstBasis_eq_coord_one] using hcomp.1

/-- The two-dimensional complement of the fixed pair inside the four-dimensional
split space. -/
def e8SplitTailTailTailIndex : Fin 2 → Fin 4
  | 0 => 2
  | 1 => 3

/-- The split quadratic polynomial on the two-dimensional hyperbolic plane. -/
def e8SplitTailTailTailQuadraticPolynomial (x : Fin 2 → ZMod 2) : ZMod 2 :=
  x 0 * x 1

/-- Embed the two-dimensional complement in the four-dimensional split space. -/
def e8SplitTailTailTailVector (x : Fin 2 → ZMod 2) : Fin 4 → ZMod 2
  | 0 => 0
  | 1 => 0
  | 2 => x 0
  | 3 => x 1

/-- Project a four-dimensional vector to the final two-dimensional complement. -/
def e8SplitTailTailTailCoordinates (v : Fin 4 → ZMod 2) : Fin 2 → ZMod 2 :=
  fun i => v (e8SplitTailTailTailIndex i)

/-- Two-dimensional coordinates recover an embedded complement vector. -/
theorem e8SplitTailTailTailCoordinates_tailTailTailVector (x : Fin 2 → ZMod 2) :
    e8SplitTailTailTailCoordinates (e8SplitTailTailTailVector x) = x := by
  funext i
  fin_cases i <;> rfl

/-- If a four-dimensional vector has zero first hyperbolic coordinates, it is
recovered from its final two-dimensional complement coordinates. -/
theorem e8SplitTailTailTailVector_tailTailTailCoordinates_of_zero
    {v : Fin 4 → ZMod 2} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    e8SplitTailTailTailVector (e8SplitTailTailTailCoordinates v) = v := by
  funext i
  fin_cases i <;> simp [e8SplitTailTailTailVector, e8SplitTailTailTailCoordinates,
    e8SplitTailTailTailIndex, h0, h1]

/-- The four-dimensional split polynomial restricts to the final two-dimensional
hyperbolic polynomial. -/
theorem e8SplitTailTailQuadraticPolynomial_tailTailTailVector (x : Fin 2 → ZMod 2) :
    e8SplitTailTailQuadraticPolynomial (e8SplitTailTailTailVector x) =
      e8SplitTailTailTailQuadraticPolynomial x := by
  simp [e8SplitTailTailQuadraticPolynomial, e8SplitTailTailTailQuadraticPolynomial,
    e8SplitTailTailTailVector]

/-- The four-dimensional split polynomial decomposes into the fixed hyperbolic
plane and the final two-dimensional complement. -/
theorem e8SplitTailTailQuadraticPolynomial_eq_head_tail (v : Fin 4 → ZMod 2) :
    e8SplitTailTailQuadraticPolynomial v =
      v 0 * v 1 + e8SplitTailTailTailQuadraticPolynomial
        (e8SplitTailTailTailCoordinates v) := by
  simp [e8SplitTailTailQuadraticPolynomial, e8SplitTailTailTailQuadraticPolynomial,
    e8SplitTailTailTailCoordinates, e8SplitTailTailTailIndex]

/-- A matrix over `𝔽₂` preserving the two-dimensional hyperbolic polynomial. -/
abbrev e8SplitTailTailTailQuadraticIsometryModTwo : Type :=
  {Y : Matrix (Fin 2) (Fin 2) (ZMod 2) //
    ∀ v : Fin 2 → ZMod 2,
      e8SplitTailTailTailQuadraticPolynomial (Y.mulVec v) =
        e8SplitTailTailTailQuadraticPolynomial v}

noncomputable instance : Fintype e8SplitTailTailTailQuadraticIsometryModTwo := by
  unfold e8SplitTailTailTailQuadraticIsometryModTwo
  infer_instance

/-- The two-dimensional hyperbolic isometry type has order `2`. -/
theorem e8SplitTailTailTailQuadraticIsometryModTwo_natCard_eq_two :
    Nat.card e8SplitTailTailTailQuadraticIsometryModTwo = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- A total inverse to the final two-dimensional complement index. -/
def e8SplitTailTailTailIndexInv : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1

/-- The total inverse recovers the original two-dimensional index on the final
complement. -/
theorem e8SplitTailTailTailIndexInv_tailTailTailIndex (i : Fin 2) :
    e8SplitTailTailTailIndexInv (e8SplitTailTailTailIndex i) = i := by
  fin_cases i <;> rfl

/-- Restrict a fixed-pair four-dimensional isometry to the final two-dimensional
complement. -/
def e8SplitTailTailFirstSecondStabilizerTailMatrix
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => Y.1.1.1 (e8SplitTailTailTailIndex i) (e8SplitTailTailTailIndex j)

/-- Restricting the four-dimensional matrix action to final complement
coordinates agrees with the final tail matrix action. -/
theorem e8SplitTailTailFirstSecondStabilizer_tailCoordinates_mulVec_tailVector
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    (x : Fin 2 → ZMod 2) :
    e8SplitTailTailTailCoordinates (Y.1.1.1.mulVec (e8SplitTailTailTailVector x)) =
      (e8SplitTailTailFirstSecondStabilizerTailMatrix Y).mulVec x := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailTailCoordinates, e8SplitTailTailTailVector,
      e8SplitTailTailFirstSecondStabilizerTailMatrix, e8SplitTailTailTailIndex,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]

/-- The restricted final tail matrix preserves the two-dimensional hyperbolic
polynomial. -/
theorem e8SplitTailTailFirstSecondStabilizerTailMatrix_mem
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    ∀ v : Fin 2 → ZMod 2,
      e8SplitTailTailTailQuadraticPolynomial
          ((e8SplitTailTailFirstSecondStabilizerTailMatrix Y).mulVec v) =
        e8SplitTailTailTailQuadraticPolynomial v := by
  intro v
  have htail :=
    e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
      (v := e8SplitTailTailTailVector v) rfl rfl
  calc
    e8SplitTailTailTailQuadraticPolynomial
        ((e8SplitTailTailFirstSecondStabilizerTailMatrix Y).mulVec v)
        = e8SplitTailTailTailQuadraticPolynomial
            (e8SplitTailTailTailCoordinates (Y.1.1.1.mulVec (e8SplitTailTailTailVector v))) := by
            rw [e8SplitTailTailFirstSecondStabilizer_tailCoordinates_mulVec_tailVector]
    _ = e8SplitTailTailQuadraticPolynomial
          (e8SplitTailTailTailVector
            (e8SplitTailTailTailCoordinates (Y.1.1.1.mulVec (e8SplitTailTailTailVector v)))) := by
            rw [e8SplitTailTailQuadraticPolynomial_tailTailTailVector]
    _ = e8SplitTailTailQuadraticPolynomial (Y.1.1.1.mulVec (e8SplitTailTailTailVector v)) := by
            rw [e8SplitTailTailTailVector_tailTailTailCoordinates_of_zero htail.1 htail.2]
    _ = e8SplitTailTailQuadraticPolynomial (e8SplitTailTailTailVector v) :=
            Y.1.1.2 (e8SplitTailTailTailVector v)
    _ = e8SplitTailTailTailQuadraticPolynomial v := by
            rw [e8SplitTailTailQuadraticPolynomial_tailTailTailVector]

/-- The restriction of a fixed-pair four-dimensional isometry as a
two-dimensional hyperbolic isometry. -/
def e8SplitTailTailFirstSecondStabilizerToTailIsometry
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    e8SplitTailTailTailQuadraticIsometryModTwo :=
  ⟨e8SplitTailTailFirstSecondStabilizerTailMatrix Y,
    e8SplitTailTailFirstSecondStabilizerTailMatrix_mem Y⟩

/-- Extend a two-dimensional hyperbolic isometry by the identity on the fixed
four-dimensional hyperbolic plane. -/
def e8SplitTailTailTailIsometryExtendMatrix
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = 1 then
      if j = 1 then 1 else 0
    else if j = 0 then
      0
    else if j = 1 then
      0
    else
      Y.1 (e8SplitTailTailTailIndexInv i) (e8SplitTailTailTailIndexInv j)

/-- The final tail block of the extended matrix acts by the original
two-dimensional isometry. -/
theorem e8SplitTailTailTailIsometryExtendMatrix_tailCoordinates_mulVec
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) (v : Fin 4 → ZMod 2) :
    e8SplitTailTailTailCoordinates ((e8SplitTailTailTailIsometryExtendMatrix Y).mulVec v) =
      Y.1.mulVec (e8SplitTailTailTailCoordinates v) := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailTailCoordinates, e8SplitTailTailTailIsometryExtendMatrix,
      e8SplitTailTailTailIndex, e8SplitTailTailTailIndexInv, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_two]

/-- The extended two-dimensional isometry preserves the four-dimensional split
polynomial. -/
theorem e8SplitTailTailTailIsometryExtendMatrix_mem
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) :
    ∀ v : Fin 4 → ZMod 2,
      e8SplitTailTailQuadraticPolynomial ((e8SplitTailTailTailIsometryExtendMatrix Y).mulVec v) =
        e8SplitTailTailQuadraticPolynomial v := by
  intro v
  rw [e8SplitTailTailQuadraticPolynomial_eq_head_tail,
    e8SplitTailTailQuadraticPolynomial_eq_head_tail]
  have h0 : ((e8SplitTailTailTailIsometryExtendMatrix Y).mulVec v) 0 = v 0 := by
    simp [e8SplitTailTailTailIsometryExtendMatrix, Matrix.mulVec, dotProduct]
  have h1 : ((e8SplitTailTailTailIsometryExtendMatrix Y).mulVec v) 1 = v 1 := by
    simp [e8SplitTailTailTailIsometryExtendMatrix, Matrix.mulVec, dotProduct]
  rw [h0, h1, e8SplitTailTailTailIsometryExtendMatrix_tailCoordinates_mulVec, Y.2]

/-- The extended two-dimensional isometry fixes the first four-dimensional basis
vector. -/
theorem e8SplitTailTailTailIsometryExtendMatrix_mulVec_firstBasis
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) :
    (e8SplitTailTailTailIsometryExtendMatrix Y).mulVec e8SplitTailTailFirstBasisVector =
      e8SplitTailTailFirstBasisVector := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailTailIsometryExtendMatrix, e8SplitTailTailFirstBasisVector,
      Matrix.mulVec, dotProduct]

/-- The extended two-dimensional isometry fixes the second four-dimensional
basis vector. -/
theorem e8SplitTailTailTailIsometryExtendMatrix_mulVec_secondBasis
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) :
    (e8SplitTailTailTailIsometryExtendMatrix Y).mulVec e8SplitTailTailSecondBasisVector =
      e8SplitTailTailSecondBasisVector := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailTailIsometryExtendMatrix, e8SplitTailTailSecondBasisVector,
      Matrix.mulVec, dotProduct]

/-- Extend a two-dimensional hyperbolic isometry to the fixed hyperbolic-pair
stabilizer in the four-dimensional split space. -/
def e8SplitTailTailTailIsometryToFirstSecondStabilizer
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) :
    e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  refine ⟨⟨⟨e8SplitTailTailTailIsometryExtendMatrix Y,
    e8SplitTailTailTailIsometryExtendMatrix_mem Y⟩,
    e8SplitTailTailTailIsometryExtendMatrix_mulVec_firstBasis Y⟩, ?_⟩
  apply Subtype.ext
  change (e8SplitTailTailTailIsometryExtendMatrix Y).mulVec e8SplitTailTailSecondBasisVector =
    e8SplitTailTailSecondBasisVector
  exact e8SplitTailTailTailIsometryExtendMatrix_mulVec_secondBasis Y

/-- Restricting the identity-on-hyperbolic-plane extension recovers the original
two-dimensional isometry. -/
theorem e8SplitTailTailFirstSecondStabilizerToTailIsometry_tailExtension
    (Y : e8SplitTailTailTailQuadraticIsometryModTwo) :
    e8SplitTailTailFirstSecondStabilizerToTailIsometry
        (e8SplitTailTailTailIsometryToFirstSecondStabilizer Y) = Y := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8SplitTailTailFirstSecondStabilizerToTailIsometry,
      e8SplitTailTailFirstSecondStabilizerTailMatrix,
      e8SplitTailTailTailIsometryToFirstSecondStabilizer,
      e8SplitTailTailTailIsometryExtendMatrix, e8SplitTailTailTailIndex,
      e8SplitTailTailTailIndexInv]

/-- Extending the final-tail restriction of a fixed-pair stabilizer recovers the
original four-dimensional isometry. -/
theorem e8SplitTailTailTailIsometryToFirstSecondStabilizer_tailRestriction
    (Y : e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    e8SplitTailTailTailIsometryToFirstSecondStabilizer
        (e8SplitTailTailFirstSecondStabilizerToTailIsometry Y) = Y := by
  have hcol0 : ∀ i : Fin 4, Y.1.1.1 i 0 = e8SplitTailTailFirstBasisVector i := by
    intro i
    have h := congrFun Y.1.2 i
    simpa [Matrix.mulVec, dotProduct, e8SplitTailTailFirstBasisVector, Fin.sum_univ_four] using h
  have hYsecond : Y.1.1.1.mulVec e8SplitTailTailSecondBasisVector =
      e8SplitTailTailSecondBasisVector := by
    have hval := congrArg Subtype.val Y.2
    simpa [e8SplitTailTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hval
  have hcol1 : ∀ i : Fin 4, Y.1.1.1 i 1 = e8SplitTailTailSecondBasisVector i := by
    intro i
    have h := congrFun hYsecond i
    simpa [Matrix.mulVec, dotProduct, e8SplitTailTailSecondBasisVector, Fin.sum_univ_four] using h
  have hrow0tail : ∀ k : Fin 2, Y.1.1.1 0 (e8SplitTailTailTailIndex k) = 0 := by
    intro k
    have htail :=
      e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
        (v := e8SplitTailTailTailVector (Pi.single k (1 : ZMod 2))) rfl rfl
    have h := htail.1
    fin_cases k <;>
      simpa [e8SplitTailTailTailVector, e8SplitTailTailTailIndex, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four, Pi.single_apply] using h
  have hrow1tail : ∀ k : Fin 2, Y.1.1.1 1 (e8SplitTailTailTailIndex k) = 0 := by
    intro k
    have htail :=
      e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
        (v := e8SplitTailTailTailVector (Pi.single k (1 : ZMod 2))) rfl rfl
    have h := htail.2
    fin_cases k <;>
      simpa [e8SplitTailTailTailVector, e8SplitTailTailTailIndex, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four, Pi.single_apply] using h
  have hrow02 : Y.1.1.1 0 2 = 0 := by simpa [e8SplitTailTailTailIndex] using hrow0tail 0
  have hrow03 : Y.1.1.1 0 3 = 0 := by simpa [e8SplitTailTailTailIndex] using hrow0tail 1
  have hrow12 : Y.1.1.1 1 2 = 0 := by simpa [e8SplitTailTailTailIndex] using hrow1tail 0
  have hrow13 : Y.1.1.1 1 3 = 0 := by simpa [e8SplitTailTailTailIndex] using hrow1tail 1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8SplitTailTailTailIsometryToFirstSecondStabilizer,
      e8SplitTailTailFirstSecondStabilizerToTailIsometry,
      e8SplitTailTailTailIsometryExtendMatrix,
      e8SplitTailTailFirstSecondStabilizerTailMatrix, e8SplitTailTailTailIndex,
      e8SplitTailTailTailIndexInv, e8SplitTailTailFirstBasisVector,
      e8SplitTailTailSecondBasisVector, hcol0, hcol1, hrow02, hrow03, hrow12, hrow13]

/-- The fixed four-dimensional hyperbolic-pair stabilizer is equivalent to the
two-dimensional hyperbolic-isometry type. -/
noncomputable def e8SplitTailTailFirstSecondStabilizerEquivTailIsometry :
    e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer ≃
      e8SplitTailTailTailQuadraticIsometryModTwo where
  toFun := e8SplitTailTailFirstSecondStabilizerToTailIsometry
  invFun := e8SplitTailTailTailIsometryToFirstSecondStabilizer
  left_inv := e8SplitTailTailTailIsometryToFirstSecondStabilizer_tailRestriction
  right_inv := e8SplitTailTailFirstSecondStabilizerToTailIsometry_tailExtension

/-- The fixed four-dimensional hyperbolic-pair stabilizer has order `2`. -/
theorem e8SplitTailTailQuadraticIsometryModTwoFirstSecondStabilizer_natCard_eq_two :
    Nat.card e8SplitTailTailQuadraticIsometryModTwoFirstSecondVectorStabilizer = 2 := by
  rw [← e8SplitTailTailTailQuadraticIsometryModTwo_natCard_eq_two]
  exact Nat.card_congr e8SplitTailTailFirstSecondStabilizerEquivTailIsometry

/-- The four-dimensional split isometry group has order `72`. -/
theorem e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_72 :
    Nat.card e8SplitTailTailQuadraticIsometryModTwo = 72 := by
  rw [e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_36_mul_firstSecondStabilizer,
    e8SplitTailTailQuadraticIsometryModTwoFirstSecondStabilizer_natCard_eq_two]

/-- Pairing with the fixed first tail basis vector reads the second tail coordinate. -/
theorem e8SplitTailPolarBilinear_firstBasis_eq_coord_one (v : Fin 6 → ZMod 2) :
    e8SplitTailPolarBilinear e8SplitTailFirstBasisVector v = v 1 := by
  simp [e8SplitTailPolarBilinear, e8SplitTailFirstBasisVector]

/-- Pairing with the fixed second tail basis vector reads the first tail coordinate. -/
theorem e8SplitTailPolarBilinear_secondBasis_eq_coord_zero (v : Fin 6 → ZMod 2) :
    e8SplitTailPolarBilinear e8SplitTailSecondBasisVector v = v 0 := by
  simp [e8SplitTailPolarBilinear, e8SplitTailSecondBasisVector]

/-- The fixed tail hyperbolic-pair stabilizer preserves the polar-orthogonal
complement of that pair. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_preserves_pairComplement
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    {v : Fin 6 → ZMod 2}
    (hfirst : e8SplitTailPolarBilinear e8SplitTailFirstBasisVector v = 0)
    (hsecond : e8SplitTailPolarBilinear e8SplitTailSecondBasisVector v = 0) :
    e8SplitTailPolarBilinear e8SplitTailFirstBasisVector (Y.1.1.1.mulVec v) = 0 ∧
      e8SplitTailPolarBilinear e8SplitTailSecondBasisVector (Y.1.1.1.mulVec v) = 0 := by
  have hYfirst : Y.1.1.1.mulVec e8SplitTailFirstBasisVector = e8SplitTailFirstBasisVector :=
    Y.1.2
  have hYsecond : Y.1.1.1.mulVec e8SplitTailSecondBasisVector =
      e8SplitTailSecondBasisVector := by
    have hval := congrArg Subtype.val Y.2
    simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hval
  constructor
  · have hpolar :=
      e8SplitTailQuadraticIsometryModTwo_preserves_polar Y.1.1 e8SplitTailFirstBasisVector v
    rw [hYfirst, hfirst] at hpolar
    exact hpolar
  · have hpolar :=
      e8SplitTailQuadraticIsometryModTwo_preserves_polar Y.1.1 e8SplitTailSecondBasisVector v
    rw [hYsecond, hsecond] at hpolar
    exact hpolar

/-- Coordinate form of complement preservation for tail vectors with zero first
two coordinates. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    {v : Fin 6 → ZMod 2} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    (Y.1.1.1.mulVec v) 0 = 0 ∧ (Y.1.1.1.mulVec v) 1 = 0 := by
  have hcomp :=
    e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_preserves_pairComplement Y
      (by simpa [e8SplitTailPolarBilinear_firstBasis_eq_coord_one] using h1)
      (by simpa [e8SplitTailPolarBilinear_secondBasis_eq_coord_zero] using h0)
  constructor
  · simpa [e8SplitTailPolarBilinear_secondBasis_eq_coord_zero] using hcomp.2
  · simpa [e8SplitTailPolarBilinear_firstBasis_eq_coord_one] using hcomp.1

/-- Restrict a fixed-pair tail isometry to the four-dimensional complement. -/
def e8SplitTailFirstSecondStabilizerTailMatrix
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => Y.1.1.1 (e8SplitTailTailIndex i) (e8SplitTailTailIndex j)

/-- Restricting the six-dimensional tail action to four-dimensional complement
coordinates agrees with the complement matrix action. -/
theorem e8SplitTailFirstSecondStabilizer_tailCoordinates_mulVec_tailVector
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    (x : Fin 4 → ZMod 2) :
    e8SplitTailTailCoordinates (Y.1.1.1.mulVec (e8SplitTailTailVector x)) =
      (e8SplitTailFirstSecondStabilizerTailMatrix Y).mulVec x := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailCoordinates, e8SplitTailTailVector,
      e8SplitTailFirstSecondStabilizerTailMatrix, e8SplitTailTailIndex,
      Matrix.mulVec, dotProduct, Fin.sum_univ_six, Fin.sum_univ_four]

/-- The restricted four-dimensional matrix preserves the split complement
polynomial. -/
theorem e8SplitTailFirstSecondStabilizerTailMatrix_mem
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    ∀ v : Fin 4 → ZMod 2,
      e8SplitTailTailQuadraticPolynomial
          ((e8SplitTailFirstSecondStabilizerTailMatrix Y).mulVec v) =
        e8SplitTailTailQuadraticPolynomial v := by
  intro v
  have htail :=
    e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
      (v := e8SplitTailTailVector v) rfl rfl
  calc
    e8SplitTailTailQuadraticPolynomial
        ((e8SplitTailFirstSecondStabilizerTailMatrix Y).mulVec v)
        = e8SplitTailTailQuadraticPolynomial
            (e8SplitTailTailCoordinates (Y.1.1.1.mulVec (e8SplitTailTailVector v))) := by
            rw [e8SplitTailFirstSecondStabilizer_tailCoordinates_mulVec_tailVector]
    _ = e8SplitTailQuadraticPolynomial
          (e8SplitTailTailVector
            (e8SplitTailTailCoordinates (Y.1.1.1.mulVec (e8SplitTailTailVector v)))) := by
            rw [e8SplitTailQuadraticPolynomial_tailTailVector]
    _ = e8SplitTailQuadraticPolynomial (Y.1.1.1.mulVec (e8SplitTailTailVector v)) := by
            rw [e8SplitTailTailVector_tailTailCoordinates_of_zero htail.1 htail.2]
    _ = e8SplitTailQuadraticPolynomial (e8SplitTailTailVector v) :=
            Y.1.1.2 (e8SplitTailTailVector v)
    _ = e8SplitTailTailQuadraticPolynomial v := by
            rw [e8SplitTailQuadraticPolynomial_tailTailVector]

/-- The restriction of a fixed-pair tail isometry as a four-dimensional split
isometry. -/
def e8SplitTailFirstSecondStabilizerToTailTailIsometry
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    e8SplitTailTailQuadraticIsometryModTwo :=
  ⟨e8SplitTailFirstSecondStabilizerTailMatrix Y,
    e8SplitTailFirstSecondStabilizerTailMatrix_mem Y⟩

/-- A total inverse to the four-dimensional complement index. -/
def e8SplitTailTailIndexInv : Fin 6 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3

/-- The total inverse recovers the original four-dimensional index on the tail
complement. -/
theorem e8SplitTailTailIndexInv_tailTailIndex (i : Fin 4) :
    e8SplitTailTailIndexInv (e8SplitTailTailIndex i) = i := by
  fin_cases i <;> rfl

/-- The six-dimensional tail polynomial decomposes into the fixed hyperbolic
plane and the four-dimensional complement. -/
theorem e8SplitTailQuadraticPolynomial_eq_head_tail (v : Fin 6 → ZMod 2) :
    e8SplitTailQuadraticPolynomial v =
      v 0 * v 1 + e8SplitTailTailQuadraticPolynomial (e8SplitTailTailCoordinates v) := by
  simp [e8SplitTailQuadraticPolynomial, e8SplitTailTailQuadraticPolynomial,
    e8SplitTailTailCoordinates, e8SplitTailTailIndex]
  ring_nf

/-- Extend a four-dimensional split isometry by the identity on the fixed tail
hyperbolic plane. -/
def e8SplitTailTailIsometryExtendMatrix (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = 1 then
      if j = 1 then 1 else 0
    else if j = 0 then
      0
    else if j = 1 then
      0
    else
      Y.1 (e8SplitTailTailIndexInv i) (e8SplitTailTailIndexInv j)

/-- The four-dimensional block of the extended matrix acts by the original
complement isometry. -/
theorem e8SplitTailTailIsometryExtendMatrix_tailCoordinates_mulVec
    (Y : e8SplitTailTailQuadraticIsometryModTwo) (v : Fin 6 → ZMod 2) :
    e8SplitTailTailCoordinates ((e8SplitTailTailIsometryExtendMatrix Y).mulVec v) =
      Y.1.mulVec (e8SplitTailTailCoordinates v) := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailCoordinates, e8SplitTailTailIsometryExtendMatrix,
      e8SplitTailTailIndex, e8SplitTailTailIndexInv, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six, Fin.sum_univ_four]

/-- The extended four-dimensional isometry preserves the six-dimensional tail
split polynomial. -/
theorem e8SplitTailTailIsometryExtendMatrix_mem
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    ∀ v : Fin 6 → ZMod 2,
      e8SplitTailQuadraticPolynomial ((e8SplitTailTailIsometryExtendMatrix Y).mulVec v) =
        e8SplitTailQuadraticPolynomial v := by
  intro v
  rw [e8SplitTailQuadraticPolynomial_eq_head_tail,
    e8SplitTailQuadraticPolynomial_eq_head_tail]
  have h0 : ((e8SplitTailTailIsometryExtendMatrix Y).mulVec v) 0 = v 0 := by
    simp [e8SplitTailTailIsometryExtendMatrix, Matrix.mulVec, dotProduct]
  have h1 : ((e8SplitTailTailIsometryExtendMatrix Y).mulVec v) 1 = v 1 := by
    simp [e8SplitTailTailIsometryExtendMatrix, Matrix.mulVec, dotProduct]
  rw [h0, h1, e8SplitTailTailIsometryExtendMatrix_tailCoordinates_mulVec, Y.2]

/-- The extended four-dimensional isometry fixes the first tail basis vector. -/
theorem e8SplitTailTailIsometryExtendMatrix_mulVec_firstBasis
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    (e8SplitTailTailIsometryExtendMatrix Y).mulVec e8SplitTailFirstBasisVector =
      e8SplitTailFirstBasisVector := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailIsometryExtendMatrix, e8SplitTailFirstBasisVector,
      Matrix.mulVec, dotProduct]

/-- The extended four-dimensional isometry fixes the second tail basis vector. -/
theorem e8SplitTailTailIsometryExtendMatrix_mulVec_secondBasis
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    (e8SplitTailTailIsometryExtendMatrix Y).mulVec e8SplitTailSecondBasisVector =
      e8SplitTailSecondBasisVector := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailTailIsometryExtendMatrix, e8SplitTailSecondBasisVector,
      Matrix.mulVec, dotProduct]

/-- Extend a four-dimensional complement isometry to the fixed tail hyperbolic
pair stabilizer. -/
def e8SplitTailTailIsometryToFirstSecondStabilizer
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  refine ⟨⟨⟨e8SplitTailTailIsometryExtendMatrix Y,
    e8SplitTailTailIsometryExtendMatrix_mem Y⟩,
    e8SplitTailTailIsometryExtendMatrix_mulVec_firstBasis Y⟩, ?_⟩
  apply Subtype.ext
  change (e8SplitTailTailIsometryExtendMatrix Y).mulVec e8SplitTailSecondBasisVector =
    e8SplitTailSecondBasisVector
  exact e8SplitTailTailIsometryExtendMatrix_mulVec_secondBasis Y

/-- Restricting the identity-on-hyperbolic-plane extension recovers the original
four-dimensional isometry. -/
theorem e8SplitTailFirstSecondStabilizerToTailTailIsometry_tailExtension
    (Y : e8SplitTailTailQuadraticIsometryModTwo) :
    e8SplitTailFirstSecondStabilizerToTailTailIsometry
        (e8SplitTailTailIsometryToFirstSecondStabilizer Y) = Y := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8SplitTailFirstSecondStabilizerToTailTailIsometry,
      e8SplitTailFirstSecondStabilizerTailMatrix,
      e8SplitTailTailIsometryToFirstSecondStabilizer,
      e8SplitTailTailIsometryExtendMatrix, e8SplitTailTailIndex,
      e8SplitTailTailIndexInv]

/-- Extending the four-dimensional restriction of a fixed-pair tail stabilizer
recovers the original six-dimensional tail isometry. -/
theorem e8SplitTailTailIsometryToFirstSecondStabilizer_tailRestriction
    (Y : e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    e8SplitTailTailIsometryToFirstSecondStabilizer
        (e8SplitTailFirstSecondStabilizerToTailTailIsometry Y) = Y := by
  have hcol0 : ∀ i : Fin 6, Y.1.1.1 i 0 = e8SplitTailFirstBasisVector i := by
    intro i
    have h := congrFun Y.1.2 i
    simpa [Matrix.mulVec, dotProduct, e8SplitTailFirstBasisVector, Fin.sum_univ_six] using h
  have hYsecond : Y.1.1.1.mulVec e8SplitTailSecondBasisVector =
      e8SplitTailSecondBasisVector := by
    have hval := congrArg Subtype.val Y.2
    simpa [e8SplitTailQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hval
  have hcol1 : ∀ i : Fin 6, Y.1.1.1 i 1 = e8SplitTailSecondBasisVector i := by
    intro i
    have h := congrFun hYsecond i
    simpa [Matrix.mulVec, dotProduct, e8SplitTailSecondBasisVector, Fin.sum_univ_six] using h
  have hrow0tail : ∀ k : Fin 4, Y.1.1.1 0 (e8SplitTailTailIndex k) = 0 := by
    intro k
    have htail :=
      e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
        (v := e8SplitTailTailVector (Pi.single k (1 : ZMod 2))) rfl rfl
    have h := htail.1
    fin_cases k <;>
      simpa [e8SplitTailTailVector, e8SplitTailTailIndex, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six, Pi.single_apply] using h
  have hrow1tail : ∀ k : Fin 4, Y.1.1.1 1 (e8SplitTailTailIndex k) = 0 := by
    intro k
    have htail :=
      e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
        (v := e8SplitTailTailVector (Pi.single k (1 : ZMod 2))) rfl rfl
    have h := htail.2
    fin_cases k <;>
      simpa [e8SplitTailTailVector, e8SplitTailTailIndex, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six, Pi.single_apply] using h
  have hrow02 : Y.1.1.1 0 2 = 0 := by simpa [e8SplitTailTailIndex] using hrow0tail 0
  have hrow03 : Y.1.1.1 0 3 = 0 := by simpa [e8SplitTailTailIndex] using hrow0tail 1
  have hrow04 : Y.1.1.1 0 4 = 0 := by simpa [e8SplitTailTailIndex] using hrow0tail 2
  have hrow05 : Y.1.1.1 0 5 = 0 := by simpa [e8SplitTailTailIndex] using hrow0tail 3
  have hrow12 : Y.1.1.1 1 2 = 0 := by simpa [e8SplitTailTailIndex] using hrow1tail 0
  have hrow13 : Y.1.1.1 1 3 = 0 := by simpa [e8SplitTailTailIndex] using hrow1tail 1
  have hrow14 : Y.1.1.1 1 4 = 0 := by simpa [e8SplitTailTailIndex] using hrow1tail 2
  have hrow15 : Y.1.1.1 1 5 = 0 := by simpa [e8SplitTailTailIndex] using hrow1tail 3
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8SplitTailTailIsometryToFirstSecondStabilizer,
      e8SplitTailFirstSecondStabilizerToTailTailIsometry,
      e8SplitTailTailIsometryExtendMatrix,
      e8SplitTailFirstSecondStabilizerTailMatrix, e8SplitTailTailIndex,
      e8SplitTailTailIndexInv, e8SplitTailFirstBasisVector,
      e8SplitTailSecondBasisVector, hcol0, hcol1, hrow02, hrow03, hrow04,
      hrow05, hrow12, hrow13, hrow14, hrow15]

/-- The fixed tail hyperbolic-pair stabilizer is equivalent to the
four-dimensional complement isometry type. -/
noncomputable def e8SplitTailFirstSecondStabilizerEquivTailTailIsometry :
    e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer ≃
      e8SplitTailTailQuadraticIsometryModTwo where
  toFun := e8SplitTailFirstSecondStabilizerToTailTailIsometry
  invFun := e8SplitTailTailIsometryToFirstSecondStabilizer
  left_inv := e8SplitTailTailIsometryToFirstSecondStabilizer_tailRestriction
  right_inv := e8SplitTailFirstSecondStabilizerToTailTailIsometry_tailExtension

/-- The fixed tail hyperbolic-pair stabilizer has order `72`. -/
theorem e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_natCard_eq_72 :
    Nat.card e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer = 72 := by
  rw [← e8SplitTailTailQuadraticIsometryModTwo_natCard_eq_72]
  exact Nat.card_congr e8SplitTailFirstSecondStabilizerEquivTailTailIsometry

/-- The six-dimensional tail isometry group has order `40320`. -/
theorem e8SplitTailQuadraticIsometryModTwo_natCard_eq_40320 :
    Nat.card e8SplitTailQuadraticIsometryModTwo = 40320 := by
  rw [e8SplitTailQuadraticIsometryModTwo_natCard_eq_560_mul_firstSecondStabilizer,
    e8SplitTailQuadraticIsometryModTwoFirstSecondVectorStabilizer_natCard_eq_72]

/-- Restrict a fixed-pair split E8 isometry to the six-dimensional complement. -/
def e8SplitFirstSecondStabilizerTailMatrix
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j => Y.1.1.1 (e8SplitTailIndex i) (e8SplitTailIndex j)

/-- Restricting the full matrix action to the tail coordinates agrees with the
tail matrix action. -/
theorem e8SplitFirstSecondStabilizer_tailCoordinates_mulVec_tailVector
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer)
    (x : Fin 6 → ZMod 2) :
    e8SplitTailCoordinates (Y.1.1.1.mulVec (e8SplitTailVector x)) =
      (e8SplitFirstSecondStabilizerTailMatrix Y).mulVec x := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailCoordinates, e8SplitTailVector, e8SplitFirstSecondStabilizerTailMatrix,
      e8SplitTailIndex, Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Fin.sum_univ_six]

/-- The restricted tail matrix of a fixed-pair split E8 isometry preserves the
six-dimensional split quadratic polynomial. -/
theorem e8SplitFirstSecondStabilizerTailMatrix_mem
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    ∀ v : Fin 6 → ZMod 2,
      e8SplitTailQuadraticPolynomial
          ((e8SplitFirstSecondStabilizerTailMatrix Y).mulVec v) =
        e8SplitTailQuadraticPolynomial v := by
  intro v
  have htail :=
    e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
      (v := e8SplitTailVector v) rfl rfl
  calc
    e8SplitTailQuadraticPolynomial
        ((e8SplitFirstSecondStabilizerTailMatrix Y).mulVec v)
        = e8SplitTailQuadraticPolynomial
            (e8SplitTailCoordinates (Y.1.1.1.mulVec (e8SplitTailVector v))) := by
            rw [e8SplitFirstSecondStabilizer_tailCoordinates_mulVec_tailVector]
    _ = e8SplitQuadraticPolynomial
          (e8SplitTailVector
            (e8SplitTailCoordinates (Y.1.1.1.mulVec (e8SplitTailVector v)))) := by
            rw [e8SplitQuadraticPolynomial_tailVector]
    _ = e8SplitQuadraticPolynomial (Y.1.1.1.mulVec (e8SplitTailVector v)) := by
            rw [e8SplitTailVector_tailCoordinates_of_zero htail.1 htail.2]
    _ = e8SplitQuadraticPolynomial (e8SplitTailVector v) := Y.1.1.2 (e8SplitTailVector v)
    _ = e8SplitTailQuadraticPolynomial v := by
            rw [e8SplitQuadraticPolynomial_tailVector]

/-- The restriction of a fixed-pair split E8 isometry as a tail quadratic
isometry. -/
def e8SplitFirstSecondStabilizerToTailIsometry
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    e8SplitTailQuadraticIsometryModTwo :=
  ⟨e8SplitFirstSecondStabilizerTailMatrix Y,
    e8SplitFirstSecondStabilizerTailMatrix_mem Y⟩

/-- A total inverse to `e8SplitTailIndex`, used only on tail rows and columns. -/
def e8SplitTailIndexInv : Fin 8 → Fin 6
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 5

/-- The total inverse recovers the original six-dimensional index on the tail. -/
theorem e8SplitTailIndexInv_tailIndex (i : Fin 6) :
    e8SplitTailIndexInv (e8SplitTailIndex i) = i := by
  fin_cases i <;> rfl

/-- The full split polynomial decomposes into the fixed hyperbolic plane and the
six-dimensional tail polynomial. -/
theorem e8SplitQuadraticPolynomial_eq_head_tail (v : Fin 8 → ZMod 2) :
    e8SplitQuadraticPolynomial v =
      v 0 * v 1 + e8SplitTailQuadraticPolynomial (e8SplitTailCoordinates v) := by
  simp [e8SplitQuadraticPolynomial, e8SplitTailQuadraticPolynomial, e8SplitTailCoordinates]
  ring

/-- Extend a six-dimensional tail isometry by the identity on the fixed
hyperbolic plane. -/
def e8SplitTailIsometryExtendMatrix (Y : e8SplitTailQuadraticIsometryModTwo) :
    Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = 1 then
      if j = 1 then 1 else 0
    else if j = 0 then
      0
    else if j = 1 then
      0
    else
      Y.1 (e8SplitTailIndexInv i) (e8SplitTailIndexInv j)

/-- The tail block of the extended matrix acts by the original tail isometry. -/
theorem e8SplitTailIsometryExtendMatrix_tailCoordinates_mulVec
    (Y : e8SplitTailQuadraticIsometryModTwo) (v : Fin 8 → ZMod 2) :
    e8SplitTailCoordinates ((e8SplitTailIsometryExtendMatrix Y).mulVec v) =
      Y.1.mulVec (e8SplitTailCoordinates v) := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailCoordinates, e8SplitTailIsometryExtendMatrix, e8SplitTailIndexInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Fin.sum_univ_six]

/-- The extended tail isometry preserves the full split E8 quadratic polynomial. -/
theorem e8SplitTailIsometryExtendMatrix_mem
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    ∀ v : Fin 8 → ZMod 2,
      e8SplitQuadraticPolynomial ((e8SplitTailIsometryExtendMatrix Y).mulVec v) =
        e8SplitQuadraticPolynomial v := by
  intro v
  rw [e8SplitQuadraticPolynomial_eq_head_tail,
    e8SplitQuadraticPolynomial_eq_head_tail]
  have h0 : ((e8SplitTailIsometryExtendMatrix Y).mulVec v) 0 = v 0 := by
    simp [e8SplitTailIsometryExtendMatrix, Matrix.mulVec, dotProduct]
  have h1 : ((e8SplitTailIsometryExtendMatrix Y).mulVec v) 1 = v 1 := by
    simp [e8SplitTailIsometryExtendMatrix, Matrix.mulVec, dotProduct]
  rw [h0, h1, e8SplitTailIsometryExtendMatrix_tailCoordinates_mulVec, Y.2]

/-- The extended tail isometry fixes the first split basis vector. -/
theorem e8SplitTailIsometryExtendMatrix_mulVec_firstBasis
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    (e8SplitTailIsometryExtendMatrix Y).mulVec e8SplitFirstBasisVector =
      e8SplitFirstBasisVector := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailIsometryExtendMatrix, e8SplitFirstBasisVector,
      Matrix.mulVec, dotProduct]

/-- The extended tail isometry fixes the second split basis vector. -/
theorem e8SplitTailIsometryExtendMatrix_mulVec_secondBasis
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    (e8SplitTailIsometryExtendMatrix Y).mulVec e8SplitSecondBasisVector =
      e8SplitSecondBasisVector := by
  funext i
  fin_cases i <;>
    simp [e8SplitTailIsometryExtendMatrix, e8SplitSecondBasisVector,
      Matrix.mulVec, dotProduct]

/-- Extend a tail isometry to the fixed hyperbolic-pair stabilizer. -/
def e8SplitTailIsometryToFirstSecondStabilizer
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer := by
  refine ⟨⟨⟨e8SplitTailIsometryExtendMatrix Y,
    e8SplitTailIsometryExtendMatrix_mem Y⟩,
    e8SplitTailIsometryExtendMatrix_mulVec_firstBasis Y⟩, ?_⟩
  apply Subtype.ext
  change (e8SplitTailIsometryExtendMatrix Y).mulVec e8SplitSecondBasisVector =
    e8SplitSecondBasisVector
  exact e8SplitTailIsometryExtendMatrix_mulVec_secondBasis Y

/-- Restricting the identity-on-hyperbolic-plane extension recovers the original
tail isometry. -/
theorem e8SplitFirstSecondStabilizerToTailIsometry_tailExtension
    (Y : e8SplitTailQuadraticIsometryModTwo) :
    e8SplitFirstSecondStabilizerToTailIsometry
        (e8SplitTailIsometryToFirstSecondStabilizer Y) = Y := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8SplitFirstSecondStabilizerToTailIsometry,
      e8SplitFirstSecondStabilizerTailMatrix, e8SplitTailIsometryToFirstSecondStabilizer,
      e8SplitTailIsometryExtendMatrix, e8SplitTailIndex, e8SplitTailIndexInv]

/-- Extending the tail restriction of a fixed-pair stabilizer recovers the
original full split isometry. -/
theorem e8SplitTailIsometryToFirstSecondStabilizer_tailRestriction
    (Y : e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer) :
    e8SplitTailIsometryToFirstSecondStabilizer
        (e8SplitFirstSecondStabilizerToTailIsometry Y) = Y := by
  have hcol0 : ∀ i : Fin 8, Y.1.1.1 i 0 = e8SplitFirstBasisVector i := by
    intro i
    have h := congrFun Y.1.2 i
    simpa [Matrix.mulVec, dotProduct, e8SplitFirstBasisVector, Fin.sum_univ_eight] using h
  have hYsecond : Y.1.1.1.mulVec e8SplitSecondBasisVector = e8SplitSecondBasisVector := by
    have hval := congrArg Subtype.val Y.2
    simpa [e8SplitQuadraticIsometryModTwoFirstVectorStabilizerSecondVectorMap] using hval
  have hcol1 : ∀ i : Fin 8, Y.1.1.1 i 1 = e8SplitSecondBasisVector i := by
    intro i
    have h := congrFun hYsecond i
    simpa [Matrix.mulVec, dotProduct, e8SplitSecondBasisVector, Fin.sum_univ_eight] using h
  have hrow0tail : ∀ k : Fin 6, Y.1.1.1 0 (e8SplitTailIndex k) = 0 := by
    intro k
    have htail :=
      e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
        (v := e8SplitTailVector (Pi.single k (1 : ZMod 2))) rfl rfl
    have h := htail.1
    fin_cases k <;>
      simpa [e8SplitTailVector, e8SplitTailIndex, Matrix.mulVec, dotProduct,
        Fin.sum_univ_eight, Pi.single_apply] using h
  have hrow1tail : ∀ k : Fin 6, Y.1.1.1 1 (e8SplitTailIndex k) = 0 := by
    intro k
    have htail :=
      e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer_mulVec_tail_coordinates_zero Y
        (v := e8SplitTailVector (Pi.single k (1 : ZMod 2))) rfl rfl
    have h := htail.2
    fin_cases k <;>
      simpa [e8SplitTailVector, e8SplitTailIndex, Matrix.mulVec, dotProduct,
        Fin.sum_univ_eight, Pi.single_apply] using h
  have hrow02 : Y.1.1.1 0 2 = 0 := by simpa [e8SplitTailIndex] using hrow0tail 0
  have hrow03 : Y.1.1.1 0 3 = 0 := by simpa [e8SplitTailIndex] using hrow0tail 1
  have hrow04 : Y.1.1.1 0 4 = 0 := by simpa [e8SplitTailIndex] using hrow0tail 2
  have hrow05 : Y.1.1.1 0 5 = 0 := by simpa [e8SplitTailIndex] using hrow0tail 3
  have hrow06 : Y.1.1.1 0 6 = 0 := by simpa [e8SplitTailIndex] using hrow0tail 4
  have hrow07 : Y.1.1.1 0 7 = 0 := by simpa [e8SplitTailIndex] using hrow0tail 5
  have hrow12 : Y.1.1.1 1 2 = 0 := by simpa [e8SplitTailIndex] using hrow1tail 0
  have hrow13 : Y.1.1.1 1 3 = 0 := by simpa [e8SplitTailIndex] using hrow1tail 1
  have hrow14 : Y.1.1.1 1 4 = 0 := by simpa [e8SplitTailIndex] using hrow1tail 2
  have hrow15 : Y.1.1.1 1 5 = 0 := by simpa [e8SplitTailIndex] using hrow1tail 3
  have hrow16 : Y.1.1.1 1 6 = 0 := by simpa [e8SplitTailIndex] using hrow1tail 4
  have hrow17 : Y.1.1.1 1 7 = 0 := by simpa [e8SplitTailIndex] using hrow1tail 5
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e8SplitTailIsometryToFirstSecondStabilizer,
      e8SplitFirstSecondStabilizerToTailIsometry, e8SplitTailIsometryExtendMatrix,
      e8SplitFirstSecondStabilizerTailMatrix, e8SplitTailIndex, e8SplitTailIndexInv,
      e8SplitFirstBasisVector, e8SplitSecondBasisVector, hcol0, hcol1,
      hrow02, hrow03, hrow04, hrow05, hrow06, hrow07, hrow12, hrow13, hrow14,
      hrow15, hrow16, hrow17]

/-- The fixed hyperbolic-pair stabilizer is equivalent to the six-dimensional
tail quadratic-isometry type. -/
noncomputable def e8SplitFirstSecondStabilizerEquivTailIsometry :
    e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer ≃
      e8SplitTailQuadraticIsometryModTwo where
  toFun := e8SplitFirstSecondStabilizerToTailIsometry
  invFun := e8SplitTailIsometryToFirstSecondStabilizer
  left_inv := e8SplitTailIsometryToFirstSecondStabilizer_tailRestriction
  right_inv := e8SplitFirstSecondStabilizerToTailIsometry_tailExtension

/-- The remaining fixed-pair stabilizer order is the order of the six-dimensional
tail isometry type. -/
theorem e8SplitQuadraticIsometryModTwoFirstSecondStabilizer_natCard_eq_tail :
    Nat.card e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer =
      Nat.card e8SplitTailQuadraticIsometryModTwo := by
  exact Nat.card_congr e8SplitFirstSecondStabilizerEquivTailIsometry

/-- A tail-isometry group count of `40320` supplies the remaining pair-stabilizer
count. -/
theorem e8SplitQuadraticIsometryModTwoFirstSecondStabilizer_card_eq_40320_of_tail
    (hcard : Nat.card e8SplitTailQuadraticIsometryModTwo = 40320) :
    Nat.card e8SplitQuadraticIsometryModTwoFirstSecondVectorStabilizer = 40320 := by
  rw [e8SplitQuadraticIsometryModTwoFirstSecondStabilizer_natCard_eq_tail, hcard]

/-- A tail-isometry group count of `40320` supplies the split E8 quadratic-isometry
base count `348364800`. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_348364800_of_tail_card
    (hcard : Nat.card e8SplitTailQuadraticIsometryModTwo = 40320) :
    Nat.card e8SplitQuadraticIsometryModTwo = 348364800 :=
  e8SplitQuadraticIsometryModTwo_natCard_eq_348364800_of_firstSecondStabilizer_card
    (e8SplitQuadraticIsometryModTwoFirstSecondStabilizer_card_eq_40320_of_tail hcard)

/-- The split E8 quadratic-isometry base count is `348364800`. -/
theorem e8SplitQuadraticIsometryModTwo_natCard_eq_348364800 :
    Nat.card e8SplitQuadraticIsometryModTwo = 348364800 :=
  e8SplitQuadraticIsometryModTwo_natCard_eq_348364800_of_tail_card
    e8SplitTailQuadraticIsometryModTwo_natCard_eq_40320

/-- The corrected E8 quadratic-isometry base count transported back from the
split four-hyperbolic-plane model. -/
theorem e8QuadraticIsometryModTwo_natCard_eq_348364800 :
    Nat.card e8QuadraticIsometryModTwo = 348364800 := by
  rw [e8QuadraticIsometryModTwo_natCard_eq_split,
    e8SplitQuadraticIsometryModTwo_natCard_eq_348364800]

/-- The split finite-set presentation of the E8 quadratic-isometry base count. -/
theorem e8SplitQuadraticIsometryModTwoMatrices_card_eq_348364800 :
    e8SplitQuadraticIsometryModTwoMatrices.card = 348364800 := by
  rw [e8SplitQuadraticIsometryModTwoMatrices_card,
    e8SplitQuadraticIsometryModTwo_natCard_eq_348364800]

/-- A matrix over `ZMod 4` preserving the E8 quadratic polynomial modulo four. -/
abbrev e8QuadraticIsometryModFour : Type :=
  {X : Matrix (Fin 8) (Fin 8) (ZMod 4) //
    ∀ v : Fin 8 → ZMod 4,
      e8QuadraticPolynomial (X.mulVec v) = e8QuadraticPolynomial v}

noncomputable instance : Fintype e8QuadraticIsometryModFour := by
  classical
  unfold e8QuadraticIsometryModFour
  infer_instance

/-- Coordinatewise reduction of an E8 quadratic isometry from `ZMod 4` to
`ZMod 2`. -/
def e8QuadraticIsometryModFourToModTwoMatrix
    (X : Matrix (Fin 8) (Fin 8) (ZMod 4)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  X.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2))

/-- Reducing a `ZMod 4` E8 quadratic isometry gives a `ZMod 2` E8 quadratic
isometry. -/
theorem e8QuadraticIsometryModFourToModTwo_mem
    (X : e8QuadraticIsometryModFour) :
    ∀ v : Fin 8 → ZMod 2,
      e8QuadraticPolynomial
          ((e8QuadraticIsometryModFourToModTwoMatrix X.1).mulVec v) =
        e8QuadraticPolynomial v := by
  intro v
  let f : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
  let w : Fin 8 → ZMod 4 := fun i => (v i).val
  have hw : (fun i : Fin 8 => f (w i)) = v := by
    funext i
    dsimp [w, f]
    rw [ZMod.cast_natCast (by norm_num : 2 ∣ 4)]
    exact ZMod.natCast_zmod_val (v i)
  have hmul :
      (e8QuadraticIsometryModFourToModTwoMatrix X.1).mulVec v =
        fun i : Fin 8 => f ((X.1.mulVec w) i) := by
    calc
      (e8QuadraticIsometryModFourToModTwoMatrix X.1).mulVec v =
          (e8QuadraticIsometryModFourToModTwoMatrix X.1).mulVec (fun j => f (w j)) := by
            rw [hw]
      _ = fun i : Fin 8 => f ((X.1.mulVec w) i) := by
            ext i
            exact (RingHom.map_mulVec f X.1 w i).symm
  calc
    e8QuadraticPolynomial
        ((e8QuadraticIsometryModFourToModTwoMatrix X.1).mulVec v)
        = e8QuadraticPolynomial (fun i : Fin 8 => f ((X.1.mulVec w) i)) := by
          rw [hmul]
    _ = f (e8QuadraticPolynomial (X.1.mulVec w)) := by
          rw [map_e8QuadraticPolynomial]
    _ = f (e8QuadraticPolynomial w) := by
          rw [X.2 w]
    _ = e8QuadraticPolynomial v := by
          rw [map_e8QuadraticPolynomial, hw]

/-- The subtype map induced by reducing a `ZMod 4` E8 quadratic isometry modulo
`2`. -/
def e8QuadraticIsometryModFourToModTwo
    (X : e8QuadraticIsometryModFour) : e8QuadraticIsometryModTwo :=
  ⟨e8QuadraticIsometryModFourToModTwoMatrix X.1,
    e8QuadraticIsometryModFourToModTwo_mem X⟩

/-- The corrected E8 finite-field target as a filtered finite set. -/
noncomputable def e8QuadraticIsometryModTwoMatrices :
    Finset (Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  classical
  exact Finset.univ.filter fun Y =>
    ∀ v : Fin 8 → ZMod 2,
      e8QuadraticPolynomial (Y.mulVec v) = e8QuadraticPolynomial v

/-- Membership in the corrected E8 mod-two quadratic-isometry target. -/
theorem mem_e8QuadraticIsometryModTwoMatrices_iff
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Y ∈ e8QuadraticIsometryModTwoMatrices ↔
      ∀ v : Fin 8 → ZMod 2,
        e8QuadraticPolynomial (Y.mulVec v) = e8QuadraticPolynomial v := by
  simp [e8QuadraticIsometryModTwoMatrices]

/-- The finite-set and subtype presentations of the corrected E8 mod-two
quadratic-isometry target have the same cardinality. -/
theorem e8QuadraticIsometryModTwoMatrices_card :
    e8QuadraticIsometryModTwoMatrices.card = Nat.card e8QuadraticIsometryModTwo := by
  classical
  rw [Nat.card_eq_fintype_card]
  change e8QuadraticIsometryModTwoMatrices.card =
    Fintype.card {Y : Matrix (Fin 8) (Fin 8) (ZMod 2) //
      ∀ v : Fin 8 → ZMod 2,
        e8QuadraticPolynomial (Y.mulVec v) = e8QuadraticPolynomial v}
  rw [e8QuadraticIsometryModTwoMatrices]
  exact (Fintype.card_subtype (fun Y : Matrix (Fin 8) (Fin 8) (ZMod 2) =>
    ∀ v : Fin 8 → ZMod 2,
      e8QuadraticPolynomial (Y.mulVec v) = e8QuadraticPolynomial v)).symm

/-- The corrected E8 finite-set presentation of the quadratic-isometry base
count. -/
theorem e8QuadraticIsometryModTwoMatrices_card_eq_348364800 :
    e8QuadraticIsometryModTwoMatrices.card = 348364800 := by
  rw [e8QuadraticIsometryModTwoMatrices_card,
    e8QuadraticIsometryModTwo_natCard_eq_348364800]

/-- For the concrete E8 seed, the native dyadic Schulze--Pillot local factor is
just the depth-three associated-bilinear quotient count divided by `2^49`.
This is the count-normalization interface for the later finite enumeration; it
is not an evaluation of the count. -/
theorem e8Lattice_massLocalFactor_two_eq_associatedBilinearDualQuotientCount_div :
    e8Lattice.massLocalFactor 2 =
      ((associatedBilinearDualQuotientCount e8Lattice 2 3 : ℚ) : ℝ) /
        (2 : ℝ) ^ 49 := by
  have hfactor : gramDetPadicValuationFactor 2 8 8 = (2 : ℝ) ^ 28 := by
    unfold gramDetPadicValuationFactor
    norm_num
  rw [massLocalFactor_two_eq_associatedBilinearDualQuotientCount_three_valuationFactor_of_isUnimodular
    e8Lattice_isUnimodular, hfactor]
  norm_num
  ring


/-- For the concrete E8 seed, the remaining depth-three associated-bilinear
count is the explicit mod-`4` coordinate quotient count. -/
theorem e8Lattice_associatedBilinearDualQuotientCount_eq_primePowCoordinateSubmodule :
    associatedBilinearDualQuotientCount e8Lattice 2 3 =
      coordinateLocalDualQuotientCount e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2) := by
  exact associatedBilinearDualQuotientCount_two_three_eq_primePowCoordinateSubmodule
    (n := 8) (L := e8Lattice) e8Lattice_isUnimodular

/-- If the finite quotient count for the concrete E8 seed has the
expected value, then the dyadic Schulze--Pillot local factor is the
proposed `42525/256`.  The count hypothesis is a local finite count; it is not a
consequence of the global mass formula. -/
theorem e8Lattice_massLocalFactor_two_eq_of_associatedBilinearDualQuotientCount
    (hcount : associatedBilinearDualQuotientCount e8Lattice 2 3 = 42525 * 2 ^ 41) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  rw [e8Lattice_massLocalFactor_two_eq_associatedBilinearDualQuotientCount_div,
    hcount]
  norm_num


/-- The explicit finite coordinate solution-family type for the E8 depth-three
dyadic count.  Its quotient denominator is the concrete mod-`4` coordinate
submodule `2^2 ℤ^8`. -/
abbrev e8LatticeDepthThreeCoordinateSolutionFamily :=
  {Y : Fin 8 → localDualQuotientTarget
      (primePowCoordinateSubmodule (n := 8) 2 2) //
    Y ∈ localDualQuotientSolutionFamilies e8Lattice 2 3
      (primePowCoordinateSubmodule (n := 8) 2 2)
      (primePowCoordinateSubmodule_rank (n := 8) 2 2)}

/-- The matrix form of the E8 depth-three coordinate solution target.  This
is the same finite problem as `e8LatticeDepthThreeCoordinateSolutionFamily`,
but with the chosen quotient basis images represented by a matrix over
`ZMod 4`. -/
abbrev e8LatticeDepthThreeCoordinateSolutionMatrix :=
  {X : Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 2 : ℕ)) //
    localDualQuotientLiftFamily (n := 8) 2 2 X ∈
      localDualQuotientSolutionFamilies e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2)}

instance : Fintype e8LatticeDepthThreeCoordinateSolutionMatrix := by
  classical
  unfold e8LatticeDepthThreeCoordinateSolutionMatrix
  infer_instance

/-- The finite set of `ZMod 4` matrices representing the E8 depth-three
coordinate solution target. -/
noncomputable def e8LatticeDepthThreeCoordinateSolutionMatrices :
    Finset (Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 2 : ℕ))) := by
  classical
  exact Finset.univ.filter fun X =>
    localDualQuotientLiftFamily (n := 8) 2 2 X ∈
      localDualQuotientSolutionFamilies e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2)

/-- Membership in the named E8 `ZMod 4` matrix target is membership in the
corresponding filtered finite set. -/
theorem mem_e8LatticeDepthThreeCoordinateSolutionMatrices_iff
    (X : Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 2 : ℕ))) :
    X ∈ e8LatticeDepthThreeCoordinateSolutionMatrices ↔
      localDualQuotientLiftFamily (n := 8) 2 2 X ∈
        localDualQuotientSolutionFamilies e8Lattice 2 3
          (primePowCoordinateSubmodule (n := 8) 2 2)
          (primePowCoordinateSubmodule_rank (n := 8) 2 2) := by
  simp [e8LatticeDepthThreeCoordinateSolutionMatrices]

/-- The filtered finite set and the subtype presentation of the E8 `ZMod 4`
matrix target have the same cardinality. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrices_card :
    e8LatticeDepthThreeCoordinateSolutionMatrices.card =
      Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix := by
  classical
  rw [Nat.card_eq_fintype_card]
  change e8LatticeDepthThreeCoordinateSolutionMatrices.card =
    Fintype.card {X : Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 2 : ℕ)) //
      localDualQuotientLiftFamily (n := 8) 2 2 X ∈
        localDualQuotientSolutionFamilies e8Lattice 2 3
          (primePowCoordinateSubmodule (n := 8) 2 2)
          (primePowCoordinateSubmodule_rank (n := 8) 2 2)}
  rw [e8LatticeDepthThreeCoordinateSolutionMatrices]
  exact (Fintype.card_subtype (fun X : Matrix (Fin 8) (Fin 8)
    (ZMod (primePowModulus 2 2 : ℕ)) =>
      localDualQuotientLiftFamily (n := 8) 2 2 X ∈
        localDualQuotientSolutionFamilies e8Lattice 2 3
          (primePowCoordinateSubmodule (n := 8) 2 2)
          (primePowCoordinateSubmodule_rank (n := 8) 2 2))).symm

/-- The quotient-family and `ZMod 4` matrix presentations of the E8 depth-three
coordinate target are equivalent. -/
noncomputable def e8LatticeDepthThreeCoordinateSolutionMatrixEquiv :
    e8LatticeDepthThreeCoordinateSolutionMatrix ≃
      e8LatticeDepthThreeCoordinateSolutionFamily where
  toFun X := ⟨localDualQuotientLiftFamily (n := 8) 2 2 X.1, X.2⟩
  invFun Y :=
    ⟨localDualQuotientFamilyMatrix (n := 8) 2 2 Y.1, by
      rw [localDualQuotientLiftFamily_familyMatrix]
      simp⟩
  left_inv X := by
    apply Subtype.ext
    exact localDualQuotientFamilyMatrix_liftFamily (n := 8) 2 2 X.1
  right_inv Y := by
    apply Subtype.ext
    exact localDualQuotientLiftFamily_familyMatrix (n := 8) 2 2 Y.1

/-- The named E8 `ZMod 4` matrix target has the same cardinality as the named
quotient-family target. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrix_natCard :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix =
      Nat.card e8LatticeDepthThreeCoordinateSolutionFamily := by
  exact Nat.card_congr e8LatticeDepthThreeCoordinateSolutionMatrixEquiv

/-- The E8 coordinate quotient count is the cardinality of the named finite
solution-family type. -/
theorem e8Lattice_depthThreeCoordinateSolutionFamily_natCard :
    Nat.card e8LatticeDepthThreeCoordinateSolutionFamily =
      coordinateLocalDualQuotientCount e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2) := by
  unfold e8LatticeDepthThreeCoordinateSolutionFamily coordinateLocalDualQuotientCount
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The named E8 `ZMod 4` matrix target is another exact presentation of the
coordinate quotient count. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrix_natCard_eq_coordinateLocalDualQuotientCount :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix =
      coordinateLocalDualQuotientCount e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2) := by
  rw [e8Lattice_depthThreeCoordinateSolutionMatrix_natCard,
    e8Lattice_depthThreeCoordinateSolutionFamily_natCard]

/-- If the explicit mod-`4` coordinate quotient count for E8 has the expected
value, then the native dyadic Schulze--Pillot local factor is `42525/256`. -/
theorem e8Lattice_massLocalFactor_two_eq_of_primePowCoordinateSubmoduleCount
    (hcount : coordinateLocalDualQuotientCount e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2) = 42525 * 2 ^ 41) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_associatedBilinearDualQuotientCount
    (by
      rw [e8Lattice_associatedBilinearDualQuotientCount_eq_primePowCoordinateSubmodule]
      exact hcount)

/-- If the named finite E8 coordinate solution-family type has the expected
cardinality, then the native dyadic Schulze--Pillot local factor is
`42525/256`. -/
theorem e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionFamily_natCard
    (hcount : Nat.card e8LatticeDepthThreeCoordinateSolutionFamily = 42525 * 2 ^ 41) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_primePowCoordinateSubmoduleCount
    (by
      rw [← e8Lattice_depthThreeCoordinateSolutionFamily_natCard]
      exact hcount)

set_option backward.isDefEq.respectTransparency false in
/-- A depth-three E8 `ZMod 4` matrix solution preserves the corrected
quadratic polynomial `Q_E8` modulo `4`.  The quotient condition preserves the
stored form `q_E8 = 2 * Q_E8` modulo `8`, and the final step cancels that
visible factor of `2` down to a mod-`4` statement. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrix_to_e8QuadraticIsometryModFour_mem
    (X : e8LatticeDepthThreeCoordinateSolutionMatrix) :
    ∀ v : Fin 8 → ZMod 4,
      e8QuadraticPolynomial (X.1.mulVec v) = e8QuadraticPolynomial v := by
  intro v
  let x : Fin 8 → ℤ := fun i => (v i).val
  let D : Submodule ℤ (Fin 8 → ℤ) := primePowCoordinateSubmodule (n := 8) 2 2
  let Y : Fin 8 → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := 8) 2 2 X.1
  let q : localDualQuotientTarget D := quotientBasisFamilyMap D Y x
  let y : Fin 8 → ℤ := Quotient.out q
  have hq : quotientBasisFamilyMap D Y x = D.mkQ y := by
    change q = D.mkQ y
    exact (Submodule.Quotient.mk_out q).symm
  have hquad :
      (e8Lattice.quadForm y : ZMod (primePowModulus 2 3 : ℕ)) =
        (e8Lattice.quadForm x : ZMod (primePowModulus 2 3 : ℕ)) := by
    exact (mem_localDualQuotientSolutionFamilies_iff.mp X.2) x y hq
  have hxv : (fun i : Fin 8 => (x i : ZMod 4)) = v := by
    funext i
    dsimp [x]
    exact ZMod.natCast_zmod_val (v i)
  have hvec :
      (fun i : Fin 8 => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
        X.1.mulVec v := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := 8) 2 2 Y x
    have hqcoord :
        primePowQuotientVector (n := 8) 2 2
            (quotientBasisFamilyMap D Y x) =
          fun i : Fin 8 => (y i : ZMod (primePowModulus 2 2 : ℕ)) := by
      rw [hq]
      exact primePowQuotientVector_mkQ (n := 8) 2 2 y
    have hm : localDualQuotientFamilyMatrix (n := 8) 2 2 Y = X.1 := by
      exact localDualQuotientFamilyMatrix_liftFamily (n := 8) 2 2 X.1
    calc
      (fun i : Fin 8 => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
          (localDualQuotientFamilyMatrix (n := 8) 2 2 Y).mulVec
            (fun j : Fin 8 => (x j : ZMod (primePowModulus 2 2 : ℕ))) := by
            exact (hmat.trans hqcoord).symm
      _ = X.1.mulVec v := by
            rw [hm]
            change X.1.mulVec (fun j : Fin 8 => (x j : ZMod 4)) = X.1.mulVec v
            rw [hxv]
  have hquadQ :
      ((2 * e8QuadraticPolynomial y : ℤ) : ZMod 8) =
        ((2 * e8QuadraticPolynomial x : ℤ) : ZMod 8) := by
    simpa [primePowModulus, e8Lattice_quadForm_eq_two_mul_e8QuadraticPolynomial] using hquad
  have hQint :
      ((e8QuadraticPolynomial y : ℤ) : ZMod 4) =
        ((e8QuadraticPolynomial x : ℤ) : ZMod 4) :=
    zmod_four_intCast_eq_of_two_mul_eq_zmod_eight _ _ hquadQ
  have hyQ : e8QuadraticPolynomial (X.1.mulVec v) =
      ((e8QuadraticPolynomial y : ℤ) : ZMod 4) := by
    rw [← hvec]
    exact (map_e8QuadraticPolynomial (Int.castRingHom (ZMod 4)) y).symm
  have hxQ : e8QuadraticPolynomial v =
      ((e8QuadraticPolynomial x : ℤ) : ZMod 4) := by
    rw [← hxv]
    exact (map_e8QuadraticPolynomial (Int.castRingHom (ZMod 4)) x).symm
  rw [hyQ, hxQ]
  exact hQint

/-- The depth-three E8 matrix-solution subtype maps into the corrected
`ZMod 4` quadratic-isometry target. -/
def e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour
    (X : e8LatticeDepthThreeCoordinateSolutionMatrix) : e8QuadraticIsometryModFour :=
  ⟨X.1, e8LatticeDepthThreeCoordinateSolutionMatrix_to_e8QuadraticIsometryModFour_mem X⟩

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, a `ZMod 4` matrix preserving `Q_E8` is a depth-three E8
coordinate solution.  The quotient condition asks for preservation of
`q_E8 = 2 * Q_E8` modulo `8`; the `ZMod 4` equality for `Q_E8` supplies this
after multiplying by the visible factor `2`. -/
theorem e8QuadraticIsometryModFour_to_e8LatticeDepthThreeCoordinateSolutionMatrix_mem
    (X : e8QuadraticIsometryModFour) :
    localDualQuotientLiftFamily (n := 8) 2 2 X.1 ∈
      localDualQuotientSolutionFamilies e8Lattice 2 3
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let D : Submodule ℤ (Fin 8 → ℤ) := primePowCoordinateSubmodule (n := 8) 2 2
  let Y : Fin 8 → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := 8) 2 2 X.1
  have hvec :
      (fun i : Fin 8 => (y i : ZMod 4)) =
        X.1.mulVec (fun j : Fin 8 => (x j : ZMod 4)) := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := 8) 2 2 Y x
    have hq := congrArg (primePowQuotientVector (n := 8) 2 2) hxy
    have hm : localDualQuotientFamilyMatrix (n := 8) 2 2 Y = X.1 := by
      exact localDualQuotientFamilyMatrix_liftFamily (n := 8) 2 2 X.1
    calc
      (fun i : Fin 8 => (y i : ZMod 4)) =
          primePowQuotientVector (n := 8) 2 2 (D.mkQ y) := by
            exact (primePowQuotientVector_mkQ (n := 8) 2 2 y).symm
      _ = primePowQuotientVector (n := 8) 2 2
            (quotientBasisFamilyMap D Y x) := by
            exact hq.symm
      _ = (localDualQuotientFamilyMatrix (n := 8) 2 2 Y).mulVec
            (fun j : Fin 8 => (x j : ZMod 4)) := by
            exact hmat.symm
      _ = X.1.mulVec (fun j : Fin 8 => (x j : ZMod 4)) := by
            rw [hm]
  have hQmod4 :
      ((e8QuadraticPolynomial y : ℤ) : ZMod 4) =
        ((e8QuadraticPolynomial x : ℤ) : ZMod 4) := by
    have hyQ : e8QuadraticPolynomial (fun i : Fin 8 => (y i : ZMod 4)) =
        ((e8QuadraticPolynomial y : ℤ) : ZMod 4) := by
      exact (map_e8QuadraticPolynomial (Int.castRingHom (ZMod 4)) y).symm
    have hxQ : e8QuadraticPolynomial (fun i : Fin 8 => (x i : ZMod 4)) =
        ((e8QuadraticPolynomial x : ℤ) : ZMod 4) := by
      exact (map_e8QuadraticPolynomial (Int.castRingHom (ZMod 4)) x).symm
    calc
      ((e8QuadraticPolynomial y : ℤ) : ZMod 4) =
          e8QuadraticPolynomial (fun i : Fin 8 => (y i : ZMod 4)) := hyQ.symm
      _ = e8QuadraticPolynomial (X.1.mulVec (fun j : Fin 8 => (x j : ZMod 4))) := by
            rw [hvec]
      _ = e8QuadraticPolynomial (fun j : Fin 8 => (x j : ZMod 4)) := X.2 _
      _ = ((e8QuadraticPolynomial x : ℤ) : ZMod 4) := hxQ
  have hquadQ :
      ((2 * e8QuadraticPolynomial y : ℤ) : ZMod 8) =
        ((2 * e8QuadraticPolynomial x : ℤ) : ZMod 8) :=
    two_mul_eq_zmod_eight_of_zmod_four_intCast_eq _ _ hQmod4
  simpa [primePowModulus, e8Lattice_quadForm_eq_two_mul_e8QuadraticPolynomial] using hquadQ

/-- The corrected `ZMod 4` quadratic-isometry target maps back to the
depth-three E8 matrix-solution subtype. -/
def e8QuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix
    (X : e8QuadraticIsometryModFour) : e8LatticeDepthThreeCoordinateSolutionMatrix :=
  ⟨X.1, e8QuadraticIsometryModFour_to_e8LatticeDepthThreeCoordinateSolutionMatrix_mem X⟩

/-- The depth-three E8 matrix target is exactly the corrected `ZMod 4`
quadratic-isometry target. -/
def e8LatticeDepthThreeCoordinateSolutionMatrixEquivQuadraticIsometryModFour :
    e8LatticeDepthThreeCoordinateSolutionMatrix ≃ e8QuadraticIsometryModFour where
  toFun := e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour
  invFun := e8QuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    rfl

/-- The depth-three E8 matrix target has the same cardinality as the corrected
`ZMod 4` quadratic-isometry target. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrix_natCard_eq_quadraticIsometryModFour :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix = Nat.card e8QuadraticIsometryModFour :=
  Nat.card_congr e8LatticeDepthThreeCoordinateSolutionMatrixEquivQuadraticIsometryModFour

/-- Composing the depth-three E8 solution-to-`ZMod 4` quadratic-isometry map
with reduction gives a corrected `ZMod 2` quadratic isometry. -/
def e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModTwo
    (X : e8LatticeDepthThreeCoordinateSolutionMatrix) : e8QuadraticIsometryModTwo :=
  e8QuadraticIsometryModFourToModTwo
    (e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour X)
/-- If the named E8 `ZMod 4` matrix target has the expected cardinality,
then the native dyadic Schulze--Pillot local factor is `42525/256`. -/
theorem e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionMatrix_natCard
    (hcount : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix = 42525 * 2 ^ 41) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionFamily_natCard
    (by
      rw [← e8Lattice_depthThreeCoordinateSolutionMatrix_natCard]
      exact hcount)

/-- If the filtered finite set of E8 `ZMod 4` matrix solutions has the
expected cardinality, then the native dyadic Schulze--Pillot local factor is
`42525/256`. -/
theorem e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionMatrices_card
    (hcount : e8LatticeDepthThreeCoordinateSolutionMatrices.card = 42525 * 2 ^ 41) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionMatrix_natCard
    (by
      rw [← e8Lattice_depthThreeCoordinateSolutionMatrices_card]
      exact hcount)

/-- The proposed E8 finite count factors numerically as the expected mod-`2`
base count `348364800` times a depth-one lift factor `2^28`.  This is only an
arithmetic bridge for the remaining finite enumeration target. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrices_expected_card_factorization :
    348364800 * 2 ^ 28 = 42525 * 2 ^ 41 := by
  norm_num

/-- Coordinatewise reduction of E8 depth-three solution matrices from `ZMod 4`
to `ZMod 2`. -/
def e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo
    (X : Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 2 : ℕ))) :
    Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  X.map (ZMod.castHom
    (show 2 ∣ (primePowModulus 2 2 : ℕ) by
      norm_num [primePowModulus])
    (ZMod 2))


/-- The corrected mod-`2` quadratic-isometry map has the same underlying matrix
as the existing coordinatewise mod-`2` reduction of the depth-three solution. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModTwo_coe
    (X : e8LatticeDepthThreeCoordinateSolutionMatrix) :
    (e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModTwo X).1 =
      e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo X.1 := by
  rfl

/-- The mod-`2` image of the E8 `ZMod 4` matrix-solution subtype.  This names
the base finite type for the later mod-`2` count. -/
abbrev e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage :=
  {Y : Matrix (Fin 8) (Fin 8) (ZMod 2) //
    ∃ X : e8LatticeDepthThreeCoordinateSolutionMatrix,
      e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo X.1 = Y}

instance : Fintype e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage := by
  classical
  unfold e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage
  infer_instance

/-- The reduction map from the E8 mod-`4` matrix solution subtype to its named
mod-`2` image. -/
noncomputable def e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo :
    e8LatticeDepthThreeCoordinateSolutionMatrix →
      e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage := fun X =>
  ⟨e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo X.1, ⟨X, rfl⟩⟩

/-- The mod-`2` image of the corrected E8 `ZMod 4` quadratic-isometry subtype.
This is the same base image as the depth-three matrix-solution image, after the
proved identification of the depth-three target with `e8QuadraticIsometryModFour`. -/
abbrev e8QuadraticIsometryModFourReductionModTwoImage :=
  {Y : Matrix (Fin 8) (Fin 8) (ZMod 2) //
    ∃ X : e8QuadraticIsometryModFour,
      e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y}

instance : Fintype e8QuadraticIsometryModFourReductionModTwoImage := by
  classical
  unfold e8QuadraticIsometryModFourReductionModTwoImage
  infer_instance

/-- The reduction map from corrected E8 `ZMod 4` quadratic isometries to their
named mod-`2` image. -/
noncomputable def e8QuadraticIsometryModFourReductionModTwo :
    e8QuadraticIsometryModFour → e8QuadraticIsometryModFourReductionModTwoImage := fun X =>
  ⟨e8QuadraticIsometryModFourToModTwoMatrix X.1, ⟨X, rfl⟩⟩

/-- The depth-three mod-`2` image is the same finite type as the image of the
corrected `ZMod 4` quadratic-isometry reduction. -/
noncomputable def
    e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage :
    e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage ≃
      e8QuadraticIsometryModFourReductionModTwoImage where
  toFun Y :=
    ⟨Y.1, by
      rcases Y.2 with ⟨X, hX⟩
      refine ⟨e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour X, ?_⟩
      simpa [e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour,
        e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo,
        e8QuadraticIsometryModFourToModTwoMatrix, primePowModulus] using hX⟩
  invFun Y :=
    ⟨Y.1, by
      rcases Y.2 with ⟨X, hX⟩
      refine ⟨e8QuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix X, ?_⟩
      simpa [e8QuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix,
        e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo,
        e8QuadraticIsometryModFourToModTwoMatrix, primePowModulus] using hX⟩
  left_inv Y := by
    apply Subtype.ext
    rfl
  right_inv Y := by
    apply Subtype.ext
    rfl

/-- Cardinality form of the equivalence between the old depth-three image and
the corrected `ZMod 4` quadratic-isometry reduction image. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage_natCard_eq_quadraticIsometryModFourReductionModTwoImage :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      Nat.card e8QuadraticIsometryModFourReductionModTwoImage :=
  Nat.card_congr
    e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage

/-- The corrected `ZMod 4` quadratic-isometry reduction image maps into the
corrected mod-`2` quadratic-isometry target. -/
noncomputable def e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry
    (Y : e8QuadraticIsometryModFourReductionModTwoImage) :
    e8QuadraticIsometryModTwo :=
  ⟨Y.1, by
    rcases Y.2 with ⟨X, hX⟩
    simpa [← hX] using (e8QuadraticIsometryModFourToModTwo X).2⟩

/-- The map from the corrected `ZMod 4` reduction image into the mod-`2`
quadratic-isometry target keeps the same underlying matrix. -/
theorem e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry_coe
    (Y : e8QuadraticIsometryModFourReductionModTwoImage) :
    (e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry Y).1 = Y.1 := by
  rfl

/-- The corrected `ZMod 4` reduction image embeds into the mod-`2`
quadratic-isometry target. -/
theorem e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry_injective :
    Function.Injective
      e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry := by
  intro Y Z h
  apply Subtype.ext
  exact congrArg (fun T : e8QuadraticIsometryModTwo => T.1) h

/-- Matrix-lift surjectivity for the corrected `ZMod 4 → ZMod 2`
quadratic-isometry reduction implies surjectivity of the image inclusion into
the corrected mod-`2` quadratic-isometry target. -/
theorem e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry_surjective_of_lift
    (hlift : ∀ Y : e8QuadraticIsometryModTwo,
      ∃ X : e8QuadraticIsometryModFour,
        e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y.1) :
    Function.Surjective e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry := by
  intro Y
  obtain ⟨X, hX⟩ := hlift Y
  refine ⟨⟨Y.1, ⟨X, hX⟩⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- A direct lift for every corrected mod-`2` quadratic isometry gives the
remaining image-cardinality equality.  This is the surjectivity form of the E8
image comparison. -/
theorem e8QuadraticIsometryModFourReductionModTwoImage_natCard_eq_quadraticIsometry_of_lift
    (hlift : ∀ Y : e8QuadraticIsometryModTwo,
      ∃ X : e8QuadraticIsometryModFour,
        e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y.1) :
    Nat.card e8QuadraticIsometryModFourReductionModTwoImage =
      Nat.card e8QuadraticIsometryModTwo :=
  Nat.card_congr (Equiv.ofBijective
    e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry
    ⟨e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry_injective,
      e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry_surjective_of_lift hlift⟩)

/-- The canonical `0/1` representative of an element of `ZMod 2` inside
`ZMod 4`.  This is not a ring homomorphism; it is only the chosen coordinate
lift used to state the remaining E8 mod-`4` lifting problem. -/
def zmodTwoLiftToFour (a : ZMod 2) : ZMod 4 :=
  (a.val : ZMod 4)

/-- The chosen `0/1` lift from a mod-`2` matrix to a mod-`4` matrix. -/
def e8MatrixModTwoLiftToModFour
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 4) :=
  fun i j => zmodTwoLiftToFour (Y i j)

/-- A first-order `2A` correction, with `A` recorded over `ZMod 2`. -/
def e8MatrixModTwoCorrectionToModFour
    (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 4) :=
  fun i j => (2 : ZMod 4) * zmodTwoLiftToFour (A i j)

/-- The concrete shape of the remaining E8 mod-`4` lift problem: a chosen
`0/1` lift plus a `2A` correction. -/
def e8MatrixModFourCorrectedLift
    (Y A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 4) :=
  e8MatrixModTwoLiftToModFour Y + e8MatrixModTwoCorrectionToModFour A

/-- The chosen `0/1` lift reduces to the original mod-`2` scalar. -/
theorem zmodTwoLiftToFour_to_modTwo (a : ZMod 2) :
    ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (zmodTwoLiftToFour a) = a := by
  dsimp [zmodTwoLiftToFour]
  rw [ZMod.cast_natCast (by norm_num : 2 ∣ 4)]
  exact ZMod.natCast_zmod_val a

/-- A `2A` first-order correction vanishes after reduction modulo `2`. -/
theorem e8MatrixModTwoCorrectionToModFour_to_modTwo
    (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8QuadraticIsometryModFourToModTwoMatrix (e8MatrixModTwoCorrectionToModFour A) = 0 := by
  ext i j
  dsimp [e8QuadraticIsometryModFourToModTwoMatrix, e8MatrixModTwoCorrectionToModFour]
  exact (by decide :
    ∀ a : ZMod 2, ((2 : ZMod 4) * zmodTwoLiftToFour a).cast = (0 : ZMod 2)) (A i j)

private theorem two_mul_zmodTwoLiftToFour_add (a b : ZMod 2) :
    (2 : ZMod 4) * zmodTwoLiftToFour (a + b) =
      (2 : ZMod 4) * zmodTwoLiftToFour a +
        (2 : ZMod 4) * zmodTwoLiftToFour b := by
  exact (by decide : ∀ a b : ZMod 2,
    (2 : ZMod 4) * zmodTwoLiftToFour (a + b) =
      (2 : ZMod 4) * zmodTwoLiftToFour a +
        (2 : ZMod 4) * zmodTwoLiftToFour b) a b

private theorem two_mul_zmodTwoLiftToFour_mul_cast (a : ZMod 2) (x : ZMod 4) :
    (2 : ZMod 4) * zmodTwoLiftToFour (a * (x.cast : ZMod 2)) =
      ((2 : ZMod 4) * zmodTwoLiftToFour a) * x := by
  exact (by decide : ∀ (a : ZMod 2) (x : ZMod 4),
    (2 : ZMod 4) * zmodTwoLiftToFour (a * (x.cast : ZMod 2)) =
      ((2 : ZMod 4) * zmodTwoLiftToFour a) * x) a x

/-- Multiplication by `2` makes the chosen `0/1` lift additive. -/
theorem zmodTwoLiftToFour_add_mul_two (a b : ZMod 2) :
    zmodTwoLiftToFour (a + b) * (2 : ZMod 4) =
      zmodTwoLiftToFour a * (2 : ZMod 4) + zmodTwoLiftToFour b * (2 : ZMod 4) := by
  exact (by decide : ∀ a b : ZMod 2,
    zmodTwoLiftToFour (a + b) * (2 : ZMod 4) =
      zmodTwoLiftToFour a * (2 : ZMod 4) + zmodTwoLiftToFour b * (2 : ZMod 4)) a b

/-- Doubled chosen lifts in `ZMod 4` are fixed by negation. -/
theorem neg_zmodTwoLiftToFour_mul_two (a : ZMod 2) :
    -(zmodTwoLiftToFour a * (2 : ZMod 4)) = zmodTwoLiftToFour a * (2 : ZMod 4) := by
  exact (by decide : ∀ a : ZMod 2,
    -(zmodTwoLiftToFour a * (2 : ZMod 4)) = zmodTwoLiftToFour a * (2 : ZMod 4)) a

/-- Adding a doubled mod-`2` lift does not change a square in `ZMod 4`. -/
theorem zmodFour_sq_add_two_zmodTwoLiftToFour (x : ZMod 4) (a : ZMod 2) :
    (x + (2 : ZMod 4) * zmodTwoLiftToFour a) ^ 2 = x ^ 2 := by
  exact (by decide : ∀ (x : ZMod 4) (a : ZMod 2),
    (x + (2 : ZMod 4) * zmodTwoLiftToFour a) ^ 2 = x ^ 2) x a

/-- First-order product expansion for doubled mod-`2` lifts in `ZMod 4`. -/
theorem zmodFour_mul_add_two_zmodTwoLiftToFour (x y : ZMod 4) (a b : ZMod 2) :
    (x + (2 : ZMod 4) * zmodTwoLiftToFour a) *
        (y + (2 : ZMod 4) * zmodTwoLiftToFour b) =
      x * y + zmodTwoLiftToFour ((x.cast : ZMod 2) * b + a * (y.cast : ZMod 2)) *
        (2 : ZMod 4) := by
  exact (by decide : ∀ (x y : ZMod 4) (a b : ZMod 2),
    (x + (2 : ZMod 4) * zmodTwoLiftToFour a) *
        (y + (2 : ZMod 4) * zmodTwoLiftToFour b) =
      x * y + zmodTwoLiftToFour ((x.cast : ZMod 2) * b + a * (y.cast : ZMod 2)) *
        (2 : ZMod 4)) x y a b

set_option maxHeartbeats 2000000 in
/-- The first-order correction matrix acts only on the mod-two reduction of the
input vector.  This is the finite-level linearization used in the remaining
E8 mod-`4` fiber count. -/
theorem e8MatrixModTwoCorrectionToModFour_mulVec
    (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : Fin 8 → ZMod 4) :
    (e8MatrixModTwoCorrectionToModFour A).mulVec v =
      fun i : Fin 8 => (2 : ZMod 4) * zmodTwoLiftToFour
        (A.mulVec (fun j : Fin 8 => (v j).cast) i) := by
  ext i
  fin_cases i <;>
    simp [e8MatrixModTwoCorrectionToModFour, Matrix.mulVec, dotProduct, Fin.sum_univ_eight,
      two_mul_zmodTwoLiftToFour_add, two_mul_zmodTwoLiftToFour_mul_cast]

/-- The chosen `0/1` lift of the identity matrix acts as the identity on
`ZMod 4` vectors. -/
theorem e8MatrixModTwoLiftToModFour_one_mulVec (v : Fin 8 → ZMod 4) :
    (e8MatrixModTwoLiftToModFour (1 : Matrix (Fin 8) (Fin 8) (ZMod 2))).mulVec v = v := by
  ext i
  fin_cases i <;>
    simp [e8MatrixModTwoLiftToModFour, zmodTwoLiftToFour, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Fin.sum_univ_eight] <;>
    exact (by decide : ∀ x : ZMod 4, (ZMod.cast (1 : ZMod 2) : ZMod 4) * x = x) _

/-- For the identity mod-`2` isometry, a corrected lift sends `v` to
`v + 2A(v mod 2)`. -/
theorem e8MatrixModFourCorrectedLift_one_mulVec
    (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : Fin 8 → ZMod 4) :
    (e8MatrixModFourCorrectedLift (1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) A).mulVec v =
      fun i : Fin 8 => v i + (2 : ZMod 4) * zmodTwoLiftToFour
        (A.mulVec (fun j : Fin 8 => (v j).cast) i) := by
  rw [e8MatrixModFourCorrectedLift, Matrix.add_mulVec,
    e8MatrixModTwoLiftToModFour_one_mulVec, e8MatrixModTwoCorrectionToModFour_mulVec]
  rfl

/-- A corrected `0/1` lift always reduces back to the original mod-`2` matrix. -/
theorem e8MatrixModFourCorrectedLift_to_modTwo
    (Y A : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8QuadraticIsometryModFourToModTwoMatrix (e8MatrixModFourCorrectedLift Y A) = Y := by
  ext i j
  dsimp [e8QuadraticIsometryModFourToModTwoMatrix, e8MatrixModFourCorrectedLift,
    e8MatrixModTwoLiftToModFour, e8MatrixModTwoCorrectionToModFour]
  exact (by decide : ∀ y a : ZMod 2,
    (zmodTwoLiftToFour y + (2 : ZMod 4) * zmodTwoLiftToFour a).cast = y) (Y i j) (A i j)

/-- For an even mod-`4` difference, record the corresponding mod-`2` half. -/
def zmodFourHalfDifferenceFromLift (x : ZMod 4) (_y : ZMod 2) : ZMod 2 :=
  ((x.val / 2 : ℕ) : ZMod 2)

/-- The entrywise correction matrix recovered from a mod-`4` matrix whose
reduction is the supplied mod-`2` matrix. -/
def e8MatrixModFourCorrectionOfReduction
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (X : Matrix (Fin 8) (Fin 8) (ZMod 4)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => zmodFourHalfDifferenceFromLift (X i j - zmodTwoLiftToFour (Y i j)) (Y i j)

/-- A mod-`4` scalar with prescribed mod-`2` reduction is recovered by the
chosen `0/1` lift plus twice the recovered half-difference. -/
theorem zmodTwoLiftToFour_add_two_halfDifference_eq
    (x : ZMod 4) (y : ZMod 2) (hxy : x.cast = y) :
    zmodTwoLiftToFour y +
        (2 : ZMod 4) * zmodTwoLiftToFour (zmodFourHalfDifferenceFromLift (x - zmodTwoLiftToFour y) y) = x := by
  exact (by decide : ∀ (x : ZMod 4) (y : ZMod 2), x.cast = y →
    zmodTwoLiftToFour y +
        (2 : ZMod 4) * zmodTwoLiftToFour (zmodFourHalfDifferenceFromLift (x - zmodTwoLiftToFour y) y) = x) x y hxy

/-- The half-difference recovered from an already-corrected scalar is the
original correction. -/
theorem zmodFourHalfDifferenceFromLift_corrected
    (y a : ZMod 2) :
    zmodFourHalfDifferenceFromLift
        (zmodTwoLiftToFour y + (2 : ZMod 4) * zmodTwoLiftToFour a - zmodTwoLiftToFour y) y = a := by
  exact (by decide : ∀ y a : ZMod 2,
    zmodFourHalfDifferenceFromLift
        (zmodTwoLiftToFour y + (2 : ZMod 4) * zmodTwoLiftToFour a - zmodTwoLiftToFour y) y = a) y a

/-- A mod-`4` matrix with prescribed mod-`2` reduction is recovered by its
canonical lift plus the entrywise recovered correction. -/
theorem e8MatrixModFourCorrectedLift_correctionOfReduction
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (X : Matrix (Fin 8) (Fin 8) (ZMod 4))
    (hX : e8QuadraticIsometryModFourToModTwoMatrix X = Y) :
    e8MatrixModFourCorrectedLift Y (e8MatrixModFourCorrectionOfReduction Y X) = X := by
  ext i j
  dsimp [e8MatrixModFourCorrectedLift, e8MatrixModTwoLiftToModFour,
    e8MatrixModTwoCorrectionToModFour, e8MatrixModFourCorrectionOfReduction]
  exact zmodTwoLiftToFour_add_two_halfDifference_eq (X i j) (Y i j)
    (by simpa [e8QuadraticIsometryModFourToModTwoMatrix] using congrFun (congrFun hX i) j)

/-- Recovering the correction from a corrected lift returns the original
correction matrix. -/
theorem e8MatrixModFourCorrectionOfReduction_correctedLift
    (Y A : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    e8MatrixModFourCorrectionOfReduction Y (e8MatrixModFourCorrectedLift Y A) = A := by
  ext i j
  dsimp [e8MatrixModFourCorrectionOfReduction, e8MatrixModFourCorrectedLift,
    e8MatrixModTwoLiftToModFour, e8MatrixModTwoCorrectionToModFour]
  exact zmodFourHalfDifferenceFromLift_corrected (Y i j) (A i j)

/-- A correction matrix whose corrected lift preserves `Q_E8` modulo `4`. -/
abbrev e8QuadraticIsometryModFourCorrectionFiber (Y : e8QuadraticIsometryModTwo) :=
  {A : Matrix (Fin 8) (Fin 8) (ZMod 2) //
    ∀ v : Fin 8 → ZMod 4,
      e8QuadraticPolynomial ((e8MatrixModFourCorrectedLift Y.1 A).mulVec v) =
        e8QuadraticPolynomial v}

noncomputable instance (Y : e8QuadraticIsometryModTwo) :
    Fintype (e8QuadraticIsometryModFourCorrectionFiber Y) := by
  classical
  unfold e8QuadraticIsometryModFourCorrectionFiber
  infer_instance

/-- The correction fiber over the identity mod-`2` E8 quadratic isometry. -/
abbrev e8QuadraticIsometryModFourIdentityCorrectionFiber :=
  e8QuadraticIsometryModFourCorrectionFiber e8QuadraticIsometryModTwoIdentity

/-- Membership in the identity correction fiber is the concrete equation
`Q(v + 2A(v mod 2)) = Q(v)`. -/
theorem e8QuadraticIsometryModFourIdentityCorrectionFiber_mem_iff
    (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    (∀ v : Fin 8 → ZMod 4,
      e8QuadraticPolynomial
          ((e8MatrixModFourCorrectedLift
              (1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) A).mulVec v) =
        e8QuadraticPolynomial v) ↔
      ∀ v : Fin 8 → ZMod 4,
        e8QuadraticPolynomial
            (fun i : Fin 8 => v i + (2 : ZMod 4) * zmodTwoLiftToFour
              (A.mulVec (fun j : Fin 8 => (v j).cast) i)) =
          e8QuadraticPolynomial v := by
  constructor
  · intro h v
    simpa [e8MatrixModFourCorrectedLift_one_mulVec A v] using h v
  · intro h v
    simpa [e8MatrixModFourCorrectedLift_one_mulVec A v] using h v

/-- A correction matrix packages a concrete mod-`4` quadratic isometry. -/
def e8QuadraticIsometryModFourOfCorrection
    (Y : e8QuadraticIsometryModTwo)
    (A : e8QuadraticIsometryModFourCorrectionFiber Y) : e8QuadraticIsometryModFour :=
  ⟨e8MatrixModFourCorrectedLift Y.1 A.1, A.2⟩

/-- The mod-`4` isometry produced by a correction reduces to the original
mod-`2` quadratic isometry. -/
theorem e8QuadraticIsometryModFourOfCorrection_to_modTwo
    (Y : e8QuadraticIsometryModTwo)
    (A : e8QuadraticIsometryModFourCorrectionFiber Y) :
    e8QuadraticIsometryModFourToModTwoMatrix
        (e8QuadraticIsometryModFourOfCorrection Y A).1 = Y.1 := by
  exact e8MatrixModFourCorrectedLift_to_modTwo Y.1 A.1

/-- The raw fiber of mod-`4` quadratic isometry lifts of a fixed mod-`2`
quadratic isometry is equivalent to the explicit correction-fiber type. -/
noncomputable def e8QuadraticIsometryModFourRawReductionFiberEquivCorrectionFiber
    (Y : e8QuadraticIsometryModTwo) :
    {X : e8QuadraticIsometryModFour //
      e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y.1} ≃
      e8QuadraticIsometryModFourCorrectionFiber Y where
  toFun X :=
    ⟨e8MatrixModFourCorrectionOfReduction Y.1 X.1.1, by
      intro v
      have hmat : e8MatrixModFourCorrectedLift Y.1
            (e8MatrixModFourCorrectionOfReduction Y.1 X.1.1) = X.1.1 :=
        e8MatrixModFourCorrectedLift_correctionOfReduction Y.1 X.1.1 X.2
      simpa [hmat] using X.1.2 v⟩
  invFun A :=
    ⟨e8QuadraticIsometryModFourOfCorrection Y A,
      e8QuadraticIsometryModFourOfCorrection_to_modTwo Y A⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact e8MatrixModFourCorrectedLift_correctionOfReduction Y.1 X.1.1 X.2
  right_inv A := by
    apply Subtype.ext
    exact e8MatrixModFourCorrectionOfReduction_correctedLift Y.1 A.1

/-- Cardinality form of the equivalence between raw lift fibers and correction
fibers. -/
theorem e8QuadraticIsometryModFour_rawReductionFiber_natCard_eq_correctionFiber
    (Y : e8QuadraticIsometryModTwo) :
    Nat.card {X : e8QuadraticIsometryModFour //
      e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y.1} =
      Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y) :=
  Nat.card_congr (e8QuadraticIsometryModFourRawReductionFiberEquivCorrectionFiber Y)

/-- The named reduction-image fiber over an image point is equivalent to the
raw lift fiber over the corresponding mod-`2` quadratic isometry. -/
noncomputable def e8QuadraticIsometryModFourReductionModTwoFiberEquivRawReductionFiber
    (Y : e8QuadraticIsometryModFourReductionModTwoImage) :
    {X : e8QuadraticIsometryModFour //
      e8QuadraticIsometryModFourReductionModTwo X = Y} ≃
      {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourToModTwoMatrix X.1 =
          (e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry Y).1} where
  toFun X :=
    ⟨X.1, by
      have h := congrArg Subtype.val X.2
      simpa [e8QuadraticIsometryModFourReductionModTwo,
        e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry] using h⟩
  invFun X :=
    ⟨X.1, by
      apply Subtype.ext
      simpa [e8QuadraticIsometryModFourReductionModTwo,
        e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry] using X.2⟩
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    rfl

/-- A named reduction-image fiber has the same cardinality as the explicit
correction fiber over the corresponding mod-`2` quadratic isometry. -/
theorem e8QuadraticIsometryModFourReductionModTwo_fiber_natCard_eq_correctionFiber
    (Y : e8QuadraticIsometryModFourReductionModTwoImage) :
    Nat.card {X : e8QuadraticIsometryModFour //
      e8QuadraticIsometryModFourReductionModTwo X = Y} =
      Nat.card (e8QuadraticIsometryModFourCorrectionFiber
        (e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry Y)) := by
  rw [Nat.card_congr (e8QuadraticIsometryModFourReductionModTwoFiberEquivRawReductionFiber Y)]
  exact e8QuadraticIsometryModFour_rawReductionFiber_natCard_eq_correctionFiber
    (e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry Y)

/-- Nonempty correction fibers for every mod-`2` quadratic isometry imply the
lift-surjectivity input used by the E8 local-factor bridge. -/
theorem e8QuadraticIsometryModFour_lift_surjective_of_correction_nonempty
    (hcorr : ∀ Y : e8QuadraticIsometryModTwo,
      Nonempty (e8QuadraticIsometryModFourCorrectionFiber Y)) :
    ∀ Y : e8QuadraticIsometryModTwo,
      ∃ X : e8QuadraticIsometryModFour,
        e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y.1 := by
  intro Y
  rcases hcorr Y with ⟨A⟩
  exact ⟨e8QuadraticIsometryModFourOfCorrection Y A,
    e8QuadraticIsometryModFourOfCorrection_to_modTwo Y A⟩

/-- Cardinality consequence of the verified containment for the corrected
`ZMod 4` quadratic-isometry reduction image. -/
theorem e8QuadraticIsometryModFourReductionModTwoImage_natCard_le_quadraticIsometry :
    Nat.card e8QuadraticIsometryModFourReductionModTwoImage ≤
      Nat.card e8QuadraticIsometryModTwo :=
  Nat.card_le_card_of_injective
    e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry
    e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry_injective

/-- The corrected `ZMod 4` reduction image is bounded by the already-counted
mod-`2` quadratic-isometry target.  Equality/surjectivity is the remaining
image comparison. -/
theorem e8QuadraticIsometryModFourReductionModTwoImage_natCard_le_348364800 :
    Nat.card e8QuadraticIsometryModFourReductionModTwoImage ≤ 348364800 := by
  rw [← e8QuadraticIsometryModTwo_natCard_eq_348364800]
  exact e8QuadraticIsometryModFourReductionModTwoImage_natCard_le_quadraticIsometry

/-- The named mod-`2` image of E8 depth-three solutions maps into the corrected
quadratic-isometry target.  This records the verified image-containment half of
the remaining image-comparison problem. -/
noncomputable def e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry
    (Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage) :
    e8QuadraticIsometryModTwo :=
  ⟨Y.1, by
    rcases Y.2 with ⟨X, hX⟩
    simpa [← hX, e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModTwo_coe]
      using (e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModTwo X).2⟩

/-- The image-containment map into the corrected quadratic-isometry target keeps
the same underlying mod-`2` matrix. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry_coe
    (Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage) :
    (e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry Y).1 = Y.1 := by
  rfl

/-- The named mod-`2` image embeds in the corrected quadratic-isometry target. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry_injective :
    Function.Injective
      e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry := by
  intro Y Z h
  apply Subtype.ext
  exact congrArg (fun T : e8QuadraticIsometryModTwo => T.1) h

/-- Cardinality consequence of the verified containment of the named mod-`2`
image in the corrected quadratic-isometry target.  Equality/surjectivity remains
the open finite-field comparison. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage_natCard_le_quadraticIsometry :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage ≤
      Nat.card e8QuadraticIsometryModTwo :=
  Nat.card_le_card_of_injective
    e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry
    e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageToQuadraticIsometry_injective

/-- The verified image-containment direction bounds the depth-three mod-`2`
image by the now-counted corrected E8 quadratic-isometry target.  The reverse
inequality/equality is the remaining finite-field image comparison. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage_natCard_le_348364800 :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage ≤ 348364800 := by
  rw [← e8QuadraticIsometryModTwo_natCard_eq_348364800]
  exact e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage_natCard_le_quadraticIsometry

/-- If every mod-`2` image point has exactly `2^28` E8 mod-`4` matrix lifts,
then the E8 matrix-solution subtype cardinality factors through the mod-`2`
image count. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrix_natCard_eq_modTwoImage_mul_of_fiber_card
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix =
      Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage * 2 ^ 28 := by
  exact nat_card_eq_mul_of_fiber_card
    e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo (2 ^ 28) hfiber

/-- The same uniform-fiber factorization for the filtered E8 finite set. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrices_card_eq_modTwoImage_mul_of_fiber_card
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8LatticeDepthThreeCoordinateSolutionMatrices.card =
      Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage * 2 ^ 28 := by
  rw [e8Lattice_depthThreeCoordinateSolutionMatrices_card,
    e8Lattice_depthThreeCoordinateSolutionMatrix_natCard_eq_modTwoImage_mul_of_fiber_card hfiber]

/-- If the mod-`2` image has the expected base cardinality and every image
point has `2^28` E8 mod-`4` lifts, then the native dyadic Schulze--Pillot local
factor is `42525/256`.  Both finite count assertions remain explicit hypotheses. -/
theorem e8Lattice_massLocalFactor_two_eq_of_modTwoImage_natCard_and_fiber_card
    (hbase : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionMatrices_card
    (by
      rw [e8Lattice_depthThreeCoordinateSolutionMatrices_card_eq_modTwoImage_mul_of_fiber_card hfiber, hbase]
      exact e8Lattice_depthThreeCoordinateSolutionMatrices_expected_card_factorization)

/-- Conditional bridge from the corrected quadratic mod-two base count and the
existing uniform fiber target to the native E8 dyadic factor. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_natCard_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      Nat.card e8QuadraticIsometryModTwo)
    (hbase : Nat.card e8QuadraticIsometryModTwo = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_modTwoImage_natCard_and_fiber_card
    (by rw [himage, hbase]) hfiber

/-- Corrected E8 quadratic mod-two bridge with the base count discharged by the
split four-hyperbolic-plane count.  The remaining hypotheses are exactly the
reverse image/cardinality comparison and uniform `2^28` mod-`4` lift count. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_image_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      Nat.card e8QuadraticIsometryModTwo)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_natCard_and_fiber_card
    himage e8QuadraticIsometryModTwo_natCard_eq_348364800 hfiber

/-- The old depth-three fiber over a mod-`2` image point is the same finite type
as the fiber of the corrected `ZMod 4` quadratic-isometry reduction over the
corresponding image point. -/
noncomputable def
    e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwoFiberEquivQuadraticIsometryModFourReductionModTwoFiber
    (Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage) :
    {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
      e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} ≃
      {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourReductionModTwo X =
          e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage Y} where
  toFun X :=
    ⟨e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour X.1, by
      apply Subtype.ext
      have h := congrArg Subtype.val X.2
      simpa [e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo,
        e8QuadraticIsometryModFourReductionModTwo,
        e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage,
        e8LatticeDepthThreeCoordinateSolutionMatrixToQuadraticIsometryModFour,
        e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo,
        e8QuadraticIsometryModFourToModTwoMatrix, primePowModulus] using h⟩
  invFun X :=
    ⟨e8QuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix X.1, by
      apply Subtype.ext
      have h := congrArg Subtype.val X.2
      simpa [e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo,
        e8QuadraticIsometryModFourReductionModTwo,
        e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage,
        e8QuadraticIsometryModFourToDepthThreeCoordinateSolutionMatrix,
        e8LatticeDepthThreeCoordinateSolutionMatrixModFourToModTwo,
        e8QuadraticIsometryModFourToModTwoMatrix, primePowModulus] using h⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Fiber cardinalities are unchanged by replacing the depth-three matrix target
with the equivalent corrected `ZMod 4` quadratic-isometry target. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo_fiber_natCard_eq_quadraticIsometryModFourReductionModTwo_fiber
    (Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage) :
    Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
      e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} =
      Nat.card {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourReductionModTwo X =
          e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage Y} :=
  Nat.card_congr
    (e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwoFiberEquivQuadraticIsometryModFourReductionModTwoFiber Y)

/-- Corrected E8 bridge stated directly for the `ZMod 4 → ZMod 2`
quadratic-isometry reduction.  The remaining hypotheses are the surjectivity/cardinality
comparison for that reduction image and the uniform `2^28` lift
count for its fibers. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModFourReduction_image_and_fiber_card
    (himage : Nat.card e8QuadraticIsometryModFourReductionModTwoImage =
      Nat.card e8QuadraticIsometryModTwo)
    (hfiber : ∀ Y : e8QuadraticIsometryModFourReductionModTwoImage,
      Nat.card {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_image_and_fiber_card
    (by
      rw [e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage_natCard_eq_quadraticIsometryModFourReductionModTwoImage]
      exact himage)
    (fun Y => by
      rw [e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo_fiber_natCard_eq_quadraticIsometryModFourReductionModTwo_fiber]
      exact hfiber
        (e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImageEquivQuadraticIsometryModFourReductionModTwoImage Y))

/-- Corrected E8 bridge stated with the image comparison as direct lift
surjectivity for `e8QuadraticIsometryModFour → e8QuadraticIsometryModTwo`, plus
the uniform `2^28` fiber count for the same reduction map. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModFourReduction_lift_and_fiber_card
    (hlift : ∀ Y : e8QuadraticIsometryModTwo,
      ∃ X : e8QuadraticIsometryModFour,
        e8QuadraticIsometryModFourToModTwoMatrix X.1 = Y.1)
    (hfiber : ∀ Y : e8QuadraticIsometryModFourReductionModTwoImage,
      Nat.card {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModFourReduction_image_and_fiber_card
    (e8QuadraticIsometryModFourReductionModTwoImage_natCard_eq_quadraticIsometry_of_lift hlift) hfiber

/-- Corrected E8 bridge with the lift-surjectivity input stated as nonemptiness
of the explicit `0/1 + 2A` correction fibers. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModFourCorrection_nonempty_and_fiber_card
    (hcorr : ∀ Y : e8QuadraticIsometryModTwo,
      Nonempty (e8QuadraticIsometryModFourCorrectionFiber Y))
    (hfiber : ∀ Y : e8QuadraticIsometryModFourReductionModTwoImage,
      Nat.card {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModFourReduction_lift_and_fiber_card
    (e8QuadraticIsometryModFour_lift_surjective_of_correction_nonempty hcorr) hfiber

/-- Corrected E8 bridge with the remaining lift count stated entirely as a
uniform cardinality of the explicit `0/1 + 2A` correction fibers.  Positivity of
`2^28` supplies the nonemptiness needed for lift-surjectivity. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModFourCorrection_fiber_card
    (hfiber : ∀ Y : e8QuadraticIsometryModTwo,
      Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y) = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  have hcorr : ∀ Y : e8QuadraticIsometryModTwo,
      Nonempty (e8QuadraticIsometryModFourCorrectionFiber Y) := by
    intro Y
    exact (Nat.card_pos_iff.mp (by rw [hfiber Y]; norm_num :
      0 < Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y))).1
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModFourCorrection_nonempty_and_fiber_card
    hcorr
    (fun Y => by
      rw [e8QuadraticIsometryModFourReductionModTwo_fiber_natCard_eq_correctionFiber]
      exact hfiber (e8QuadraticIsometryModFourReductionModTwoImageToQuadraticIsometry Y))

/-- Variant of the corrected E8 bridge using the finite-set cardinality of the
mod-`2` quadratic-isometry target. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModFourReduction_image_card_and_fiber_card
    (himage : Nat.card e8QuadraticIsometryModFourReductionModTwoImage =
      e8QuadraticIsometryModTwoMatrices.card)
    (hfiber : ∀ Y : e8QuadraticIsometryModFourReductionModTwoImage,
      Nat.card {X : e8QuadraticIsometryModFour //
        e8QuadraticIsometryModFourReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModFourReduction_image_and_fiber_card
    (by rw [himage, e8QuadraticIsometryModTwoMatrices_card]) hfiber

/-- Finite-set-cardinality variant of the corrected E8 quadratic mod-two bridge. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_card_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      e8QuadraticIsometryModTwoMatrices.card)
    (hbase : e8QuadraticIsometryModTwoMatrices.card = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_natCard_and_fiber_card
    (by rw [himage, e8QuadraticIsometryModTwoMatrices_card])
    (by rw [← e8QuadraticIsometryModTwoMatrices_card, hbase]) hfiber

/-- Finite-set corrected E8 quadratic mod-two bridge with the base count already
discharged. -/
theorem e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_image_card_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      e8QuadraticIsometryModTwoMatrices.card)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_image_and_fiber_card
    (by rw [himage, e8QuadraticIsometryModTwoMatrices_card]) hfiber

/-- Split-model subtype-cardinality variant of the corrected E8 quadratic
mod-two bridge.  This is the Lean-facing form of the base-count target
after conjugating `Q_E8` to four hyperbolic planes over `𝔽₂`. -/
theorem e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_natCard_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      Nat.card e8SplitQuadraticIsometryModTwo)
    (hbase : Nat.card e8SplitQuadraticIsometryModTwo = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_quadraticModTwo_natCard_and_fiber_card
    (by rw [himage, ← e8QuadraticIsometryModTwo_natCard_eq_split])
    (by rw [e8QuadraticIsometryModTwo_natCard_eq_split, hbase]) hfiber

/-- Split-model bridge with the base count discharged by the proved split
quadratic-isometry count. -/
theorem e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_image_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      Nat.card e8SplitQuadraticIsometryModTwo)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_natCard_and_fiber_card
    himage e8SplitQuadraticIsometryModTwo_natCard_eq_348364800 hfiber

/-- Split-model finite-set-cardinality variant of the corrected E8 quadratic
mod-two bridge. -/
theorem e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_card_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      e8SplitQuadraticIsometryModTwoMatrices.card)
    (hbase : e8SplitQuadraticIsometryModTwoMatrices.card = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_natCard_and_fiber_card
    (by rw [himage, e8SplitQuadraticIsometryModTwoMatrices_card])
    (by rw [← e8SplitQuadraticIsometryModTwoMatrices_card, hbase]) hfiber

/-- Split finite-set bridge with the base count discharged by the proved split
quadratic-isometry count. -/
theorem e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_image_card_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      e8SplitQuadraticIsometryModTwoMatrices.card)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_splitQuadraticModTwo_card_and_fiber_card
    himage e8SplitQuadraticIsometryModTwoMatrices_card_eq_348364800 hfiber


/-- The mod-`2` Gram-congruence target for the E8 seed, using the bilinear
Gram matrix.  Because the Gram matrix here is `2 • pairingMatrix`, this mod-`2`
target is the full matrix set and is not the quadratic-isometry base target for
the E8 dyadic count. -/
noncomputable def e8LatticeModTwoGramCongruenceMatrices :
    Finset (Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 1 : ℕ))) :=
  gramCongruenceSolutionMatrices e8Lattice 2 1

/-- The subtype form of the E8 mod-`2` Gram-congruence target.  This turns
the finite set target into a `Nat.card` target parallel to the mod-`2` image
subtype, but it is not the quadratic-isometry target. -/
abbrev e8LatticeModTwoGramCongruenceMatrix : Type :=
  e8LatticeModTwoGramCongruenceMatrices

noncomputable instance : Fintype e8LatticeModTwoGramCongruenceMatrix := by
  classical
  exact Finset.fintypeCoeSort e8LatticeModTwoGramCongruenceMatrices

/-- The filtered finite set and subtype presentations of the E8 mod-`2`
Gram-congruence target have the same cardinality. -/
theorem e8Lattice_modTwoGramCongruenceMatrices_card :
    e8LatticeModTwoGramCongruenceMatrices.card =
      Nat.card e8LatticeModTwoGramCongruenceMatrix := by
  classical
  change e8LatticeModTwoGramCongruenceMatrices.card =
    Nat.card ↥e8LatticeModTwoGramCongruenceMatrices
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_coe e8LatticeModTwoGramCongruenceMatrices).symm

/-- Membership in the named E8 mod-`2` Gram-congruence target. -/
theorem mem_e8LatticeModTwoGramCongruenceMatrices_iff
    (X : Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 1 : ℕ))) :
    X ∈ e8LatticeModTwoGramCongruenceMatrices ↔
      (Matrix.transpose X * matrixMod e8Lattice.polarGramMatrix (primePowModulus 2 1) * X =
        matrixMod e8Lattice.polarGramMatrix (primePowModulus 2 1)) := by
  simpa [e8LatticeModTwoGramCongruenceMatrices] using
    (mem_gramCongruenceSolutionMatrices_iff (L := e8Lattice) (p := 2) (k := 1) (X := X))


/-- The E8 mod-`2` Gram-congruence target uses the bilinear Gram matrix,
which vanishes modulo two under the normalization `polarGramMatrix =
2 • pairingMatrix`. -/
theorem matrixMod_e8Lattice_polarGramMatrix_two_eq_zero :
    matrixMod e8Lattice.polarGramMatrix (primePowModulus 2 1) =
      (0 : Matrix (Fin 8) (Fin 8) (ZMod (primePowModulus 2 1 : ℕ))) := by
  rw [matrixMod_polarGramMatrix_eq_two_smul_pairingMatrix]
  have htwo : (2 : ZMod (primePowModulus 2 1 : ℕ)) = 0 := by
    change (2 : ZMod 2) = 0
    exact (ZMod.natCast_eq_zero_iff 2 2).2 dvd_rfl
  ext i j
  simp [htwo]

/-- Therefore the E8 mod-`2` Gram-congruence finite set is the full matrix
set.  The E8 dyadic count must use the quadratic form modulo two instead. -/
theorem e8LatticeModTwoGramCongruenceMatrices_eq_univ :
    e8LatticeModTwoGramCongruenceMatrices = Finset.univ := by
  classical
  ext X
  rw [mem_e8LatticeModTwoGramCongruenceMatrices_iff]
  simp [matrixMod_e8Lattice_polarGramMatrix_two_eq_zero]

set_option backward.isDefEq.respectTransparency false in
/-- A depth-three E8 `ZMod 4` matrix solution is also a depth-two solution
for the same coordinate denominator.  This is only a reduction of the modulus
in the quadratic congruence, not a count. -/
theorem e8LatticeDepthThreeCoordinateSolutionMatrix_mem_depthTwo
    (X : e8LatticeDepthThreeCoordinateSolutionMatrix) :
    localDualQuotientLiftFamily (n := 8) 2 2 X.1 ∈
      localDualQuotientSolutionFamilies e8Lattice 2 2
        (primePowCoordinateSubmodule (n := 8) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8) 2 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have h8 := (mem_localDualQuotientSolutionFamilies_iff.mp X.2) x y hxy
  have hdiv : (primePowModulus 2 2 : ℕ) ∣ (primePowModulus 2 3 : ℕ) := by
    norm_num [primePowModulus]
  have hcast := congrArg (ZMod.castHom hdiv (ZMod (primePowModulus 2 2 : ℕ))) h8
  simpa [primePowModulus] using hcast

/-- A lifted coordinate solution family gives a Gram-congruence matrix at
the same prime-power level.  This packages the existing family-matrix bridge
for the coordinate-denominator presentation used by the dyadic E8 target. -/
theorem localDualQuotientLiftFamily_mem_gramCongruenceSolutionMatrices
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : localDualQuotientLiftFamily (n := n) p k X ∈
      localDualQuotientSolutionFamilies L p k
        (primePowCoordinateSubmodule (n := n) p k)
        (primePowCoordinateSubmodule_rank (n := n) p k)) :
    X ∈ gramCongruenceSolutionMatrices L p k := by
  have h := localDualQuotientFamilyMatrix_mem_gramCongruenceSolutionMatrices
    (L := L) (p := p) (k := k) hX
  simpa using h

/-- Gram-congruence solution matrices reduce along a quotient map of
prime-power moduli.  This is a bookkeeping lemma for finite-level targets. -/
theorem gramCongruenceSolutionMatrices_map_castHom_mem
    (L : PositiveDefiniteIntegralLattice n) (p k r : ℕ) [Fact (Nat.Prime p)]
    (hdiv : (primePowModulus p r : ℕ) ∣ (primePowModulus p k : ℕ))
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : X ∈ gramCongruenceSolutionMatrices L p k) :
    X.map (ZMod.castHom hdiv (ZMod (primePowModulus p r : ℕ))) ∈
      gramCongruenceSolutionMatrices L p r := by
  rw [mem_gramCongruenceSolutionMatrices_iff] at hX ⊢
  let f : ZMod (primePowModulus p k : ℕ) →+* ZMod (primePowModulus p r : ℕ) :=
    ZMod.castHom hdiv _
  have hf (z : ℤ) : f (z : ZMod (primePowModulus p k : ℕ)) =
      (z : ZMod (primePowModulus p r : ℕ)) := by
    rw [ZMod.castHom_apply]
    exact ZMod.cast_intCast hdiv z
  have hfun :
      (⇑f ∘ (Int.cast : ℤ → ZMod (primePowModulus p k : ℕ))) =
        (Int.cast : ℤ → ZMod (primePowModulus p r : ℕ)) := by
    funext z
    exact hf z
  have hcast := congrArg (RingHom.mapMatrix f) hX
  change ((Matrix.transpose X * matrixMod L.polarGramMatrix (primePowModulus p k) * X).map f) =
    (matrixMod L.polarGramMatrix (primePowModulus p k)).map f at hcast
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hcast
  simp only [matrixMod, Matrix.map_map] at hcast
  rw [hfun] at hcast
  simpa [f] using hcast

/-- Combining the coordinate lifted-family bridge with reduction of
Gram-congruence matrices: a coordinate solution at level `p^k` reduces to a
Gram-congruence solution at any lower prime-power quotient. -/
theorem localDualQuotientLiftFamily_map_castHom_mem_gramCongruenceSolutionMatrices
    (L : PositiveDefiniteIntegralLattice n) (p k r : ℕ) [Fact (Nat.Prime p)]
    (hdiv : (primePowModulus p r : ℕ) ∣ (primePowModulus p k : ℕ))
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : localDualQuotientLiftFamily (n := n) p k X ∈
      localDualQuotientSolutionFamilies L p k
        (primePowCoordinateSubmodule (n := n) p k)
        (primePowCoordinateSubmodule_rank (n := n) p k)) :
    X.map (ZMod.castHom hdiv (ZMod (primePowModulus p r : ℕ))) ∈
      gramCongruenceSolutionMatrices L p r := by
  exact gramCongruenceSolutionMatrices_map_castHom_mem
    (L := L) (p := p) (k := k) (r := r) hdiv
    (localDualQuotientLiftFamily_mem_gramCongruenceSolutionMatrices
      (L := L) (p := p) (k := k) hX)

/-- Conditional local factor through the mod-`2` Gram-congruence target.
The premise `hbase` is false for this target: the set is `Finset.univ`, since
`matrixMod e8Lattice.polarGramMatrix 2 = 0`.  The E8 count uses the direct
mod-`2` image/fiber statement, or a quadratic-form mod-`2` target, instead. -/
theorem e8Lattice_massLocalFactor_two_eq_of_modTwoGramCongruence_card_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      e8LatticeModTwoGramCongruenceMatrices.card)
    (hbase : e8LatticeModTwoGramCongruenceMatrices.card = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_modTwoImage_natCard_and_fiber_card
    (by rw [himage, hbase]) hfiber

/-- Subtype-cardinality variant of the E8 mod-`2` Gram-congruence bridge.
Its base-cardinality premise is a hypothesis that is not established here. -/
theorem e8Lattice_massLocalFactor_two_eq_of_modTwoGramCongruence_natCard_and_fiber_card
    (himage : Nat.card e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage =
      Nat.card e8LatticeModTwoGramCongruenceMatrix)
    (hbase : Nat.card e8LatticeModTwoGramCongruenceMatrix = 348364800)
    (hfiber : ∀ Y : e8LatticeDepthThreeCoordinateSolutionMatrixModTwoImage,
      Nat.card {X : e8LatticeDepthThreeCoordinateSolutionMatrix //
        e8LatticeDepthThreeCoordinateSolutionMatrixReductionModTwo X = Y} = 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_modTwoGramCongruence_card_and_fiber_card
    (by rw [himage, ← e8Lattice_modTwoGramCongruenceMatrices_card])
    (by rw [e8Lattice_modTwoGramCongruenceMatrices_card, hbase]) hfiber

/-- If the filtered finite set of E8 `ZMod 4` matrix solutions has the factored
cardinality expected from a mod-`2` base count and a uniform `2^28` lift count,
then the native dyadic Schulze--Pillot local factor is `42525/256`.  This keeps
the finite enumeration as an explicit hypothesis. -/
theorem e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionMatrices_card_factored
    (hcount : e8LatticeDepthThreeCoordinateSolutionMatrices.card = 348364800 * 2 ^ 28) :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  exact e8Lattice_massLocalFactor_two_eq_of_depthThreeCoordinateSolutionMatrices_card
    (by
      rw [hcount]
      exact e8Lattice_depthThreeCoordinateSolutionMatrices_expected_card_factorization)


end PositiveDefiniteIntegralLattice
