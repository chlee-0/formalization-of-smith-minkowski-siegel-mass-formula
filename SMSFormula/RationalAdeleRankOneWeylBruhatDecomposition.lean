import SMSFormula.RationalAdeleRankOneEisensteinSiegelFunctional

/-!
# Rational Weyl action on the rank-one Bruhat cusp index

This file isolates the exact `2 × 2` rational matrix calculation needed for
the Weyl transformation of the convergent rank-one cusp functional.  We use
the explicit convention

```text
n(t) = [[1,t],[0,1]],   w = [[0,1],[-1,0]],
m(r) = [[r,0],[0,r⁻¹]].
```

Right multiplication by `w` swaps the infinity cusp with the finite cusp
`0`, and sends a nonzero finite parameter `t` to `-t⁻¹`.  The residual left
factor is upper triangular and has determinant one.  In the nonzero chart the
literal identity is

```text
w n(t) w = n(-t⁻¹) m(-t⁻¹) w n(-t⁻¹).
```

This is only the rational Bruhat representative square.  It deliberately does
not identify the existing analytic Fourier operator with a generic Weil
representation, nor assert how the residual diagonal factor acts on a test
function or its value at zero.
-/

noncomputable section

open Matrix

namespace RationalQuadraticSpaceMatrix

/-- The rational upper-unipotent rank-one matrix. -/
def rationalRankOneUnipotentMatrix (t : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, t; 0, 1]

/-- The chosen rational Weyl matrix. -/
def rationalRankOneWeylMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 1; -1, 0]

/-- The rational diagonal rank-one matrix `diag(r,r⁻¹)`. -/
def rationalRankOneDiagonalMatrix (r : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![r, 0; 0, r⁻¹]

@[simp]
theorem rationalRankOneUnipotentMatrix_det (t : ℚ) :
    (rationalRankOneUnipotentMatrix t).det = 1 := by
  simp [rationalRankOneUnipotentMatrix, Matrix.det_fin_two]

@[simp]
theorem rationalRankOneWeylMatrix_det :
    rationalRankOneWeylMatrix.det = 1 := by
  simp [rationalRankOneWeylMatrix, Matrix.det_fin_two]

@[simp]
theorem rationalRankOneDiagonalMatrix_det {r : ℚ} (hr : r ≠ 0) :
    (rationalRankOneDiagonalMatrix r).det = 1 := by
  simp [rationalRankOneDiagonalMatrix, Matrix.det_fin_two, hr]

/-- The exact nonzero-chart rational Bruhat decomposition.  The diagonal
factor appears explicitly. -/
theorem rationalRankOneWeyl_unipotent_weyl_decomposition
    (t : ℚ) (ht : t ≠ 0) :
    rationalRankOneWeylMatrix * rationalRankOneUnipotentMatrix t *
        rationalRankOneWeylMatrix =
      rationalRankOneUnipotentMatrix (-t⁻¹) *
        rationalRankOneDiagonalMatrix (-t⁻¹) *
        rationalRankOneWeylMatrix *
        rationalRankOneUnipotentMatrix (-t⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalRankOneWeylMatrix, rationalRankOneUnipotentMatrix,
      rationalRankOneDiagonalMatrix, Matrix.mul_apply, ht]

/-! ## The induced involution on the rational cusp index -/

/-- The right Weyl action on the affine-cusp model `{∞} ∪ ℚ`. -/
def rationalRankOneWeylCuspAction :
    RationalRankOneProjectiveCusp → RationalRankOneProjectiveCusp
  | Sum.inl _ => Sum.inr 0
  | Sum.inr t => if t = 0 then Sum.inl () else Sum.inr (-t⁻¹)

@[simp]
theorem rationalRankOneWeylCuspAction_infinity :
    rationalRankOneWeylCuspAction (Sum.inl ()) = Sum.inr 0 :=
  rfl

@[simp]
theorem rationalRankOneWeylCuspAction_finite_zero :
    rationalRankOneWeylCuspAction (Sum.inr 0) = Sum.inl () := by
  simp [rationalRankOneWeylCuspAction]

@[simp]
theorem rationalRankOneWeylCuspAction_finite_of_ne_zero
    {t : ℚ} (ht : t ≠ 0) :
    rationalRankOneWeylCuspAction (Sum.inr t) = Sum.inr (-t⁻¹) := by
  simp [rationalRankOneWeylCuspAction, ht]

/-- The rational Weyl cusp action is an involution. -/
theorem rationalRankOneWeylCuspAction_involutive :
    Function.Involutive rationalRankOneWeylCuspAction := by
  intro c
  rcases c with u | t
  · cases u
    simp
  · by_cases ht : t = 0
    · subst t
      simp
    · have hinv : -t⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht)
      simp [rationalRankOneWeylCuspAction, ht, hinv]

/-- The involutive permutation of the literal rational cusp index induced by
right multiplication by the Weyl matrix. -/
def rationalRankOneWeylCuspEquiv :
    RationalRankOneProjectiveCusp ≃ RationalRankOneProjectiveCusp :=
  rationalRankOneWeylCuspAction_involutive.toPerm

/-! ## The exact representative square -/

/-- Bruhat representatives: the identity at infinity and `w n(t)` on the
finite chart. -/
def rationalRankOneBruhatRepresentative :
    RationalRankOneProjectiveCusp → Matrix (Fin 2) (Fin 2) ℚ
  | Sum.inl _ => 1
  | Sum.inr t =>
      rationalRankOneWeylMatrix * rationalRankOneUnipotentMatrix t

/-- The residual left upper-triangular factor after right multiplication by
`w`.  Its nonzero branch keeps the diagonal matrix visible. -/
def rationalRankOneWeylBruhatFactor :
    RationalRankOneProjectiveCusp → Matrix (Fin 2) (Fin 2) ℚ
  | Sum.inl _ => 1
  | Sum.inr t =>
      if t = 0 then -1 else
        rationalRankOneUnipotentMatrix (-t⁻¹) *
          rationalRankOneDiagonalMatrix (-t⁻¹)

@[simp]
theorem rationalRankOneBruhatRepresentative_det
    (c : RationalRankOneProjectiveCusp) :
    (rationalRankOneBruhatRepresentative c).det = 1 := by
  rcases c with _ | t
  · simp [rationalRankOneBruhatRepresentative]
  · simp [rationalRankOneBruhatRepresentative, Matrix.det_mul]

/-- Every residual factor is upper triangular. -/
theorem rationalRankOneWeylBruhatFactor_lowerLeft
    (c : RationalRankOneProjectiveCusp) :
    rationalRankOneWeylBruhatFactor c 1 0 = 0 := by
  rcases c with _ | t
  · simp [rationalRankOneWeylBruhatFactor]
  · by_cases ht : t = 0 <;>
      simp [rationalRankOneWeylBruhatFactor, ht,
        rationalRankOneUnipotentMatrix, rationalRankOneDiagonalMatrix,
        Matrix.mul_apply]

/-- Every residual upper-triangular factor has determinant one. -/
theorem rationalRankOneWeylBruhatFactor_det
    (c : RationalRankOneProjectiveCusp) :
    (rationalRankOneWeylBruhatFactor c).det = 1 := by
  rcases c with _ | t
  · simp [rationalRankOneWeylBruhatFactor]
  · by_cases ht : t = 0
    · simp [rationalRankOneWeylBruhatFactor, ht, Matrix.det_fin_two]
    · rw [rationalRankOneWeylBruhatFactor, if_neg ht, Matrix.det_mul,
        rationalRankOneUnipotentMatrix_det,
        rationalRankOneDiagonalMatrix_det
          (neg_ne_zero.mpr (inv_ne_zero ht))]
      simp

/-- Exact commuting representative square for right multiplication by `w`.
The source representative times `w` is the target representative times the
visible residual upper-triangular factor on the left. -/
theorem rationalRankOneBruhatRepresentative_mul_weyl
    (c : RationalRankOneProjectiveCusp) :
    rationalRankOneBruhatRepresentative c * rationalRankOneWeylMatrix =
      rationalRankOneWeylBruhatFactor c *
        rationalRankOneBruhatRepresentative
          (rationalRankOneWeylCuspAction c) := by
  rcases c with _ | t
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rationalRankOneBruhatRepresentative,
        rationalRankOneWeylBruhatFactor, rationalRankOneWeylCuspAction,
        rationalRankOneWeylMatrix, rationalRankOneUnipotentMatrix,
        Matrix.mul_apply]
  · by_cases ht : t = 0
    · subst t
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rationalRankOneBruhatRepresentative,
          rationalRankOneWeylBruhatFactor, rationalRankOneWeylCuspAction,
          rationalRankOneWeylMatrix, rationalRankOneUnipotentMatrix,
          Matrix.mul_apply]
    · simp only [rationalRankOneBruhatRepresentative,
        rationalRankOneWeylBruhatFactor, rationalRankOneWeylCuspAction,
        ht, ↓reduceIte]
      rw [← Matrix.mul_assoc]
      exact rationalRankOneWeyl_unipotent_weyl_decomposition t ht

end RationalQuadraticSpaceMatrix

end
