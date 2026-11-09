import SMSFormula.CliffordSpinAction
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# The rational matrix realization of the Clifford Spin action

`CliffordSpinAction.lean` constructs the quadratic-isometry representation of
mathlib's Spin group on the underlying quadratic module.  This file specializes
that representation to a `RationalQuadraticSpaceMatrix` and connects it to the
repository's matrix orthogonal group.

For a symmetric matrix `A`, the associated bilinear form of
`A.toQuadraticMap'` is the bilinear form represented by `A`; consequently the
matrix recovered from the quadratic map is literally `A`.  The standard
equivalences

```text
LinearEquiv ≃ GeneralLinearGroup(Module),
GeneralLinearGroup(Matrix) ≃ GeneralLinearGroup(Module)
```

then turn the abstract Spin representation into invertible matrices.  The
matrix formula for composition of a quadratic map proves

```text
M.transpose * V.pairingMatrix * M = V.pairingMatrix.
```

Thus the representation lands in `V.rationalOrthogonalMatrixSubgroup`.
Determinant one, the central `mu_2` kernel, surjectivity, and base change are
handled in separate modules.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Recovering the matrix of the quadratic map defined by a symmetric matrix
returns the original matrix when two is invertible. -/
theorem toMatrix'_toQuadraticMap'_of_isSymm
    (A : Matrix ι ι R) (hA : A.IsSymm) :
    A.toQuadraticMap'.toMatrix' = A := by
  rw [QuadraticForm.toMatrix']
  have hsymm : (Matrix.toBilin' A).IsSymm := by
    constructor
    intro x y
    simp only [Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, x i * A i j * y j) =
          ∑ j, ∑ i, x i * A i j * y j := Finset.sum_comm
      _ = ∑ i, ∑ j, y i * A i j * x j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hA.apply i j]
        ring
  change LinearMap.BilinForm.toMatrix'
      (QuadraticMap.associatedHom ℕ
        (LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' A))) = A
  rw [QuadraticMap.associated_left_inverse ℕ hsymm.1]
  exact LinearMap.BilinForm.toMatrix'_toBilin' A

end Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The rational quadratic form represented by `V.pairingMatrix`. -/
def quadraticForm (V : RationalQuadraticSpaceMatrix n) :
    QuadraticForm ℚ (Fin n → ℚ) :=
  V.pairingMatrix.toQuadraticMap'

@[simp]
theorem quadraticForm_toMatrix' (V : RationalQuadraticSpaceMatrix n) :
    V.quadraticForm.toMatrix' = V.pairingMatrix :=
  Matrix.toMatrix'_toQuadraticMap'_of_isSymm V.pairingMatrix V.form_symm

/-- The matrix-unit realization of the generic Clifford Spin
representation. -/
def spinMatrixRepresentation (V : RationalQuadraticSpaceMatrix n) :
    spinGroup V.quadraticForm →* (Matrix (Fin n) (Fin n) ℚ)ˣ :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ
      (Fin n → ℚ)).symm.toMonoidHom.comp
        (spinGroup.conjugationRepresentation V.quadraticForm))

@[simp]
theorem spinMatrixRepresentation_val (V : RationalQuadraticSpaceMatrix n)
    (x : spinGroup V.quadraticForm) :
    (V.spinMatrixRepresentation x : Matrix (Fin n) (Fin n) ℚ) =
      LinearMap.toMatrix'
        ((spinGroup.conjugationRepresentation V.quadraticForm x).toLinearMap) := by
  rfl

/-- Multiplication by the realized matrix is the original Spin action. -/
@[simp]
theorem spinMatrixRepresentation_mulVec (V : RationalQuadraticSpaceMatrix n)
    (x : spinGroup V.quadraticForm) (m : Fin n → ℚ) :
    (V.spinMatrixRepresentation x : Matrix (Fin n) (Fin n) ℚ) *ᵥ m =
      spinGroup.conjugationRepresentation V.quadraticForm x m := by
  rw [spinMatrixRepresentation_val]
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix'
    (spinGroup.conjugationRepresentation V.quadraticForm x).toLinearMap) m

/-- Every matrix in the Spin representation preserves the rational form
matrix. -/
theorem spinMatrixRepresentation_mem_orthogonal
    (V : RationalQuadraticSpaceMatrix n)
    (x : spinGroup V.quadraticForm) :
    V.spinMatrixRepresentation x ∈ V.rationalOrthogonalMatrixSubgroup := by
  rw [V.mem_rationalOrthogonalMatrixSubgroup_iff]
  rw [spinMatrixRepresentation_val, ← V.quadraticForm_toMatrix']
  rw [← QuadraticForm.toMatrix'_comp]
  have hcomp : V.quadraticForm.comp
      (spinGroup.conjugationRepresentation V.quadraticForm x).toLinearMap =
      V.quadraticForm := by
    apply QuadraticMap.ext
    intro m
    exact spinGroup.conjugationRepresentation_map_app V.quadraticForm x m
  rw [hcomp]

/-- The rational matrix orthogonal representation induced by Clifford
conjugation. -/
def spinOrthogonalRepresentation (V : RationalQuadraticSpaceMatrix n) :
    spinGroup V.quadraticForm →* V.rationalOrthogonalMatrixSubgroup where
  toFun x := ⟨V.spinMatrixRepresentation x,
    V.spinMatrixRepresentation_mem_orthogonal x⟩
  map_one' := Subtype.ext (map_one V.spinMatrixRepresentation)
  map_mul' x y := Subtype.ext (map_mul V.spinMatrixRepresentation x y)

@[simp]
theorem spinOrthogonalRepresentation_coe
    (V : RationalQuadraticSpaceMatrix n)
    (x : spinGroup V.quadraticForm) :
    (V.spinOrthogonalRepresentation x :
      (Matrix (Fin n) (Fin n) ℚ)ˣ) = V.spinMatrixRepresentation x :=
  rfl

end RationalQuadraticSpaceMatrix
