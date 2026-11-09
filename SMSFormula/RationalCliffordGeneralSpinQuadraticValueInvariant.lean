import SMSFormula.RationalCliffordGeneralSpinAdelicCarrier
import SMSFormula.RationalAdeleRankOneQuadraticPhase

/-!
# The acting group preserves the quadratic value

A special-orthogonal matrix point satisfies `Mᵀ F M = F` by definition, so the quadratic value
is unchanged by the matrix action, over any commutative `ℚ`-algebra and in particular over the
full adeles.  Hence the acting full-adelic `GSpin` group maps every fiber of the adelic
quadratic value into itself.

This is the fibration-preserving half of the input the invariant disintegration needs: the
group acts on the coordinate space over the value line.  The other half -- that the coordinate
Haar itself is preserved -- is a different statement and is not proved here.

Negative scope: no measure is moved, no disintegration is constructed, and nothing is claimed
about the adelic modulus of the matrix action.
-/

noncomputable section

open Matrix
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- A special-orthogonal matrix point preserves the matrix quadratic expression over any
commutative `ℚ`-algebra. -/
theorem specialOrthogonalMatrixPoint_dotProduct_mulVec
    (V : RationalQuadraticSpaceMatrix n) (K : Type*) [CommRing K] [Algebra ℚ K]
    (M : V.specialOrthogonalMatrixPoint K) (x : Fin n → K) :
    (M.1 *ᵥ x) ⬝ᵥ (V.specialOrthogonalMappedFormMatrix K *ᵥ (M.1 *ᵥ x)) =
      x ⬝ᵥ (V.specialOrthogonalMappedFormMatrix K *ᵥ x) := by
  have hM := M.2.1
  calc (M.1 *ᵥ x) ⬝ᵥ (V.specialOrthogonalMappedFormMatrix K *ᵥ (M.1 *ᵥ x))
      = (M.1 *ᵥ x) ⬝ᵥ ((V.specialOrthogonalMappedFormMatrix K * M.1) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ (M.1ᵀ *ᵥ ((V.specialOrthogonalMappedFormMatrix K * M.1) *ᵥ x)) := by
        rw [Matrix.dotProduct_mulVec x M.1ᵀ
          ((V.specialOrthogonalMappedFormMatrix K * M.1) *ᵥ x), Matrix.vecMul_transpose]
    _ = x ⬝ᵥ ((M.1ᵀ * (V.specialOrthogonalMappedFormMatrix K * M.1)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ ((M.1ᵀ * V.specialOrthogonalMappedFormMatrix K * M.1) *ᵥ x) := by
        rw [mul_assoc]
    _ = x ⬝ᵥ (V.specialOrthogonalMappedFormMatrix K *ᵥ x) := by rw [hM]

/-- The adelic instance: the matrix action of a special-orthogonal point preserves the
full-adelic quadratic value. -/
theorem fullAdelicQuadraticFormValue_specialOrthogonalMatrixPoint
    (V : RationalQuadraticSpaceMatrix n)
    (M : V.specialOrthogonalMatrixPoint RationalAdele) (x : Fin n → RationalAdele) :
    V.fullAdelicQuadraticFormValue (M.1 *ᵥ x) = V.fullAdelicQuadraticFormValue x := by
  rw [V.fullAdelicQuadraticFormValue_eq_dotProduct,
    V.fullAdelicQuadraticFormValue_eq_dotProduct]
  exact V.specialOrthogonalMatrixPoint_dotProduct_mulVec RationalAdele M x

/-- The acting group preserves the value.  Every full-adelic `GSpin` point maps each fiber of
the adelic quadratic value into itself. -/
theorem fullAdelicQuadraticFormValue_cliffordGeneralSpin
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicCliffordGeneralSpinGroup) (x : Fin n → RationalAdele) :
    V.fullAdelicQuadraticFormValue (g.matrixPoint.1 *ᵥ x) =
      V.fullAdelicQuadraticFormValue x :=
  V.fullAdelicQuadraticFormValue_specialOrthogonalMatrixPoint g.matrixPoint x

/-- The same statement as a preimage identity: the value fibers are exactly preserved. -/
theorem preimage_fullAdelicQuadraticFormValue_cliffordGeneralSpin
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicCliffordGeneralSpinGroup) (s : Set RationalAdele) :
    (fun x : Fin n → RationalAdele => g.matrixPoint.1 *ᵥ x) ⁻¹'
        (V.fullAdelicQuadraticFormValue ⁻¹' s) =
      V.fullAdelicQuadraticFormValue ⁻¹' s := by
  ext x
  simp only [Set.mem_preimage]
  rw [V.fullAdelicQuadraticFormValue_cliffordGeneralSpin g x]

end RationalQuadraticSpaceMatrix

end
