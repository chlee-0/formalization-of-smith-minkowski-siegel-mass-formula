import SMSFormula.AdelicProperFinitePresentation
import SMSFormula.SkewAdjointBaseChange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Cayley algebra over a commutative ring

This module isolates the ring-theoretic core of the matrix Cayley transform.
The denominator conditions are stated with `IsUnit`, so no field cancellation
or topological openness is used.  If `2` and the determinant of the form are
units, the transform gives an exact equivalence between its skew-adjoint
source and its special-orthogonal inverse domain.
-/

noncomputable section

open scoped Matrix

namespace Matrix

set_option maxHeartbeats 3000000

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The ambient Cayley source over a commutative ring. -/
def cayleyRingSource : Set (Matrix ι ι R) :=
  {X | IsUnit (1 - X)}

/-- The ambient inverse domain over a commutative ring. -/
def cayleyRingInverseDomain : Set (Matrix ι ι R) :=
  {g | IsUnit (g + 1)}

/-- The ambient forward Cayley formula. -/
def cayleyRingForwardMatrix (X : Matrix ι ι R) : Matrix ι ι R :=
  (1 + X) * (1 - X)⁻¹

/-- The ambient inverse Cayley formula. -/
def cayleyRingInverseMatrix (g : Matrix ι ι R) : Matrix ι ι R :=
  (g + 1)⁻¹ * (g - 1)

/-- The scalar matrix `2`. -/
def cayleyRingTwoMatrix : Matrix ι ι R :=
  Matrix.scalar ι 2

private theorem cayleyRing_two_isUnit (h2 : IsUnit (2 : R)) :
    IsUnit (cayleyRingTwoMatrix (ι := ι) (R := R)) :=
  h2.map (Matrix.scalar ι)

private theorem cayleyRing_nonsing_inv_commute
    (X : Matrix ι ι R) (hX : X ∈ cayleyRingSource) :
    (1 - X)⁻¹ * X = X * (1 - X)⁻¹ := by
  let A : Matrix ι ι R := 1 - X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  apply hX.mul_left_cancel
  calc
    A * (A⁻¹ * X) = X := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAdet, one_mul]
    _ = A * (X * A⁻¹) := by
      rw [← Matrix.mul_assoc]
      have hcomm : A * X = X * A := by
        dsimp [A]
        noncomm_ring
      rw [hcomm, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAdet, mul_one]

theorem cayleyRingForwardMatrix_add_one
    (X : Matrix ι ι R) (hX : X ∈ cayleyRingSource) :
    cayleyRingForwardMatrix X + 1 =
      cayleyRingTwoMatrix * (1 - X)⁻¹ := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  change B * A⁻¹ + 1 = cayleyRingTwoMatrix * A⁻¹
  have hBA : B + A = cayleyRingTwoMatrix (ι := ι) (R := R) := by
    calc
      B + A = (2 : R) • (1 : Matrix ι ι R) := by
        dsimp [A, B]
        module
      _ = cayleyRingTwoMatrix := by
        rw [smul_eq_diagonal_mul, Matrix.mul_one]
        rfl
  calc
    B * A⁻¹ + 1 = B * A⁻¹ + A * A⁻¹ := by
      rw [Matrix.mul_nonsing_inv A hAdet]
    _ = (B + A) * A⁻¹ := (add_mul B A A⁻¹).symm
    _ = cayleyRingTwoMatrix * A⁻¹ := by rw [hBA]

theorem cayleyRingForwardMatrix_sub_one
    (X : Matrix ι ι R) (hX : X ∈ cayleyRingSource) :
    cayleyRingForwardMatrix X - 1 =
      cayleyRingTwoMatrix * X * (1 - X)⁻¹ := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  change B * A⁻¹ - 1 = cayleyRingTwoMatrix * X * A⁻¹
  have hBA : B - A = cayleyRingTwoMatrix (ι := ι) (R := R) * X := by
    calc
      B - A = (2 : R) • X := by
        dsimp [A, B]
        module
      _ = cayleyRingTwoMatrix * X := by
        rw [smul_eq_diagonal_mul]
        rfl
  calc
    B * A⁻¹ - 1 = B * A⁻¹ - A * A⁻¹ := by
      rw [Matrix.mul_nonsing_inv A hAdet]
    _ = (B - A) * A⁻¹ := (sub_mul B A A⁻¹).symm
    _ = cayleyRingTwoMatrix * X * A⁻¹ := by rw [hBA]

theorem cayleyRingForwardMatrix_cross
    (X : Matrix ι ι R) (hX : X ∈ cayleyRingSource) :
    (cayleyRingForwardMatrix X + 1) * X =
      cayleyRingForwardMatrix X - 1 := by
  rw [cayleyRingForwardMatrix_add_one X hX,
    cayleyRingForwardMatrix_sub_one X hX]
  rw [Matrix.mul_assoc, cayleyRing_nonsing_inv_commute X hX,
    ← Matrix.mul_assoc]

theorem cayleyRingForwardMatrix_mem_inverseDomain
    (h2 : IsUnit (2 : R)) (X : Matrix ι ι R)
    (hX : X ∈ cayleyRingSource) :
    cayleyRingForwardMatrix X ∈ cayleyRingInverseDomain := by
  change IsUnit (cayleyRingForwardMatrix X + 1)
  rw [cayleyRingForwardMatrix_add_one X hX]
  exact (cayleyRing_two_isUnit h2).mul
    (Matrix.isUnit_nonsing_inv_iff.mpr hX)

theorem cayleyRingInverseMatrix_forward
    (h2 : IsUnit (2 : R)) (X : Matrix ι ι R)
    (hX : X ∈ cayleyRingSource) :
    cayleyRingInverseMatrix (cayleyRingForwardMatrix X) = X := by
  have hC := cayleyRingForwardMatrix_mem_inverseDomain h2 X hX
  have hCdet : IsUnit (cayleyRingForwardMatrix X + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hC
  rw [cayleyRingInverseMatrix, ← cayleyRingForwardMatrix_cross X hX,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCdet, one_mul]

theorem one_sub_cayleyRingInverseMatrix
    (g : Matrix ι ι R) (hg : g ∈ cayleyRingInverseDomain) :
    1 - cayleyRingInverseMatrix g =
      (g + 1)⁻¹ * cayleyRingTwoMatrix := by
  have hCdet : IsUnit (g + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hg
  rw [cayleyRingInverseMatrix]
  calc
    1 - (g + 1)⁻¹ * (g - 1) =
        (g + 1)⁻¹ * (g + 1) - (g + 1)⁻¹ * (g - 1) := by
      rw [Matrix.nonsing_inv_mul _ hCdet]
    _ = (g + 1)⁻¹ * ((g + 1) - (g - 1)) :=
      (mul_sub (g + 1)⁻¹ (g + 1) (g - 1)).symm
    _ = (g + 1)⁻¹ * cayleyRingTwoMatrix := by
      congr 1
      calc
        (g + 1) - (g - 1) = (2 : R) • (1 : Matrix ι ι R) := by module
        _ = cayleyRingTwoMatrix := by
          rw [smul_eq_diagonal_mul, Matrix.mul_one]
          rfl

theorem cayleyRingInverseMatrix_mem_source
    (h2 : IsUnit (2 : R)) (g : Matrix ι ι R)
    (hg : g ∈ cayleyRingInverseDomain) :
    cayleyRingInverseMatrix g ∈ cayleyRingSource := by
  change IsUnit (1 - cayleyRingInverseMatrix g)
  rw [one_sub_cayleyRingInverseMatrix g hg]
  exact (Matrix.isUnit_nonsing_inv_iff.mpr hg).mul
    (cayleyRing_two_isUnit h2)

theorem cayleyRingInverseMatrix_cross
    (g : Matrix ι ι R) (hg : g ∈ cayleyRingInverseDomain) :
    (g + 1) * cayleyRingInverseMatrix g = g - 1 := by
  have hCdet : IsUnit (g + 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hg
  rw [cayleyRingInverseMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hCdet, one_mul]

theorem cayleyRingForwardMatrix_inverse
    (h2 : IsUnit (2 : R)) (g : Matrix ι ι R)
    (hg : g ∈ cayleyRingInverseDomain) :
    cayleyRingForwardMatrix (cayleyRingInverseMatrix g) = g := by
  let X := cayleyRingInverseMatrix g
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hX : X ∈ cayleyRingSource :=
    cayleyRingInverseMatrix_mem_source h2 g hg
  have hAdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hcross : (g + 1) * X = g - 1 :=
    cayleyRingInverseMatrix_cross g hg
  have hgX : g * X = g - 1 - X := by
    calc
      g * X = (g + 1) * X - X := by noncomm_ring
      _ = g - 1 - X := by rw [hcross]
  have hrel : g * A = B := by
    dsimp [A, B]
    rw [mul_sub, mul_one, hgX]
    noncomm_ring
  change B * A⁻¹ = g
  rw [← hrel]
  exact Matrix.mul_nonsing_inv_cancel_right A g hAdet

/-- The skew-adjoint Cayley source for a form over the same ring. -/
def skewAdjointCayleyRingSource (F : Matrix ι ι R) :
    Set ((skewAdjointMatricesLieSubalgebra F).toSubmodule) :=
  {X | (X : Matrix ι ι R) ∈ cayleyRingSource}

theorem skewAdjointCayleyRing_numerator_form_eq
    (F : Matrix ι ι R)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
    (1 + (X : Matrix ι ι R))ᵀ * F *
        (1 + (X : Matrix ι ι R)) =
      (1 - (X : Matrix ι ι R))ᵀ * F *
        (1 - (X : Matrix ι ι R)) := by
  let Xm : Matrix ι ι R := X
  have hker : skewAdjointOperator F Xm = 0 :=
    LinearMap.mem_ker.mp ((mem_ker_skewAdjointOperator_iff F Xm).mpr X.property)
  have hskew : Xmᵀ * F = -(F * Xm) :=
    eq_neg_of_add_eq_zero_left hker
  change (1 + Xm)ᵀ * F * (1 + Xm) = (1 - Xm)ᵀ * F * (1 - Xm)
  rw [Matrix.transpose_add, Matrix.transpose_sub]
  simp only [Matrix.transpose_one]
  rw [show (1 + Xmᵀ) * F * (1 + Xm) = F + Xmᵀ * F * Xm by
    calc
      _ = F + Xmᵀ * F + F * Xm + Xmᵀ * F * Xm := by noncomm_ring
      _ = F + Xmᵀ * F * Xm := by rw [hskew]; noncomm_ring]
  calc
    F + Xmᵀ * F * Xm =
        (1 - Xmᵀ) * F * (1 - Xm) := by
      calc
        _ = F - Xmᵀ * F - F * Xm + Xmᵀ * F * Xm := by
          rw [hskew]
          noncomm_ring
        _ = _ := by noncomm_ring

theorem skewAdjointCayleyRingForwardMatrix_formPreserving
    (F : Matrix ι ι R)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hX : (X : Matrix ι ι R) ∈ cayleyRingSource) :
    (cayleyRingForwardMatrix (X : Matrix ι ι R))ᵀ * F *
        cayleyRingForwardMatrix (X : Matrix ι ι R) = F := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hAtdet : IsUnit Aᵀ.det := by simpa using hAdet
  have hnum : Bᵀ * F * B = Aᵀ * F * A :=
    skewAdjointCayleyRing_numerator_form_eq F X
  change (B * A⁻¹)ᵀ * F * (B * A⁻¹) = F
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc
    (Aᵀ)⁻¹ * Bᵀ * F * (B * A⁻¹) =
        (Aᵀ)⁻¹ * (Bᵀ * F * B) * A⁻¹ := by noncomm_ring
    _ = (Aᵀ)⁻¹ * (Aᵀ * F * A) * A⁻¹ := by rw [hnum]
    _ = ((Aᵀ)⁻¹ * Aᵀ) * F * (A * A⁻¹) := by noncomm_ring
    _ = F := by
      rw [Matrix.nonsing_inv_mul Aᵀ hAtdet,
        Matrix.mul_nonsing_inv A hAdet, one_mul, Matrix.mul_one]

theorem skewAdjointCayleyRing_numerator_intertwines
    (F : Matrix ι ι R)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
    (1 + (X : Matrix ι ι R))ᵀ * F =
      F * (1 - (X : Matrix ι ι R)) := by
  let Xm : Matrix ι ι R := X
  have hker : skewAdjointOperator F Xm = 0 :=
    LinearMap.mem_ker.mp ((mem_ker_skewAdjointOperator_iff F Xm).mpr X.property)
  have hskew : Xmᵀ * F = -(F * Xm) :=
    eq_neg_of_add_eq_zero_left hker
  change (1 + Xm)ᵀ * F = F * (1 - Xm)
  rw [Matrix.transpose_add]
  simp only [Matrix.transpose_one]
  calc
    (1 + Xmᵀ) * F = F + Xmᵀ * F := by noncomm_ring
    _ = F - F * Xm := by rw [hskew]; noncomm_ring
    _ = F * (1 - Xm) := by noncomm_ring

theorem skewAdjointCayleyRing_det_one_add_eq_det_one_sub
    (F : Matrix ι ι R) (hF : IsUnit F.det)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
    (1 + (X : Matrix ι ι R)).det =
      (1 - (X : Matrix ι ι R)).det := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hintertwines : Bᵀ * F = F * A :=
    skewAdjointCayleyRing_numerator_intertwines F X
  have hdet := congrArg Matrix.det hintertwines
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  change B.det = A.det
  apply hF.mul_right_cancel
  calc
    B.det * F.det = F.det * A.det := hdet
    _ = A.det * F.det := mul_comm _ _

theorem skewAdjointCayleyRingForwardMatrix_det_one
    (F : Matrix ι ι R) (hF : IsUnit F.det)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hX : (X : Matrix ι ι R) ∈ cayleyRingSource) :
    (cayleyRingForwardMatrix (X : Matrix ι ι R)).det = 1 := by
  let A : Matrix ι ι R := 1 - X
  let B : Matrix ι ι R := 1 + X
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hX
  have hBA : B.det = A.det :=
    skewAdjointCayleyRing_det_one_add_eq_det_one_sub F hF X
  change (B * A⁻¹).det = 1
  rw [Matrix.det_mul, hBA, mul_comm]
  exact Matrix.det_nonsing_inv_mul_det A hAdet

/-- The Cayley forward map into the matrix-valued special orthogonal carrier. -/
def skewAdjointCayleyRingSpecialOrthogonal
    (F : Matrix ι ι R) (hF : IsUnit F.det) :
    skewAdjointCayleyRingSource F → specialOrthogonalMatrixSet F :=
  fun X ↦
    ⟨cayleyRingForwardMatrix (X.1 : Matrix ι ι R),
      (formPreservingConstraint_eq_zero_iff _ _).mpr
        (skewAdjointCayleyRingForwardMatrix_formPreserving F X.1 X.2),
      skewAdjointCayleyRingForwardMatrix_det_one F hF X.1 X.2⟩

/-- The inverse domain restricted to the special-orthogonal carrier. -/
def cayleyRingSpecialOrthogonalInverseDomain (F : Matrix ι ι R) :
    Set (specialOrthogonalMatrixSet F) :=
  {g | (g : Matrix ι ι R) ∈ cayleyRingInverseDomain}

theorem cayleyRingInverseMatrix_cross_right
    (g : Matrix ι ι R) (hg : g ∈ cayleyRingInverseDomain) :
    cayleyRingInverseMatrix g * (g + 1) = g - 1 := by
  let C : Matrix ι ι R := g + 1
  let D : Matrix ι ι R := g - 1
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hg
  change (C⁻¹ * D) * C = D
  calc
    (C⁻¹ * D) * C = C⁻¹ * (D * C) := by rw [Matrix.mul_assoc]
    _ = C⁻¹ * (C * D) := by congr 1; dsimp [C, D]; noncomm_ring
    _ = (C⁻¹ * C) * D := by rw [Matrix.mul_assoc]
    _ = D := by rw [Matrix.nonsing_inv_mul C hCdet, one_mul]

theorem skewAdjointOperator_cayleyRingInverseMatrix_eq_zero
    (F : Matrix ι ι R) (g : specialOrthogonalMatrixSet F)
    (hg : (g : Matrix ι ι R) ∈ cayleyRingInverseDomain) :
    skewAdjointOperator F (cayleyRingInverseMatrix (g : Matrix ι ι R)) = 0 := by
  let gm : Matrix ι ι R := g
  let C : Matrix ι ι R := gm + 1
  let D : Matrix ι ι R := gm - 1
  let X : Matrix ι ι R := cayleyRingInverseMatrix gm
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hg
  have hCtdet : IsUnit Cᵀ.det := by simpa using hCdet
  have hcross : X * C = D := cayleyRingInverseMatrix_cross_right gm hg
  have hcrossT : Cᵀ * Xᵀ = Dᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hcross
  have hform : gmᵀ * F * gm = F :=
    (formPreservingConstraint_eq_zero_iff F gm).mp g.property.1
  have hcleared : Cᵀ * (Xᵀ * F + F * X) * C = 0 := by
    calc
      Cᵀ * (Xᵀ * F + F * X) * C =
          (Cᵀ * Xᵀ) * F * C + Cᵀ * F * (X * C) := by noncomm_ring
      _ = Dᵀ * F * C + Cᵀ * F * D := by rw [hcrossT, hcross]
      _ = 0 := by
        dsimp [C, D]
        rw [Matrix.transpose_add, Matrix.transpose_sub]
        simp only [Matrix.transpose_one]
        calc
          (gmᵀ - 1) * F * (gm + 1) + (gmᵀ + 1) * F * (gm - 1) =
              (gmᵀ * F * gm - F) + (gmᵀ * F * gm - F) := by noncomm_ring
          _ = 0 := by rw [hform]; simp
  change Xᵀ * F + F * X = 0
  calc
    Xᵀ * F + F * X =
        ((Cᵀ)⁻¹ * Cᵀ) * (Xᵀ * F + F * X) * (C * C⁻¹) := by
      rw [Matrix.nonsing_inv_mul Cᵀ hCtdet,
        Matrix.mul_nonsing_inv C hCdet, one_mul, Matrix.mul_one]
    _ = (Cᵀ)⁻¹ * (Cᵀ * (Xᵀ * F + F * X) * C) * C⁻¹ := by noncomm_ring
    _ = 0 := by rw [hcleared, Matrix.mul_zero, Matrix.zero_mul]

/-- The exact ring-level Cayley equivalence. -/
def skewAdjointCayleyRingForwardTarget
    (F : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hF : IsUnit F.det) :
    skewAdjointCayleyRingSource F →
      cayleyRingSpecialOrthogonalInverseDomain F :=
  fun X ↦
    ⟨skewAdjointCayleyRingSpecialOrthogonal F hF X, by
      change cayleyRingForwardMatrix (X.1 : Matrix ι ι R) ∈
        cayleyRingInverseDomain
      have hX : (X.1 : Matrix ι ι R) ∈ cayleyRingSource := X.2
      exact cayleyRingForwardMatrix_mem_inverseDomain h2
        (X.1 : Matrix ι ι R) hX⟩

def skewAdjointCayleyRingInverseSource
    (F : Matrix ι ι R) (h2 : IsUnit (2 : R)) :
    cayleyRingSpecialOrthogonalInverseDomain F →
      skewAdjointCayleyRingSource F :=
  fun g ↦
    ⟨⟨cayleyRingInverseMatrix (g.1 : Matrix ι ι R),
        (mem_ker_skewAdjointOperator_iff _ _).mp
          (skewAdjointOperator_cayleyRingInverseMatrix_eq_zero F g.1
            (show (g.1 : Matrix ι ι R) ∈ cayleyRingInverseDomain from g.2))⟩,
      by
        change cayleyRingInverseMatrix (g.1 : Matrix ι ι R) ∈
          cayleyRingSource
        exact cayleyRingInverseMatrix_mem_source h2
          (g.1 : Matrix ι ι R)
          (show (g.1 : Matrix ι ι R) ∈ cayleyRingInverseDomain from g.2)⟩

def skewAdjointCayleyRingEquivSpecialOrthogonal
    (F : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hF : IsUnit F.det) :
    skewAdjointCayleyRingSource F ≃
      cayleyRingSpecialOrthogonalInverseDomain F where
  toFun := skewAdjointCayleyRingForwardTarget F h2 hF
  invFun := skewAdjointCayleyRingInverseSource F h2
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact cayleyRingInverseMatrix_forward h2 (X.1 : Matrix ι ι R)
      (show (X.1 : Matrix ι ι R) ∈ cayleyRingSource from X.2)
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact cayleyRingForwardMatrix_inverse h2 (g.1 : Matrix ι ι R)
      (show (g.1 : Matrix ι ι R) ∈ cayleyRingInverseDomain from g.2)

@[simp]
theorem coe_skewAdjointCayleyRingEquivSpecialOrthogonal_apply
    (F : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hF : IsUnit F.det)
    (X : skewAdjointCayleyRingSource F) :
    ((skewAdjointCayleyRingEquivSpecialOrthogonal F h2 hF X).1 :
      Matrix ι ι R) =
        (1 + (X.1 : Matrix ι ι R)) *
          (1 - (X.1 : Matrix ι ι R))⁻¹ :=
  rfl

@[simp]
theorem coe_skewAdjointCayleyRingEquivSpecialOrthogonal_symm_apply
    (F : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hF : IsUnit F.det)
    (g : cayleyRingSpecialOrthogonalInverseDomain F) :
    (((skewAdjointCayleyRingEquivSpecialOrthogonal F h2 hF).symm g).1 :
      Matrix ι ι R) =
        ((g.1 : Matrix ι ι R) + 1)⁻¹ * ((g.1 : Matrix ι ι R) - 1) := by
  change cayleyRingInverseMatrix (g.1 : Matrix ι ι R) =
    ((g.1 : Matrix ι ι R) + 1)⁻¹ * ((g.1 : Matrix ι ι R) - 1)
  rfl

end Matrix
