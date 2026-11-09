import SMSFormula.RationalSpecialOrthogonalReduced
import SMSFormula.RationalCliffordSpinCandidatePointGroup

/-!
# Coordinate Hopf-data precursor for the affine Spin cover

The special-orthogonal and Clifford--Spin-candidate affine carriers were
bundled as group schemes by representability.  Their coordinate rings are
not bundled as mathlib `HopfAlgebra`s.  This file extracts the three
contravariant coordinate operations directly from the natural groups of
algebra-valued points:

```text
comultiplication = left universal point * right universal point,
counit            = the unit rational point,
antipode           = the inverse universal point.
```

It also proves that the already injective coordinate homomorphism

```text
O(SO_V) -> O(SpinCandidate_V)
```

commutes with all three operations.  Thus the exact remaining Hopf precursor
is to prove the coalgebra and antipode axioms for these explicit maps and
package the coordinate homomorphism as a `BialgHom`.  No faithful-flatness
claim is made here.
-/

noncomputable section

open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable instance specialOrthogonalCoordinateAlgHomGroup
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Group (V.specialOrthogonalCoordinateRing →ₐ[ℚ] A) :=
  Equiv.group ((V.specialOrthogonalCoordinateAlgHomEquivMatrixPoint A).trans
    (V.specialOrthogonalMatrixPointEquivGroup A))

def specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (V.specialOrthogonalCoordinateRing →ₐ[ℚ] A) ≃*
      V.specialOrthogonalMatrixGroup A :=
  Equiv.mulEquiv ((V.specialOrthogonalCoordinateAlgHomEquivMatrixPoint A).trans
    (V.specialOrthogonalMatrixPointEquivGroup A))

@[simp]
theorem specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_comp
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] A) :
    V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B (f.comp F) =
      V.specialOrthogonalMatrixGroupMap f
        (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A F) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

def specialOrthogonalCoordinateAlgHomMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    (V.specialOrthogonalCoordinateRing →ₐ[ℚ] A) →*
      (V.specialOrthogonalCoordinateRing →ₐ[ℚ] B) where
  toFun F := f.comp F
  map_one' := by
    apply (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B).injective
    calc
      V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B (f.comp 1) =
          V.specialOrthogonalMatrixGroupMap f
            (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A 1) :=
        V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_comp f 1
      _ = 1 := by rw [map_one, map_one]
      _ = V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B 1 :=
        (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B).map_one.symm
  map_mul' F G := by
    apply (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B).injective
    calc
      V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B (f.comp (F * G)) =
          V.specialOrthogonalMatrixGroupMap f
            (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A (F * G)) :=
        V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_comp f (F * G)
      _ = V.specialOrthogonalMatrixGroupMap f
          (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A F *
            V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A G) := by
        rw [map_mul]
      _ = V.specialOrthogonalMatrixGroupMap f
            (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A F) *
          V.specialOrthogonalMatrixGroupMap f
            (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A G) := by rw [map_mul]
      _ = V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B (f.comp F) *
          V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B (f.comp G) := by
        rw [V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_comp,
          V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_comp]
      _ = V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B
          (f.comp F * f.comp G) :=
        (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup B).map_mul _ _ |>.symm

@[simp]
theorem specialOrthogonalCoordinateAlgHomMap_apply
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] A) :
    V.specialOrthogonalCoordinateAlgHomMap f F = f.comp F := rfl

@[simp]
theorem specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (F : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) :
    V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A
        (F.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom) =
      V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalGroup A F := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

def cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] A) →*
      (V.specialOrthogonalCoordinateRing →ₐ[ℚ] A) where
  toFun F := F.comp V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
  map_one' := by
    apply (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A).injective
    rw [V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp,
      map_one, map_one]
  map_mul' F G := by
    apply (V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup A).injective
    rw [V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp,
      map_mul, map_mul,
      V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp,
      V.specialOrthogonalCoordinateAlgHomMulEquivMatrixGroup_candidateComp]

def specialOrthogonalCoordinateComul :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      V.specialOrthogonalCoordinateRing ⊗[ℚ]
        V.specialOrthogonalCoordinateRing := by
  letI := V.specialOrthogonalCoordinateAlgHomGroup
    (V.specialOrthogonalCoordinateRing ⊗[ℚ] V.specialOrthogonalCoordinateRing)
  exact ((Algebra.TensorProduct.includeLeft :
      V.specialOrthogonalCoordinateRing →ₐ[ℚ]
        V.specialOrthogonalCoordinateRing ⊗[ℚ]
          V.specialOrthogonalCoordinateRing) *
    (Algebra.TensorProduct.includeRight :
      V.specialOrthogonalCoordinateRing →ₐ[ℚ]
        V.specialOrthogonalCoordinateRing ⊗[ℚ]
          V.specialOrthogonalCoordinateRing) :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      V.specialOrthogonalCoordinateRing ⊗[ℚ]
        V.specialOrthogonalCoordinateRing)

def specialOrthogonalCoordinateCounit :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ] ℚ := 1

def specialOrthogonalCoordinateAntipode :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      V.specialOrthogonalCoordinateRing :=
  (AlgHom.id ℚ V.specialOrthogonalCoordinateRing)⁻¹

def cliffordSpinCandidateCoordinateComul :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
        V.cliffordSpinCandidateCoordinateRing := by
  letI := V.cliffordSpinCandidateCoordinateAlgHomGroup
    (V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
      V.cliffordSpinCandidateCoordinateRing)
  exact ((Algebra.TensorProduct.includeLeft :
      V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
        V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
          V.cliffordSpinCandidateCoordinateRing) *
    (Algebra.TensorProduct.includeRight :
      V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
        V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
          V.cliffordSpinCandidateCoordinateRing) :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
        V.cliffordSpinCandidateCoordinateRing)

def cliffordSpinCandidateCoordinateCounit :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] ℚ := 1

def cliffordSpinCandidateCoordinateAntipode :
    V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing :=
  (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)⁻¹

theorem cliffordSpinCandidateCoordinateCounit_comp :
    (V.cliffordSpinCandidateCoordinateCounit.comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom) =
        V.specialOrthogonalCoordinateCounit := by
  change (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom ℚ) 1 = 1
  exact map_one
    (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom ℚ)

theorem cliffordSpinCandidateCoordinateAntipode_comp :
    (V.cliffordSpinCandidateCoordinateAntipode.comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom) =
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.comp
          V.specialOrthogonalCoordinateAntipode := by
  let f := V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
  calc
    V.cliffordSpinCandidateCoordinateAntipode.comp f =
        ((V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom
          V.cliffordSpinCandidateCoordinateRing)
            (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing))⁻¹ := by
      exact map_inv
        (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom
        V.cliffordSpinCandidateCoordinateRing)
          (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
    _ = f⁻¹ := by rfl
    _ = f.comp V.specialOrthogonalCoordinateAntipode := by
      exact (map_inv (V.specialOrthogonalCoordinateAlgHomMap f)
        (AlgHom.id ℚ V.specialOrthogonalCoordinateRing)).symm

theorem tensorMap_specialOrthogonalCoordinateHom_includeLeft :
    (Algebra.TensorProduct.map
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom).comp
      (Algebra.TensorProduct.includeLeft :
        V.specialOrthogonalCoordinateRing →ₐ[ℚ]
          V.specialOrthogonalCoordinateRing ⊗[ℚ]
            V.specialOrthogonalCoordinateRing) =
    (Algebra.TensorProduct.includeLeft :
      V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
        V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
          V.cliffordSpinCandidateCoordinateRing).comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
  ext x
  simp

theorem tensorMap_specialOrthogonalCoordinateHom_includeRight :
    (Algebra.TensorProduct.map
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom).comp
      (Algebra.TensorProduct.includeRight :
        V.specialOrthogonalCoordinateRing →ₐ[ℚ]
          V.specialOrthogonalCoordinateRing ⊗[ℚ]
            V.specialOrthogonalCoordinateRing) =
    (Algebra.TensorProduct.includeRight :
      V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
        V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
          V.cliffordSpinCandidateCoordinateRing).comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
  ext x
  simp

theorem cliffordSpinCandidateCoordinateComul_comp :
    (V.cliffordSpinCandidateCoordinateComul.comp
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom) =
    (Algebra.TensorProduct.map
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom).comp
        V.specialOrthogonalCoordinateComul := by
  letI := V.cliffordSpinCandidateCoordinateAlgHomGroup
    (V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
      V.cliffordSpinCandidateCoordinateRing)
  letI := V.specialOrthogonalCoordinateAlgHomGroup
    (V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
      V.cliffordSpinCandidateCoordinateRing)
  letI := V.specialOrthogonalCoordinateAlgHomGroup
    (V.specialOrthogonalCoordinateRing ⊗[ℚ]
      V.specialOrthogonalCoordinateRing)
  let f := V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
  let lB : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
        V.cliffordSpinCandidateCoordinateRing :=
    Algebra.TensorProduct.includeLeft
  let rB : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
        V.cliffordSpinCandidateCoordinateRing :=
    Algebra.TensorProduct.includeRight
  let lA : V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      V.specialOrthogonalCoordinateRing ⊗[ℚ]
        V.specialOrthogonalCoordinateRing :=
    Algebra.TensorProduct.includeLeft
  let rA : V.specialOrthogonalCoordinateRing →ₐ[ℚ]
      V.specialOrthogonalCoordinateRing ⊗[ℚ]
        V.specialOrthogonalCoordinateRing :=
    Algebra.TensorProduct.includeRight
  let ff := Algebra.TensorProduct.map f f
  calc
    V.cliffordSpinCandidateCoordinateComul.comp f =
        (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom
          (V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
            V.cliffordSpinCandidateCoordinateRing)) (lB * rB) := rfl
    _ = (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom
          (V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
            V.cliffordSpinCandidateCoordinateRing)) lB *
        (V.cliffordSpinCandidateCoordinateAlgHomToSpecialOrthogonalAlgHom
          (V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
            V.cliffordSpinCandidateCoordinateRing)) rB := by rw [map_mul]
    _ = lB.comp f * rB.comp f := rfl
    _ = ff.comp lA * ff.comp rA := by
      rw [V.tensorMap_specialOrthogonalCoordinateHom_includeLeft,
        V.tensorMap_specialOrthogonalCoordinateHom_includeRight]
    _ = (V.specialOrthogonalCoordinateAlgHomMap
        (A := V.specialOrthogonalCoordinateRing ⊗[ℚ]
          V.specialOrthogonalCoordinateRing)
        (B := V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
          V.cliffordSpinCandidateCoordinateRing) ff) (lA * rA) :=
      (map_mul (V.specialOrthogonalCoordinateAlgHomMap
        (A := V.specialOrthogonalCoordinateRing ⊗[ℚ]
          V.specialOrthogonalCoordinateRing)
        (B := V.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
          V.cliffordSpinCandidateCoordinateRing) ff) lA rA).symm
    _ = ff.comp V.specialOrthogonalCoordinateComul := by rfl

end RationalQuadraticSpaceMatrix
