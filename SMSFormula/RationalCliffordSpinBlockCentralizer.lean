import SMSFormula.RationalCliffordSpinBlockInjectivity
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Centralizer of the added nonisotropic Clifford generator

This file identifies the even Clifford elements in a nonsingular one-line
extension which commute with the added generator.  The result is the exact
image of the complement Clifford algebra.  Intrinsic Spin and general-Spin
point reconstruction is deliberately left to the next layer.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[simp]
theorem scalarPart_algebraMap
    (Q : QuadraticForm R M) [Invertible (2 : R)] (r : R) :
    scalarPart Q (algebraMap R _ r) = r := by
  simp [scalarPart, ExteriorAlgebra.algebraMapInv]

@[simp]
theorem scalarPart_ι
    (Q : QuadraticForm R M) [Invertible (2 : R)] (m : M) :
    scalarPart Q (CliffordAlgebra.ι Q m) = 0 := by
  simp [scalarPart, ExteriorAlgebra.algebraMapInv]

@[simp]
theorem toProd_tmul_one
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.toProd Q₁ Q₂
        (x ᵍ⊗ₜ (1 : CliffordAlgebra Q₂)) =
      CliffordAlgebra.map (QuadraticMap.Isometry.inl Q₁ Q₂) x := by
  change
    ((CliffordAlgebra.toProd Q₁ Q₂).comp
      (GradedTensorProduct.includeLeft
        (CliffordAlgebra.evenOdd Q₁)
        (CliffordAlgebra.evenOdd Q₂))) x = _
  congr 1
  apply CliffordAlgebra.hom_ext
  ext v
  simp

@[simp]
theorem toProd_one_tmul
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (y : CliffordAlgebra Q₂) :
    CliffordAlgebra.toProd Q₁ Q₂
        ((1 : CliffordAlgebra Q₁) ᵍ⊗ₜ y) =
      CliffordAlgebra.map (QuadraticMap.Isometry.inr Q₁ Q₂) y := by
  change
    ((CliffordAlgebra.toProd Q₁ Q₂).comp
      (GradedTensorProduct.includeRight
        (CliffordAlgebra.evenOdd Q₁)
        (CliffordAlgebra.evenOdd Q₂))) y = _
  congr 1
  apply CliffordAlgebra.hom_ext
  ext v
  simp

@[simp]
theorem toProd_tmul
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (x : CliffordAlgebra Q₁) (y : CliffordAlgebra Q₂) :
    CliffordAlgebra.toProd Q₁ Q₂ (x ᵍ⊗ₜ y) =
      CliffordAlgebra.map (QuadraticMap.Isometry.inl Q₁ Q₂) x *
        CliffordAlgebra.map (QuadraticMap.Isometry.inr Q₁ Q₂) y := by
  rw [← GradedTensorProduct.tmul_one_mul_one_tmul,
    map_mul, toProd_tmul_one, toProd_one_tmul]

end CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Every element of the Clifford algebra of the added line has the expected
rank-two form. -/
theorem nonisotropicLastLineClifford_exists_normalForm
    (a : ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (nonisotropicLastLineQuadraticForm a A)) :
    ∃ r s : A,
      x = algebraMap A _ r +
        algebraMap A _ s *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1 := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      exact ⟨r, 0, by simp⟩
  | ι r =>
      exact ⟨0, r, by
        simpa [Algebra.smul_def] using
          (map_smul
            (CliffordAlgebra.ι
              (nonisotropicLastLineQuadraticForm a A)) r (1 : A))⟩
  | add x y hx hy =>
      obtain ⟨rx, sx, rfl⟩ := hx
      obtain ⟨ry, sy, rfl⟩ := hy
      refine ⟨rx + ry, sx + sy, ?_⟩
      simp only [map_add, add_mul]
      abel
  | mul x y hx hy =>
      obtain ⟨rx, sx, rfl⟩ := hx
      obtain ⟨ry, sy, rfl⟩ := hy
      refine ⟨rx * ry + sx * sy * algebraMap ℚ A a,
        rx * sy + sx * ry, ?_⟩
      let e := CliffordAlgebra.ι
        (nonisotropicLastLineQuadraticForm a A) 1
      have hry : e * algebraMap A _ ry = algebraMap A _ ry * e :=
        (Algebra.commutes ry e).symm
      have hsy : e * algebraMap A _ sy = algebraMap A _ sy * e :=
        (Algebra.commutes sy e).symm
      have he : e * e = algebraMap A _ (algebraMap ℚ A a) := by
        simpa [e, nonisotropicLastLineQuadraticForm_apply] using
          (CliffordAlgebra.ι_sq_scalar
            (nonisotropicLastLineQuadraticForm a A) (1 : A))
      change
        (algebraMap A _ rx + algebraMap A _ sx * e) *
            (algebraMap A _ ry + algebraMap A _ sy * e) = _
      simp only [add_mul, mul_add]
      rw [mul_assoc (algebraMap A _ sx) e (algebraMap A _ ry), hry,
        ← mul_assoc (algebraMap A _ sx) (algebraMap A _ ry) e]
      rw [mul_assoc (algebraMap A _ sx) e
        (algebraMap A _ sy * e),
        ← mul_assoc e (algebraMap A _ sy) e, hsy,
        mul_assoc (algebraMap A _ sy) e e, he]
      simp only [map_add, map_mul]
      noncomm_ring

@[simp]
theorem nonisotropicLastLineClifford_scalarPart_normalForm
    (a : ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A] [Invertible (2 : A)]
    (r s : A) :
    CliffordAlgebra.scalarPart (nonisotropicLastLineQuadraticForm a A)
        (algebraMap A _ r + algebraMap A _ s *
      CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) = r := by
  have hs :
      algebraMap A
          (CliffordAlgebra (nonisotropicLastLineQuadraticForm a A)) s *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1 =
        CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) s := by
    simpa [Algebra.smul_def] using
      (map_smul
        (CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A)) s (1 : A))
        |>.symm
  rw [hs]
  simp

@[simp]
theorem nonisotropicLastLineClifford_scalarPart_normalForm_mul_generator
    (a : ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A] [Invertible (2 : A)]
    (r s : A) :
    CliffordAlgebra.scalarPart (nonisotropicLastLineQuadraticForm a A)
        ((algebraMap A _ r + algebraMap A _ s *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) *
            CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) =
      s * algebraMap ℚ A a := by
  let QL := nonisotropicLastLineQuadraticForm a A
  let e : CliffordAlgebra QL := CliffordAlgebra.ι QL 1
  have hr : algebraMap A (CliffordAlgebra QL) r * e =
      CliffordAlgebra.ι QL r := by
    simpa [e, QL, Algebra.smul_def] using
      (map_smul (CliffordAlgebra.ι QL) r (1 : A)).symm
  have he : e * e = algebraMap A (CliffordAlgebra QL) (algebraMap ℚ A a) := by
    simpa [e, QL, nonisotropicLastLineQuadraticForm_apply] using
      (CliffordAlgebra.ι_sq_scalar QL (1 : A))
  change CliffordAlgebra.scalarPart QL
    ((algebraMap A _ r + algebraMap A _ s * e) * e) = _
  rw [add_mul, hr, mul_assoc, he,
    ← map_mul (algebraMap A (CliffordAlgebra QL)) s (algebraMap ℚ A a)]
  rw [map_add, CliffordAlgebra.scalarPart_ι,
    CliffordAlgebra.scalarPart_algebraMap]
  simp

/-- Coefficient of the added Clifford generator in the unique rank-two
normal form. -/
def nonisotropicLastLineCliffordGeneratorPart
    (a : ℚ) (_ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    CliffordAlgebra (nonisotropicLastLineQuadraticForm a A) →ₗ[A] A := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let QL := nonisotropicLastLineQuadraticForm a A
  let e : CliffordAlgebra QL := CliffordAlgebra.ι QL 1
  exact
    { toFun := fun x => algebraMap ℚ A a⁻¹ *
        CliffordAlgebra.scalarPart QL (x * e)
      map_add' := fun x y => by simp [add_mul, mul_add]
      map_smul' := fun r x => by
        have hinner :
            CliffordAlgebra.scalarPart QL
                (algebraMap A _ r * (x * e)) =
              r * CliffordAlgebra.scalarPart QL (x * e) := by
          rw [← Algebra.smul_def, map_smul]
          rfl
        change algebraMap ℚ A a⁻¹ *
            CliffordAlgebra.scalarPart QL ((algebraMap A _ r * x) * e) =
          r * (algebraMap ℚ A a⁻¹ *
            CliffordAlgebra.scalarPart QL (x * e))
        rw [mul_assoc (algebraMap A _ r) x e, hinner]
        ring }

@[simp]
theorem nonisotropicLastLineCliffordGeneratorPart_normalForm
    (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (r s : A) :
    nonisotropicLastLineCliffordGeneratorPart a ha A
        (algebraMap A _ r + algebraMap A _ s *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) = s := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  rw [nonisotropicLastLineCliffordGeneratorPart]
  change algebraMap ℚ A a⁻¹ *
      CliffordAlgebra.scalarPart (nonisotropicLastLineQuadraticForm a A)
        ((algebraMap A _ r + algebraMap A _ s *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) *
            CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) = s
  rw [nonisotropicLastLineClifford_scalarPart_normalForm_mul_generator]
  calc
    algebraMap ℚ A a⁻¹ * (s * algebraMap ℚ A a) =
        s * (algebraMap ℚ A a⁻¹ * algebraMap ℚ A a) := by ring
    _ = s := by rw [← map_mul]; simp [ha]

/-- The rank-two normal-form map for the added one-dimensional Clifford
algebra. -/
def nonisotropicLastLineCliffordNormalFormLinearMap
    (a : ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (A × A) →ₗ[A]
      CliffordAlgebra (nonisotropicLastLineQuadraticForm a A) where
  toFun p := algebraMap A _ p.1 + algebraMap A _ p.2 *
    CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul]
    abel
  map_smul' r p := by
    change
      algebraMap A _ (r * p.1) + algebraMap A _ (r * p.2) *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1 =
        algebraMap A _ r *
          (algebraMap A _ p.1 + algebraMap A _ p.2 *
            CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1)
    simp only [mul_add, map_mul, mul_assoc]

theorem nonisotropicLastLineCliffordNormalFormLinearMap_bijective
    (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Bijective
      (nonisotropicLastLineCliffordNormalFormLinearMap a A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  constructor
  · intro p q hpq
    apply Prod.ext
    · have h := congrArg
        (CliffordAlgebra.scalarPart
          (nonisotropicLastLineQuadraticForm a A)) hpq
      simpa [nonisotropicLastLineCliffordNormalFormLinearMap] using h
    · have h := congrArg
        (nonisotropicLastLineCliffordGeneratorPart a ha A) hpq
      simpa [nonisotropicLastLineCliffordNormalFormLinearMap] using h
  · intro x
    obtain ⟨r, s, hrs⟩ :=
      nonisotropicLastLineClifford_exists_normalForm a A x
    exact ⟨(r, s), by
      simpa [nonisotropicLastLineCliffordNormalFormLinearMap] using hrs.symm⟩

/-- Linear coordinates `scalar + generator` on the Clifford algebra of the
added line. -/
def nonisotropicLastLineCliffordNormalFormLinearEquiv
    (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (A × A) ≃ₗ[A]
      CliffordAlgebra (nonisotropicLastLineQuadraticForm a A) :=
  LinearEquiv.ofBijective
    (nonisotropicLastLineCliffordNormalFormLinearMap a A)
    (nonisotropicLastLineCliffordNormalFormLinearMap_bijective a ha A)

@[simp]
theorem nonisotropicLastLineCliffordNormalFormLinearEquiv_apply
    (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (p : A × A) :
    nonisotropicLastLineCliffordNormalFormLinearEquiv a ha A p =
      algebraMap A _ p.1 + algebraMap A _ p.2 *
        CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1 :=
  rfl

@[simp]
theorem nonisotropicLastLineCliffordNormalFormLinearEquiv_symm_normalForm
    (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (r s : A) :
    (nonisotropicLastLineCliffordNormalFormLinearEquiv a ha A).symm
      (algebraMap A _ r + algebraMap A _ s *
          CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1) =
      (r, s) := by
  rw [LinearEquiv.symm_apply_eq]
  rfl

/-- Split the graded tensor-product description of the block Clifford algebra
into its two coefficients along the added line. -/
def nonisotropicLastProductGradedTensorNormalFormLinearEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (CliffordAlgebra.evenOdd
        (W.commutativeScalarExtensionQuadraticForm A) ᵍ⊗[A]
      CliffordAlgebra.evenOdd
        (nonisotropicLastLineQuadraticForm a A)) ≃ₗ[A]
      (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A) ×
        CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :=
  (GradedTensorProduct.of A
      (CliffordAlgebra.evenOdd
        (W.commutativeScalarExtensionQuadraticForm A))
      (CliffordAlgebra.evenOdd
        (nonisotropicLastLineQuadraticForm a A))).symm |>.trans
    ((TensorProduct.congr
      (LinearEquiv.refl A
        (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)))
      (nonisotropicLastLineCliffordNormalFormLinearEquiv a ha A).symm).trans
      ((TensorProduct.prodRight A A
        (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) A A).trans
        ((TensorProduct.rid A
          (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A))).prodCongr
        (TensorProduct.rid A
          (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A))))))

@[simp]
theorem nonisotropicLastProductGradedTensorNormalFormLinearEquiv_tmul_normalForm
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A))
    (r s : A) :
    W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv a ha A
        (x ᵍ⊗ₜ
          (algebraMap A _ r + algebraMap A _ s *
            CliffordAlgebra.ι (nonisotropicLastLineQuadraticForm a A) 1)) =
      (r • x, s • x) := by
  simp [nonisotropicLastProductGradedTensorNormalFormLinearEquiv]

@[simp]
theorem nonisotropicLastProductGradedTensorNormalFormLinearEquiv_symm_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    (W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv a ha A).symm
        (x, y) =
      x ᵍ⊗ₜ (1 : CliffordAlgebra
        (nonisotropicLastLineQuadraticForm a A)) +
      y ᵍ⊗ₜ CliffordAlgebra.ι
        (nonisotropicLastLineQuadraticForm a A) 1 := by
  apply (W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv
    a ha A).injective
  rw [LinearEquiv.apply_symm_apply, map_add]
  have hx :
      W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv a ha A
          (x ᵍ⊗ₜ (1 : CliffordAlgebra
            (nonisotropicLastLineQuadraticForm a A))) = (x, 0) := by
    convert
      W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv_tmul_normalForm
        a ha A x 1 0 using 1 <;> simp
  have hy :
      W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv a ha A
          (y ᵍ⊗ₜ CliffordAlgebra.ι
            (nonisotropicLastLineQuadraticForm a A) 1) = (0, y) := by
    convert
      W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv_tmul_normalForm
        a ha A y 0 1 using 1 <;> simp
  rw [hx, hy]
  simp

/-- Exact two-coefficient normal form for the Clifford algebra of the
nonsingular block extension. -/
def nonisotropicLastBlockCliffordNormalFormLinearEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A) ×
      CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) ≃ₗ[A]
      CliffordAlgebra
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A) :=
  (W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv a ha A).symm |>.trans
    ((CliffordAlgebra.prodEquiv
      (W.commutativeScalarExtensionQuadraticForm A)
      (nonisotropicLastLineQuadraticForm a A)).symm.toLinearEquiv.trans
      (CliffordAlgebra.equivOfIsometry
        (W.nonisotropicLastProductIsometryEquiv a ha A)).toLinearEquiv)

@[simp]
theorem equivOfNonisotropicLastProductIsometry_map_inl
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    CliffordAlgebra.equivOfIsometry
        (W.nonisotropicLastProductIsometryEquiv a ha A)
        (CliffordAlgebra.map
          (QuadraticMap.Isometry.inl
            (W.commutativeScalarExtensionQuadraticForm A)
            (nonisotropicLastLineQuadraticForm a A)) x) =
      W.nonisotropicLastComplementCliffordMap a ha A x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
      rw [CliffordAlgebra.map_apply_ι]
      change CliffordAlgebra.map
          (W.nonisotropicLastProductIsometryEquiv a ha A).toIsometry
          (CliffordAlgebra.ι
            ((W.commutativeScalarExtensionQuadraticForm A).prod
              (nonisotropicLastLineQuadraticForm a A)) (v, 0)) = _
      rw [CliffordAlgebra.map_apply_ι]
      rw [W.nonisotropicLastComplementCliffordMap_ι]
      congr 1
      ext i
      cases i using Fin.lastCases <;> simp
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]

@[simp]
theorem equivOfNonisotropicLastProductIsometry_map_inr_generator
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    CliffordAlgebra.equivOfIsometry
        (W.nonisotropicLastProductIsometryEquiv a ha A)
        (CliffordAlgebra.map
          (QuadraticMap.Isometry.inr
            (W.commutativeScalarExtensionQuadraticForm A)
            (nonisotropicLastLineQuadraticForm a A))
          (CliffordAlgebra.ι
            (nonisotropicLastLineQuadraticForm a A) 1)) =
      CliffordAlgebra.ι
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
        (lastCoordinateVector (n := n)) := by
  rw [CliffordAlgebra.map_apply_ι]
  change CliffordAlgebra.map
      (W.nonisotropicLastProductIsometryEquiv a ha A).toIsometry
      (CliffordAlgebra.ι
        ((W.commutativeScalarExtensionQuadraticForm A).prod
          (nonisotropicLastLineQuadraticForm a A)) (0, 1)) = _
  rw [CliffordAlgebra.map_apply_ι]
  change CliffordAlgebra.ι
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
      (W.nonisotropicLastProductIsometryEquiv a ha A (0, 1)) = _
  congr 1
  ext i
  cases i using Fin.lastCases <;> simp [lastCoordinateVector]

@[simp]
theorem nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A (x, y) =
      W.nonisotropicLastComplementCliffordMap a ha A x +
      W.nonisotropicLastComplementCliffordMap a ha A y *
          CliffordAlgebra.ι
            ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
            (lastCoordinateVector (n := n)) := by
  rw [nonisotropicLastBlockCliffordNormalFormLinearEquiv]
  change CliffordAlgebra.equivOfIsometry
      (W.nonisotropicLastProductIsometryEquiv a ha A)
      ((CliffordAlgebra.prodEquiv
        (W.commutativeScalarExtensionQuadraticForm A)
        (nonisotropicLastLineQuadraticForm a A)).symm
        ((W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv
          a ha A).symm (x, y))) = _
  rw [W.nonisotropicLastProductGradedTensorNormalFormLinearEquiv_symm_apply]
  rw [map_add]
  change CliffordAlgebra.equivOfIsometry
      (W.nonisotropicLastProductIsometryEquiv a ha A)
      (CliffordAlgebra.toProd
          (W.commutativeScalarExtensionQuadraticForm A)
          (nonisotropicLastLineQuadraticForm a A)
          (x ᵍ⊗ₜ (1 : CliffordAlgebra
            (nonisotropicLastLineQuadraticForm a A))) +
        CliffordAlgebra.toProd
          (W.commutativeScalarExtensionQuadraticForm A)
          (nonisotropicLastLineQuadraticForm a A)
          (y ᵍ⊗ₜ CliffordAlgebra.ι
            (nonisotropicLastLineQuadraticForm a A) 1)) = _
  rw [CliffordAlgebra.toProd_tmul_one, CliffordAlgebra.toProd_tmul,
    map_add, map_mul]
  rw [W.equivOfNonisotropicLastProductIsometry_map_inl a ha A]
  rw [W.equivOfNonisotropicLastProductIsometry_map_inl a ha A,
    W.equivOfNonisotropicLastProductIsometry_map_inr_generator a ha A]

/-- Moving the added generator past an arbitrary complement Clifford element
applies the grading involution. -/
theorem nonisotropicLastGenerator_mul_complementCliffordMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    CliffordAlgebra.ι
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
        (lastCoordinateVector (n := n)) *
        W.nonisotropicLastComplementCliffordMap a ha A x =
      W.nonisotropicLastComplementCliffordMap a ha A
          (CliffordAlgebra.involute x) *
        CliffordAlgebra.ι
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
          (lastCoordinateVector (n := n)) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      have hmap :
          W.nonisotropicLastComplementCliffordMap a ha A
              (algebraMap A _ r) = algebraMap A _ r := by simp
      have hinv : CliffordAlgebra.involute
          (algebraMap A
            (CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) r) =
          algebraMap A _ r := by simp
      rw [hmap, hinv, hmap]
      exact (Algebra.commutes r _).symm
  | ι v =>
      rw [W.nonisotropicLastComplementCliffordMap_ι]
      have hline : lastCoordinateVector (n := n) =
          nonisotropicLastLineInclude (n := n) (1 : A) := by
        ext i
        cases i using Fin.lastCases <;> simp [lastCoordinateVector]
      have hortho :=
        W.nonisotropicLastComplement_line_isOrtho a ha A v (1 : A)
      change
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A).IsOrtho
          (nonisotropicLastComplementInclude v)
          (nonisotropicLastLineInclude (n := n) (1 : A)) at hortho
      rw [hline]
      simpa only [map_neg, neg_mul, CliffordAlgebra.involute_ι,
        W.nonisotropicLastComplementCliffordMap_ι] using
        (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hortho.symm)
  | add x y hx hy =>
      simp only [map_add, mul_add, add_mul, hx, hy]
  | mul x y hx hy =>
      rw [map_mul, map_mul]
      calc
        _ = (CliffordAlgebra.ι
              ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
              (lastCoordinateVector (n := n)) *
            W.nonisotropicLastComplementCliffordMap a ha A x) *
              W.nonisotropicLastComplementCliffordMap a ha A y := by
                rw [mul_assoc]
        _ = (W.nonisotropicLastComplementCliffordMap a ha A
              (CliffordAlgebra.involute x) *
            CliffordAlgebra.ι
              ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
              (lastCoordinateVector (n := n))) *
              W.nonisotropicLastComplementCliffordMap a ha A y := by rw [hx]
        _ = W.nonisotropicLastComplementCliffordMap a ha A
              (CliffordAlgebra.involute x) *
            (CliffordAlgebra.ι
              ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
              (lastCoordinateVector (n := n)) *
              W.nonisotropicLastComplementCliffordMap a ha A y) := by
                rw [mul_assoc]
        _ = W.nonisotropicLastComplementCliffordMap a ha A
              (CliffordAlgebra.involute x) *
            (W.nonisotropicLastComplementCliffordMap a ha A
              (CliffordAlgebra.involute y) *
              CliffordAlgebra.ι
                ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
                (lastCoordinateVector (n := n))) := by rw [hy]
        _ = _ := by
          rw [← mul_assoc]
          exact congrArg (fun z => z *
            CliffordAlgebra.ι
              ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
              (lastCoordinateVector (n := n)))
            ((W.nonisotropicLastComplementCliffordMap a ha A).map_mul
              (CliffordAlgebra.involute x) (CliffordAlgebra.involute y)).symm

@[simp]
theorem nonisotropicLastGenerator_sq
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    let e := CliffordAlgebra.ι
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
      (lastCoordinateVector (n := n))
    e * e = algebraMap A _ (algebraMap ℚ A a) := by
  dsimp only
  rw [CliffordAlgebra.ι_sq_scalar]
  have hline : lastCoordinateVector (n := n) =
      nonisotropicLastLineInclude (n := n) (1 : A) := by
    ext i
    cases i using Fin.lastCases <;> simp [lastCoordinateVector]
  rw [hline, W.nonisotropicLastExtension_quadraticForm_line a ha A,
    nonisotropicLastLineQuadraticForm_apply]
  simp

@[simp]
theorem involute_nonisotropicLastBlockCliffordNormalForm
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    CliffordAlgebra.involute
        (W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A (x, y)) =
      W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A
        (CliffordAlgebra.involute x, -CliffordAlgebra.involute y) := by
  rw [W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply,
    W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply]
  rw [map_add, map_mul]
  rw [← W.nonisotropicLastComplementCliffordMap_involute a ha A x,
    ← W.nonisotropicLastComplementCliffordMap_involute a ha A y]
  simp

@[simp]
theorem nonisotropicLastBlockCliffordNormalForm_mul_generator
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    let e := CliffordAlgebra.ι
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
      (lastCoordinateVector (n := n))
    W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A (x, y) * e =
      W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A
        ((algebraMap ℚ A a) • y, x) := by
  dsimp only
  rw [W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply,
    W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply]
  rw [add_mul, mul_assoc, W.nonisotropicLastGenerator_sq]
  simp only [Algebra.smul_def, map_mul]
  have hc :
      W.nonisotropicLastComplementCliffordMap a ha A
          (algebraMap A _ (algebraMap ℚ A a)) *
          W.nonisotropicLastComplementCliffordMap a ha A y =
        W.nonisotropicLastComplementCliffordMap a ha A y *
          algebraMap A _ (algebraMap ℚ A a) := by
    rw [show W.nonisotropicLastComplementCliffordMap a ha A
        (algebraMap A _ (algebraMap ℚ A a)) =
          algebraMap A _ (algebraMap ℚ A a) by simp]
    exact Algebra.commutes (R := A) (algebraMap ℚ A a)
      (W.nonisotropicLastComplementCliffordMap a ha A y)
  rw [hc]
  abel

@[simp]
theorem nonisotropicLastGenerator_mul_blockCliffordNormalForm
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    let e := CliffordAlgebra.ι
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
      (lastCoordinateVector (n := n))
    e * W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A (x, y) =
      W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A
        ((algebraMap ℚ A a) • CliffordAlgebra.involute y,
          CliffordAlgebra.involute x) := by
  dsimp only
  rw [W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply,
    W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply]
  rw [mul_add, W.nonisotropicLastGenerator_mul_complementCliffordMap]
  rw [← mul_assoc, W.nonisotropicLastGenerator_mul_complementCliffordMap]
  rw [mul_assoc, W.nonisotropicLastGenerator_sq]
  simp only [Algebra.smul_def, map_mul]
  have hc :
      W.nonisotropicLastComplementCliffordMap a ha A
          (algebraMap A _ (algebraMap ℚ A a)) *
          W.nonisotropicLastComplementCliffordMap a ha A
            (CliffordAlgebra.involute y) =
        W.nonisotropicLastComplementCliffordMap a ha A
            (CliffordAlgebra.involute y) *
          algebraMap A _ (algebraMap ℚ A a) := by
    rw [show W.nonisotropicLastComplementCliffordMap a ha A
        (algebraMap A _ (algebraMap ℚ A a)) =
          algebraMap A _ (algebraMap ℚ A a) by simp]
    exact Algebra.commutes (R := A) (algebraMap ℚ A a)
      (W.nonisotropicLastComplementCliffordMap a ha A
        (CliffordAlgebra.involute y))
  rw [hc]
  abel

/-- An even block-Clifford element which commutes with the added
nonisotropic generator has a unique preimage in the even complement Clifford
algebra. -/
theorem existsUnique_even_complementCliffordMap_of_commute_lastGenerator
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : CliffordAlgebra
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A))
    (hzEven : z ∈ CliffordAlgebra.even
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A))
    (hzCommute : Commute z
      (CliffordAlgebra.ι
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
        (lastCoordinateVector (n := n)))) :
    ∃! x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A),
      x ∈ CliffordAlgebra.even (W.commutativeScalarExtensionQuadraticForm A) ∧
        W.nonisotropicLastComplementCliffordMap a ha A x = z := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let E := W.nonisotropicLastBlockCliffordNormalFormLinearEquiv a ha A
  rcases hp : E.symm z with ⟨x, y⟩
  have hz : E (x, y) = z := by
    have h := E.apply_symm_apply z
    rw [hp] at h
    exact h
  have hinv := CliffordAlgebra.involute_eq_of_mem_even hzEven
  rw [← hz, W.involute_nonisotropicLastBlockCliffordNormalForm] at hinv
  have hpairEven :
      (CliffordAlgebra.involute x, -CliffordAlgebra.involute y) = (x, y) :=
    E.injective hinv
  have hxInv : CliffordAlgebra.involute x = x :=
    congrArg Prod.fst hpairEven
  have hyNegInv : -CliffordAlgebra.involute y = y :=
    congrArg Prod.snd hpairEven
  have hcomm := hzCommute.eq
  rw [← hz, W.nonisotropicLastBlockCliffordNormalForm_mul_generator,
    W.nonisotropicLastGenerator_mul_blockCliffordNormalForm] at hcomm
  have hpairComm :
      ((algebraMap ℚ A a) • y, x) =
        ((algebraMap ℚ A a) • CliffordAlgebra.involute y,
          CliffordAlgebra.involute x) := E.injective hcomm
  have hyScaled :
      (algebraMap ℚ A a) • y =
        (algebraMap ℚ A a) • CliffordAlgebra.involute y :=
    congrArg Prod.fst hpairComm
  have haUnit : IsUnit (algebraMap ℚ A a) :=
    (isUnit_iff_ne_zero.mpr ha).map (algebraMap ℚ A)
  have hyInv : y = CliffordAlgebra.involute y :=
    haUnit.smul_left_cancel.mp hyScaled
  have hyNeg : -y = y := by
    calc
      -y = -CliffordAlgebra.involute y := congrArg Neg.neg hyInv
      _ = y := hyNegInv
  have hyAdd : y + y = 0 := by
    calc
      y + y = y + (-y) := congrArg (fun t => y + t) hyNeg.symm
      _ = 0 := add_neg_cancel y
  have hyZero : y = 0 := by
    apply (isUnit_of_invertible (2 : A)).smul_left_cancel.mp
    simpa only [smul_zero, two_smul] using hyAdd
  have hxEven : x ∈ CliffordAlgebra.even
      (W.commutativeScalarExtensionQuadraticForm A) := by
    rw [CliffordAlgebra.mem_even_iff_involute_eq_of_invertible_two]
    exact hxInv
  have hxMap : W.nonisotropicLastComplementCliffordMap a ha A x = z := by
    rw [← hz, hyZero,
      W.nonisotropicLastBlockCliffordNormalFormLinearEquiv_apply]
    simp
  refine ⟨x, ⟨hxEven, hxMap⟩, ?_⟩
  intro x' hx'
  apply W.nonisotropicLastComplementCliffordMap_injective a ha A
  exact hx'.2.trans hxMap.symm

/-- Exact even-centralizer range of the complement Clifford embedding. -/
theorem mem_even_and_commute_lastGenerator_iff_existsUnique_complement
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : CliffordAlgebra
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)) :
    (z ∈ CliffordAlgebra.even
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A) ∧
      Commute z
        (CliffordAlgebra.ι
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
          (lastCoordinateVector (n := n)))) ↔
      ∃! x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A),
        x ∈ CliffordAlgebra.even (W.commutativeScalarExtensionQuadraticForm A) ∧
          W.nonisotropicLastComplementCliffordMap a ha A x = z := by
  constructor
  · rintro ⟨hzEven, hzCommute⟩
    exact W.existsUnique_even_complementCliffordMap_of_commute_lastGenerator
      a ha A z hzEven hzCommute
  · rintro ⟨x, ⟨hxEven, rfl⟩, _⟩
    exact ⟨W.nonisotropicLastComplementCliffordMap_mem_even a ha A x hxEven,
      W.nonisotropicLastComplementCliffordMap_commute_lastGenerator
        a ha A x hxEven⟩

end RationalQuadraticSpaceMatrix
