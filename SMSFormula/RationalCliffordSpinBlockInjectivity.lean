import SMSFormula.RationalCliffordGeneralSpinBlockIntrinsicPoint
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Injectivity of orthogonal-complement block maps

The complement Clifford map into a nonsingular one-line extension is
injective.  Consequently the intrinsic Spin and general-Spin block point
homomorphisms are injective.  Exact image or stabilizer-range statements are
deliberately left separate.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The scalar coefficient of a Clifford element, obtained from the exterior
algebra PBW equivalence. -/
def scalarPart (Q : QuadraticForm R M) [Invertible (2 : R)] :
    CliffordAlgebra Q →ₗ[R] R :=
  ExteriorAlgebra.algebraMapInv.toLinearMap.comp (equivExterior Q).toLinearMap

@[simp]
theorem scalarPart_one (Q : QuadraticForm R M) [Invertible (2 : R)] :
    scalarPart Q 1 = 1 := by
  simp [scalarPart]

end CliffordAlgebra

namespace GradedTensorProduct

variable {R ι A B : Type*}
variable [CommSemiring ι] [DecidableEq ι]
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [Module ι (Additive ℤˣ)]

/-- A linear retraction of the left inclusion, given any scalar functional on
the right factor taking one to one. -/
def includeLeftRetraction (φ : B →ₗ[R] R) :
    (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] A :=
  (TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y => φ y • x
          map_add' := fun y z => by rw [map_add, add_smul]
          map_smul' := fun r y => by simp [mul_smul] }
      map_add' := fun x y => by
        ext z
        simp [smul_add]
      map_smul' := fun r x => by
        ext y
        simp [smul_smul, mul_comm] }).comp
    (GradedTensorProduct.of R 𝒜 ℬ).symm.toLinearMap

@[simp]
theorem includeLeftRetraction_includeLeft
    (φ : B →ₗ[R] R) (hφ : φ 1 = 1) (x : A) :
    includeLeftRetraction 𝒜 ℬ φ (includeLeft 𝒜 ℬ x) = x := by
  simp [includeLeftRetraction, includeLeft, includeLeftRingHom,
    GradedTensorProduct.tmul, hφ]

theorem includeLeft_injective_of_linearMap_one
    (φ : B →ₗ[R] R) (hφ : φ 1 = 1) :
    Function.Injective (includeLeft 𝒜 ℬ) :=
  (Function.LeftInverse.injective fun x =>
    includeLeftRetraction_includeLeft 𝒜 ℬ φ hφ x)

end GradedTensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

@[simp]
theorem nonisotropicLastLineInclude_zero
    (A : Type*) [CommRing A] :
    nonisotropicLastLineInclude (n := n) (0 : A) = 0 := by
  ext i
  cases i using Fin.lastCases <;> simp

/-- Split the final coordinate from a block vector. -/
def nonisotropicLastBlockLinearEquiv
    (A : Type*) [CommRing A] :
    ((Fin n → A) × A) ≃ₗ[A] (Fin (n + 1) → A) where
  toFun p := nonisotropicLastComplementInclude p.1 +
    nonisotropicLastLineInclude p.2
  invFun v := (fun i => v i.castSucc, v (Fin.last n))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp
  right_inv v := by
    funext i
    cases i using Fin.lastCases <;> simp
  map_add' p q := by
    funext i
    cases i using Fin.lastCases <;> simp
  map_smul' r p := by
    funext i
    cases i using Fin.lastCases <;> simp

@[simp]
theorem nonisotropicLastBlockLinearEquiv_apply
    (A : Type*) [CommRing A] (v : Fin n → A) (r : A) :
    nonisotropicLastBlockLinearEquiv (n := n) A (v, r) =
      nonisotropicLastComplementInclude v +
        nonisotropicLastLineInclude r :=
  rfl

/-- The product quadratic form of the complement and last line is isometric
to the literal nonsingular block form. -/
def nonisotropicLastProductIsometryEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (W.commutativeScalarExtensionQuadraticForm A).prod
        (nonisotropicLastLineQuadraticForm a A) |>.IsometryEquiv
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A) where
  toLinearEquiv := nonisotropicLastBlockLinearEquiv A
  map_app' p := by
    rcases p with ⟨v, r⟩
    exact W.nonisotropicLastExtension_quadraticForm_complement_add_line a ha A v r

@[simp]
theorem nonisotropicLastProductIsometryEquiv_apply
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (v : Fin n → A) (r : A) :
    W.nonisotropicLastProductIsometryEquiv a ha A (v, r) =
      nonisotropicLastComplementInclude v +
        nonisotropicLastLineInclude r :=
  rfl

/-- Factor the complement Clifford map through the left factor of Mathlib's
graded tensor-product description of a Clifford algebra of a product. -/
theorem nonisotropicLastComplementCliffordMap_eq_prod
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.nonisotropicLastComplementCliffordMap a ha A =
      (CliffordAlgebra.equivOfIsometry
          (W.nonisotropicLastProductIsometryEquiv a ha A)).toAlgHom.comp
        ((CliffordAlgebra.prodEquiv
            (W.commutativeScalarExtensionQuadraticForm A)
            (nonisotropicLastLineQuadraticForm a A)).symm.toAlgHom.comp
          (GradedTensorProduct.includeLeft
            (CliffordAlgebra.evenOdd
              (W.commutativeScalarExtensionQuadraticForm A))
            (CliffordAlgebra.evenOdd
              (nonisotropicLastLineQuadraticForm a A)))) := by
  apply CliffordAlgebra.hom_ext
  ext v
  simp

/-- The Clifford algebra map induced by the complement inclusion is
injective over every commutative rational algebra. -/
theorem nonisotropicLastComplementCliffordMap_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective (W.nonisotropicLastComplementCliffordMap a ha A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  rw [W.nonisotropicLastComplementCliffordMap_eq_prod a ha A]
  exact (CliffordAlgebra.equivOfIsometry
      (W.nonisotropicLastProductIsometryEquiv a ha A)).injective.comp
    ((CliffordAlgebra.prodEquiv
      (W.commutativeScalarExtensionQuadraticForm A)
      (nonisotropicLastLineQuadraticForm a A)).symm.injective.comp
      (GradedTensorProduct.includeLeft_injective_of_linearMap_one
        (CliffordAlgebra.evenOdd
          (W.commutativeScalarExtensionQuadraticForm A))
        (CliffordAlgebra.evenOdd
          (nonisotropicLastLineQuadraticForm a A))
        (CliffordAlgebra.scalarPart
          (nonisotropicLastLineQuadraticForm a A))
        (CliffordAlgebra.scalarPart_one
          (nonisotropicLastLineQuadraticForm a A))))

/-- Injectivity transported into the fixed tensor coordinates used by the
intrinsic point carriers. -/
theorem nonisotropicLastComplementCoordinateCliffordMap_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective
      (W.nonisotropicLastComplementCoordinateCliffordMap a ha A) := by
  intro x y hxy
  apply (W.commutativeTensorCliffordEquiv A).injective
  apply W.nonisotropicLastComplementCliffordMap_injective a ha A
  simpa only [commutativeTensorCliffordEquiv_nonisotropicLastComplementCoordinateCliffordMap]
    using congrArg
      ((W.nonisotropicLastExtension a ha).commutativeTensorCliffordEquiv A) hxy

/-- The intrinsic Spin block homomorphism is injective. -/
theorem nonisotropicLastComplementSpinPointHom_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective (W.nonisotropicLastComplementSpinPointHom a ha A) := by
  intro x y hxy
  apply CliffordSpinIntrinsicPoint.ext
  apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
  simpa only [nonisotropicLastComplementSpinPoint_coe] using
    congrArg (fun z :
      (W.nonisotropicLastExtension a ha).CliffordSpinIntrinsicPoint A => z.1) hxy

/-- The intrinsic general-Spin block homomorphism is injective. -/
theorem nonisotropicLastComplementGeneralSpinPointHom_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective
      (W.nonisotropicLastComplementGeneralSpinPointHom a ha A) := by
  intro x y hxy
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
  apply Units.ext
  apply W.nonisotropicLastComplementCoordinateCliffordMap_injective a ha A
  simpa only [nonisotropicLastComplementGeneralSpinPoint_cliffordUnit,
    coe_nonisotropicLastComplementGeneralSpinCliffordUnit] using
      congrArg (fun z :
        (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A =>
          (z.cliffordUnit :
            (W.nonisotropicLastExtension a ha).cliffordCoordinateBaseChangeAlgebra A)) hxy

end RationalQuadraticSpaceMatrix
