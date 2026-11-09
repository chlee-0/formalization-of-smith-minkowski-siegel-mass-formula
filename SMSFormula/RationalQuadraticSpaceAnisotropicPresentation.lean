import SMSFormula.RationalQuadraticSpaceAnisotropicBaseChange
import SMSFormula.RationalCliffordSpinBlockInjectivity
import SMSFormula.RationalCliffordGeneralSpinBlockFieldShell

/-!
# Matrix presentations of orthogonal complements of anisotropic vectors

For a rational vector `x`, this file accepts (but does not choose) a
lower-rank matrix presentation of the intrinsic orthogonal complement `x⊥`.
The nonisotropy hypothesis `Q(x) ≠ 0` is supplied to the theorems that need
the codimension-one decomposition; it is not stored in the presentation
structure itself.  It composes that supplied presentation with the canonical
anisotropic decomposition to obtain the block-to-ambient quadratic isometry.

The construction is algebraic.  In particular, it does not put a topology or
Haar measure on the abstract complement, and it does not select a presentation
or a shell representative.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n m : ℕ}

/-- A supplied matrix presentation of the intrinsic orthogonal complement of
a rational vector.  Despite the type name, nonisotropy of `x` is not a field
of this structure; it is an explicit hypothesis of the theorems that use it. -/
structure AnisotropicComplementPresentation
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) (m : ℕ) where
  lowerSpace : RationalQuadraticSpaceMatrix m
  complementIsometry :
    lowerSpace.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction x)

namespace AnisotropicComplementPresentation

variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Every supplied presentation has the forced rank `n - 1`; this is a
consequence of its isometry, not an extra choice of coordinates. -/
theorem dimension_add_one
    (P : V.AnisotropicComplementPresentation x m)
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : m + 1 = n := by
  calc
    m + 1 = Module.finrank ℚ (Fin m → ℚ) + 1 := by simp
    _ = Module.finrank ℚ
          (V.anisotropicRationalOrthogonalComplement x) + 1 := by
      rw [LinearEquiv.finrank_eq
        (AnisotropicComplementPresentation.complementIsometry P).toLinearEquiv]
    _ = n := V.finrank_anisotropicRationalOrthogonalComplement_add_one x hx

/-- The supplied complement presentation, with the canonical scalar norm line
adjoined on both sides. -/
def productIsometryEquiv :
    (P.lowerSpace.quadraticForm.prod
        (nonisotropicLastLineQuadraticForm
          (V.nativeRationalQuadraticForm x) ℚ)).IsometryEquiv
      (V.anisotropicRationalOrthogonalSum x) where
  toLinearEquiv :=
    LinearEquiv.prodCongr P.complementIsometry.toLinearEquiv
      (LinearEquiv.refl ℚ ℚ)
  map_app' p := by
    rcases p with ⟨z, a⟩
    change
      V.nativeRationalQuadraticForm.orthogonalRestriction x
          (P.complementIsometry z) +
          V.nativeRationalQuadraticForm.anisotropicScalarLine x a =
        P.lowerSpace.quadraticForm z +
          nonisotropicLastLineQuadraticForm
            (V.nativeRationalQuadraticForm x) ℚ a
    rw [P.complementIsometry.map_app]
    simp [V.anisotropicRationalNormLine_apply,
      nonisotropicLastLineQuadraticForm_apply]
    ring

@[simp]
theorem productIsometryEquiv_apply (z : Fin m → ℚ) (a : ℚ) :
    P.productIsometryEquiv (z, a) = (P.complementIsometry z, a) :=
  rfl

/-- The rational block quadratic space associated to the supplied complement
presentation. -/
abbrev blockSpace (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    RationalQuadraticSpaceMatrix (m + 1) :=
  P.lowerSpace.nonisotropicLastExtension
    (V.nativeRationalQuadraticForm x) hx

/-- The literal rational block form is the product of the supplied lower form
and the norm line. -/
def blockProductIsometryEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.lowerSpace.quadraticForm.prod
        (nonisotropicLastLineQuadraticForm
          (V.nativeRationalQuadraticForm x) ℚ)).IsometryEquiv
      (P.blockSpace hx).quadraticForm where
  toLinearEquiv := nonisotropicLastBlockLinearEquiv ℚ
  map_app' p := by
    rcases p with ⟨z, a⟩
    change
      (P.blockSpace hx).quadraticForm
          (nonisotropicLastComplementInclude z +
            nonisotropicLastLineInclude a) =
        P.lowerSpace.quadraticForm z +
          nonisotropicLastLineQuadraticForm
            (V.nativeRationalQuadraticForm x) ℚ a
    simpa [quadraticForm, commutativeScalarExtensionQuadraticForm,
      commutativeScalarExtensionFormMatrix,
      specialOrthogonalMappedFormMatrix] using
      P.lowerSpace.nonisotropicLastExtension_quadraticForm_complement_add_line
        (V.nativeRationalQuadraticForm x) hx ℚ z a

/-- The supplied lower presentation determines a rational quadratic isometry
from the native last-coordinate block to the ambient space. -/
def blockToAmbientIsometryEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).quadraticForm.IsometryEquiv
      V.nativeRationalQuadraticForm :=
  (P.blockProductIsometryEquiv hx).symm |>.trans
    ((P.productIsometryEquiv).trans
      (V.anisotropicRationalDecompositionIsometryEquiv x hx))

@[simp]
theorem blockToAmbientIsometryEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : Fin m → ℚ) (a : ℚ) :
    P.blockToAmbientIsometryEquiv hx
        (nonisotropicLastComplementInclude z +
          nonisotropicLastLineInclude a) =
      a • x + P.complementIsometry z := by
  change
    V.anisotropicRationalDecompositionIsometryEquiv x hx
      (P.productIsometryEquiv
        ((P.blockProductIsometryEquiv hx).symm
          (nonisotropicLastComplementInclude z +
            nonisotropicLastLineInclude a))) = _
  have hsplit :
      (P.blockProductIsometryEquiv hx).symm
          (nonisotropicLastComplementInclude z +
            nonisotropicLastLineInclude a) = (z, a) := by
    change (nonisotropicLastBlockLinearEquiv ℚ).symm
      (nonisotropicLastComplementInclude z +
        nonisotropicLastLineInclude a) = (z, a)
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [hsplit]
  rw [P.productIsometryEquiv_apply]
  exact V.anisotropicRationalDecompositionIsometryEquiv_apply x hx
    (P.complementIsometry z) a

@[simp]
theorem blockToAmbientIsometryEquiv_lastCoordinateVector
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientIsometryEquiv hx
        (lastCoordinateVector : Fin (m + 1) → ℚ) = x := by
  rw [show (lastCoordinateVector : Fin (m + 1) → ℚ) =
      nonisotropicLastComplementInclude (0 : Fin m → ℚ) +
        nonisotropicLastLineInclude 1 by
    ext i
    cases i using Fin.lastCases <;>
      simp [lastCoordinateVector, nonisotropicLastComplementInclude,
        nonisotropicLastLineInclude]]
  simp

/-- Scalar extension of the supplied block-to-ambient isometry, expressed on
the repository's existing matrix-coordinate carriers on both sides. -/
def blockToAmbientBaseChangeIsometryEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm A).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  exact
    ((P.blockSpace hx).commutativeScalarExtensionQuadraticIsometryEquiv A).symm
      |>.trans ((P.blockToAmbientIsometryEquiv hx).baseChange (A := A))
      |>.trans (V.commutativeScalarExtensionQuadraticIsometryEquiv A)

/-- The scalar-extended block-to-ambient map agrees literally with entrywise
rational base change on every rational vector. -/
@[simp]
theorem blockToAmbientBaseChangeIsometryEquiv_rational
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (y : Fin (m + 1) → ℚ) :
    P.blockToAmbientBaseChangeIsometryEquiv hx A
        (fun i ↦ algebraMap ℚ A (y i)) =
      fun i ↦ algebraMap ℚ A (P.blockToAmbientIsometryEquiv hx y i) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let eBlock :=
    (P.blockSpace hx).commutativeScalarExtensionQuadraticIsometryEquiv A
  let eAmbient := V.commutativeScalarExtensionQuadraticIsometryEquiv A
  have hblock :
      eBlock.symm (fun i ↦ algebraMap ℚ A (y i)) =
        (1 : A) ⊗ₜ[ℚ] y := by
    change (commutativeScalarExtensionModuleEquiv (n := m + 1) A).symm
      (fun i ↦ algebraMap ℚ A (y i)) = (1 : A) ⊗ₜ[ℚ] y
    rw [LinearEquiv.symm_apply_eq]
    ext i
    symm
    change (TensorProduct.piScalarRight ℚ A A (Fin (m + 1))
      ((1 : A) ⊗ₜ[ℚ] y)) i = _
    rw [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    simp [Algebra.smul_def]
  change eAmbient
      (((P.blockToAmbientIsometryEquiv hx).baseChange (A := A))
        (eBlock.symm (fun i ↦ algebraMap ℚ A (y i)))) = _
  rw [hblock, QuadraticMap.IsometryEquiv.baseChange_tmul]
  ext i
  change (TensorProduct.piScalarRight ℚ A A (Fin n)
      ((1 : A) ⊗ₜ[ℚ] (P.blockToAmbientIsometryEquiv hx y))) i = _
  rw [TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def]

/-- The supplied presentation gives an exact equivalence from its native
block shell to the ambient shell through `x`. -/
def blockToAmbientShellEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    P.lowerSpace.nonisotropicLastQuadraticShell
        (V.nativeRationalQuadraticForm x) hx A ≃
      V.anisotropicRationalAmbientShell x A := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  exact
    { toFun := fun y ↦ ⟨e y, by
        change V.commutativeScalarExtensionQuadraticForm A (e y) = _
        rw [e.map_app, y.property]⟩
      invFun := fun y ↦ ⟨e.symm y, by
        change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm A
          (e.symm y) = _
        rw [e.symm.map_app, y.property]⟩
      left_inv := fun y ↦ Subtype.ext (e.symm_apply_apply y)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y) }

@[simp]
theorem coe_blockToAmbientShellEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (y : P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx A) :
    (P.blockToAmbientShellEquiv hx A y).1 =
      P.blockToAmbientBaseChangeIsometryEquiv hx A y :=
  rfl

/-- The native last-coordinate point of every supplied presentation maps to
the ambient rational diagonal of `x`. -/
@[simp]
theorem blockToAmbientShellEquiv_lastCoordinateVector
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    (P.blockToAmbientShellEquiv hx A
      ⟨lastCoordinateVector,
        P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
          (V.nativeRationalQuadraticForm x) hx A⟩).1 =
      fun i ↦ algebraMap ℚ A (x i) := by
  rw [coe_blockToAmbientShellEquiv]
  have hlast : (lastCoordinateVector : Fin (m + 1) → A) =
      (fun i ↦ algebraMap ℚ A
        ((lastCoordinateVector : Fin (m + 1) → ℚ) i)) := by
    ext i
    cases i using Fin.lastCases <;> simp [lastCoordinateVector]
  calc
    P.blockToAmbientBaseChangeIsometryEquiv hx A lastCoordinateVector =
        P.blockToAmbientBaseChangeIsometryEquiv hx A
          (fun i ↦ algebraMap ℚ A
            ((lastCoordinateVector : Fin (m + 1) → ℚ) i)) :=
      congrArg (P.blockToAmbientBaseChangeIsometryEquiv hx A) hlast
    _ = fun i ↦ algebraMap ℚ A
        (P.blockToAmbientIsometryEquiv hx
          (lastCoordinateVector : Fin (m + 1) → ℚ) i) :=
      P.blockToAmbientBaseChangeIsometryEquiv_rational hx A _
    _ = fun i ↦ algebraMap ℚ A (x i) := by
      rw [P.blockToAmbientIsometryEquiv_lastCoordinateVector hx]

end AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix
