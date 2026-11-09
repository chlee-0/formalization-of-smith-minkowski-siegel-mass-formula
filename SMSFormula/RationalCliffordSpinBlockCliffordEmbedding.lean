import SMSFormula.RationalCliffordSpinBlockOrthogonalComplement
import SMSFormula.RationalCliffordSpinCandidateIntrinsicPointNaturality
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

/-!
# Clifford embedding of an orthogonal complement block

For the nonsingular block carrier `W orthogonal_sum <a>`, this file lifts the
coordinate inclusion of `W` to the Clifford algebra over every commutative
rational algebra.  The map is compatible with the grade involution and
reverse, preserves the even part, and every even image commutes with the
Clifford generator of the added nonisotropic line.

This is the intrinsic Clifford layer of the high-rank Spin-volume induction.
It does not package the map as a Spin or general-Spin homomorphism, nor
identify its range with a stabilizer fiber.
-/

noncomputable section

open CliffordAlgebra

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Extend a coordinate vector by zero in the final coordinate. -/
def nonisotropicLastComplementInclude
    {A : Type*} [CommRing A] (v : Fin n → A) : Fin (n + 1) → A :=
  Fin.lastCases 0 v

@[simp]
theorem nonisotropicLastComplementInclude_castSucc
    {A : Type*} [CommRing A] (v : Fin n → A) (i : Fin n) :
    nonisotropicLastComplementInclude v i.castSucc = v i := by
  simp [nonisotropicLastComplementInclude]

@[simp]
theorem nonisotropicLastComplementInclude_last
    {A : Type*} [CommRing A] (v : Fin n → A) :
    nonisotropicLastComplementInclude v (Fin.last n) = 0 := by
  simp [nonisotropicLastComplementInclude]

/-- The coordinate inclusion as a linear map. -/
def nonisotropicLastComplementIncludeLinearMap
    (A : Type*) [CommRing A] :
    (Fin n → A) →ₗ[A] (Fin (n + 1) → A) where
  toFun := nonisotropicLastComplementInclude
  map_add' v w := by
    ext i
    cases i using Fin.lastCases <;> simp
  map_smul' r v := by
    ext i
    cases i using Fin.lastCases <;> simp

@[simp]
theorem nonisotropicLastComplementIncludeLinearMap_apply
    (A : Type*) [CommRing A] (v : Fin n → A) :
    nonisotropicLastComplementIncludeLinearMap A v =
      nonisotropicLastComplementInclude v :=
  rfl

/-- Put a scalar in the final coordinate and zero elsewhere. -/
def nonisotropicLastLineInclude
    {A : Type*} [CommRing A] (r : A) : Fin (n + 1) → A :=
  Fin.lastCases r (fun _ => 0)

@[simp]
theorem nonisotropicLastLineInclude_castSucc
    {A : Type*} [CommRing A] (r : A) (i : Fin n) :
    nonisotropicLastLineInclude (n := n) r i.castSucc = 0 := by
  simp [nonisotropicLastLineInclude]

@[simp]
theorem nonisotropicLastLineInclude_last
    {A : Type*} [CommRing A] (r : A) :
    nonisotropicLastLineInclude (n := n) r (Fin.last n) = r := by
  simp [nonisotropicLastLineInclude]

/-- The final-line inclusion as a linear map. -/
def nonisotropicLastLineIncludeLinearMap
    (A : Type*) [CommRing A] :
    A →ₗ[A] (Fin (n + 1) → A) where
  toFun := nonisotropicLastLineInclude
  map_add' r s := by
    ext i
    cases i using Fin.lastCases <;> simp
  map_smul' r s := by
    ext i
    cases i using Fin.lastCases <;> simp

@[simp]
theorem nonisotropicLastLineIncludeLinearMap_apply
    (A : Type*) [CommRing A] (r : A) :
    nonisotropicLastLineIncludeLinearMap (n := n) A r =
      nonisotropicLastLineInclude (n := n) r :=
  rfl

/-- The one-dimensional quadratic form represented by the adjoined block. -/
def nonisotropicLastLineQuadraticForm
    (a : ℚ) (A : Type*) [CommRing A] [Algebra ℚ A] :
    QuadraticForm A A :=
  algebraMap ℚ A a • QuadraticMap.sq

@[simp]
theorem nonisotropicLastLineQuadraticForm_apply
    (a : ℚ) (A : Type*) [CommRing A] [Algebra ℚ A] (r : A) :
    nonisotropicLastLineQuadraticForm a A r = algebraMap ℚ A a * r ^ 2 := by
  simp [nonisotropicLastLineQuadraticForm, QuadraticMap.sq_apply,
    Algebra.smul_def, pow_two]

theorem nonisotropicLastExtension_quadraticForm_complement
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (v : Fin n → A) :
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
        (nonisotropicLastComplementInclude v) =
      W.commutativeScalarExtensionQuadraticForm A v := by
  change
    ((Matrix.toLinearMap₂' A
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A))
        (nonisotropicLastComplementInclude v))
        (nonisotropicLastComplementInclude v) =
      ((Matrix.toLinearMap₂' A (W.specialOrthogonalMappedFormMatrix A)) v) v
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply']
  rw [W.nonisotropicLastExtension_mappedFormMatrix a ha A]
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Fin.sum_univ_castSucc]
  simp [nonisotropicLastBlockMatrix]

theorem nonisotropicLastExtension_quadraticForm_line
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (r : A) :
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
        (nonisotropicLastLineInclude (n := n) r) =
      nonisotropicLastLineQuadraticForm a A r := by
  change
    ((Matrix.toLinearMap₂' A
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A))
        (nonisotropicLastLineInclude (n := n) r))
        (nonisotropicLastLineInclude (n := n) r) =
      nonisotropicLastLineQuadraticForm a A r
  rw [Matrix.toLinearMap₂'_apply']
  rw [W.nonisotropicLastExtension_mappedFormMatrix a ha A]
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Fin.sum_univ_castSucc]
  simp [nonisotropicLastBlockMatrix,
    nonisotropicLastLineQuadraticForm, QuadraticMap.sq_apply,
    Algebra.smul_def]
  ring

theorem nonisotropicLastExtension_quadraticForm_complement_add_line
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (v : Fin n → A) (r : A) :
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
        (nonisotropicLastComplementInclude v +
          nonisotropicLastLineInclude (n := n) r) =
      W.commutativeScalarExtensionQuadraticForm A v +
        nonisotropicLastLineQuadraticForm a A r := by
  change
    ((Matrix.toLinearMap₂' A
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A))
        (nonisotropicLastComplementInclude v +
          nonisotropicLastLineInclude (n := n) r))
        (nonisotropicLastComplementInclude v +
          nonisotropicLastLineInclude (n := n) r) =
      ((Matrix.toLinearMap₂' A (W.specialOrthogonalMappedFormMatrix A)) v) v +
        nonisotropicLastLineQuadraticForm a A r
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply']
  rw [W.nonisotropicLastExtension_mappedFormMatrix a ha A]
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Fin.sum_univ_castSucc]
  simp [nonisotropicLastBlockMatrix,
    nonisotropicLastLineQuadraticForm, QuadraticMap.sq_apply,
    Algebra.smul_def]
  ring

/-- The complement coordinate inclusion preserves the quadratic form. -/
def nonisotropicLastComplementIsometry
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    W.commutativeScalarExtensionQuadraticForm A →qᵢ
      (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A where
  toLinearMap := nonisotropicLastComplementIncludeLinearMap A
  map_app' := W.nonisotropicLastExtension_quadraticForm_complement a ha A

/-- The final-line coordinate inclusion preserves its one-dimensional form. -/
def nonisotropicLastLineIsometry
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    nonisotropicLastLineQuadraticForm a A →qᵢ
      (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A where
  toLinearMap := nonisotropicLastLineIncludeLinearMap A
  map_app' := W.nonisotropicLastExtension_quadraticForm_line a ha A

/-- The Clifford algebra map induced by the complement inclusion. -/
def nonisotropicLastComplementCliffordMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A) →ₐ[A]
      CliffordAlgebra
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A) :=
  CliffordAlgebra.map (W.nonisotropicLastComplementIsometry a ha A)

@[simp]
theorem nonisotropicLastComplementCliffordMap_ι
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] (v : Fin n → A) :
    W.nonisotropicLastComplementCliffordMap a ha A
        (CliffordAlgebra.ι (W.commutativeScalarExtensionQuadraticForm A) v) =
      CliffordAlgebra.ι
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
        (nonisotropicLastComplementInclude v) := by
  exact CliffordAlgebra.map_apply_ι _ _

theorem nonisotropicLastComplementCliffordMap_involute
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    W.nonisotropicLastComplementCliffordMap a ha A
        (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute
        (W.nonisotropicLastComplementCliffordMap a ha A x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

theorem nonisotropicLastComplementCliffordMap_reverse
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    W.nonisotropicLastComplementCliffordMap a ha A
        (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse
        (W.nonisotropicLastComplementCliffordMap a ha A x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | mul x y hx hy => simp [CliffordAlgebra.reverse.map_mul, hx, hy]
  | add x y hx hy => simp [hx, hy]

@[simp]
theorem nonisotropicLastComplementInclude_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (v : Fin n → A) :
    (fun i => f (nonisotropicLastComplementInclude v i)) =
      nonisotropicLastComplementInclude (fun i => f (v i)) := by
  ext i
  cases i using Fin.lastCases <;> simp

/-- The complement Clifford map commutes with every scalar extension of
commutative rational algebras. -/
theorem nonisotropicLastComplementCliffordMap_naturality
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A)) :
    (W.nonisotropicLastExtension a ha).commutativeCliffordAlgebraBaseChangeHom f
        (W.nonisotropicLastComplementCliffordMap a ha A x) =
      W.nonisotropicLastComplementCliffordMap a ha B
        (W.commutativeCliffordAlgebraBaseChangeHom f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      simp [commutativeCliffordAlgebraBaseChangeHom,
        commutativeTensorCliffordEquiv]
  | ι v =>
      simp only [nonisotropicLastComplementCliffordMap_ι,
        commutativeCliffordAlgebraBaseChangeHom_ι]
      congr 1
      exact nonisotropicLastComplementInclude_map f.toRingHom v
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-- The complement Clifford map preserves the even part. -/
theorem nonisotropicLastComplementCliffordMap_mem_even
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A))
    (hx : x ∈ CliffordAlgebra.even
      (W.commutativeScalarExtensionQuadraticForm A)) :
    W.nonisotropicLastComplementCliffordMap a ha A x ∈
      CliffordAlgebra.even
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A) := by
  letI : Invertible (2 : A) := rationalAlgebraInvertibleTwo A
  rw [CliffordAlgebra.mem_even_iff_involute_eq_of_invertible_two]
  rw [← W.nonisotropicLastComplementCliffordMap_involute a ha A]
  exact congrArg (W.nonisotropicLastComplementCliffordMap a ha A)
    (CliffordAlgebra.involute_eq_of_mem_even hx)

theorem nonisotropicLastComplement_line_isOrtho
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (v : Fin n → A) (r : A) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A).IsOrtho
      (W.nonisotropicLastComplementIsometry a ha A v)
      (W.nonisotropicLastLineIsometry a ha A r) := by
  rw [QuadraticMap.isOrtho_def]
  change
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
        (nonisotropicLastComplementInclude v +
          nonisotropicLastLineInclude (n := n) r) =
      (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
          (nonisotropicLastComplementInclude v) +
        (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
          (nonisotropicLastLineInclude (n := n) r)
  rw [W.nonisotropicLastExtension_quadraticForm_complement_add_line a ha A,
    W.nonisotropicLastExtension_quadraticForm_complement a ha A,
    W.nonisotropicLastExtension_quadraticForm_line a ha A]

/-- Every even complement image commutes with the generator of the added
nonisotropic line. -/
theorem nonisotropicLastComplementCliffordMap_commute_lastGenerator
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : CliffordAlgebra (W.commutativeScalarExtensionQuadraticForm A))
    (hx : x ∈ CliffordAlgebra.even
      (W.commutativeScalarExtensionQuadraticForm A)) :
    Commute
      (W.nonisotropicLastComplementCliffordMap a ha A x)
      (CliffordAlgebra.ι
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A)
        (lastCoordinateVector (n := n))) := by
  let QW := W.commutativeScalarExtensionQuadraticForm A
  let QL := nonisotropicLastLineQuadraticForm a A
  let QB :=
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm A
  have hline :
      CliffordAlgebra.map (W.nonisotropicLastLineIsometry a ha A)
          (CliffordAlgebra.ι QL 1) =
        CliffordAlgebra.ι QB (lastCoordinateVector (n := n)) := by
    rw [CliffordAlgebra.map_apply_ι]
    congr 1
    change nonisotropicLastLineInclude (n := n) (1 : A) =
      lastCoordinateVector (n := n)
    ext i
    cases i using Fin.lastCases <;> simp [lastCoordinateVector]
  rw [← hline]
  exact CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
    (W.nonisotropicLastComplementIsometry a ha A)
    (W.nonisotropicLastLineIsometry a ha A)
    (W.nonisotropicLastComplement_line_isOrtho a ha A)
    x (CliffordAlgebra.ι QL 1) hx
    (CliffordAlgebra.ι_mem_evenOdd_one QL 1)

end RationalQuadraticSpaceMatrix
