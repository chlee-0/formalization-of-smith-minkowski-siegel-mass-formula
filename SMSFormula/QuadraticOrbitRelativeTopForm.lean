import SMSFormula.QuadraticRelativeTopForm

/-!
# Pull the relative coordinate form back through the actual orbit tangent

The existing rank-two lift supplies a linear right inverse. Thus the relative
vector/value form can be evaluated on the old skew-adjoint tangent without a
quotient section, chart, basis choice or chosen complement. This is the form
to compare with the group/stabilizer determinant forms; that comparison,
and every Haar multiplier it needs, remain separate.
-/

noncomputable section
open Matrix PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix (n + 1))
variable (K : Type*) [Field K] [CharZero K]
variable (x : Fin (n + 1) → K)
variable (hx : V.commutativeScalarExtensionQuadraticForm K x ≠ 0)

/-- The actual matrix orbit tangent, with its codomain the literal polar kernel. -/
def orbitPolarTangentLinearMap :
    skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K) →ₗ[K]
      ((V.commutativeScalarExtensionQuadraticForm K).polarBilin x).ker where
  toFun A := ⟨mulVec A.1 x,
    (V.exists_skew_mulVec_eq_iff_polar_eq_zero K x hx _).mp ⟨A, rfl⟩⟩
  map_add' A B := by
    apply Subtype.ext
    exact add_mulVec A.1 B.1 x
  map_smul' c A := by
    apply Subtype.ext
    exact smul_mulVec c A.1 x

/-- The rank-two lift restricted to the actual polar kernel. -/
def orbitPolarTangentLiftLinearMap :
    ((V.commutativeScalarExtensionQuadraticForm K).polarBilin x).ker →ₗ[K]
      skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K) :=
  ((Matrix.nonisotropicOrbitTangentLiftLinearMap (V.specialOrthogonalMappedFormMatrix K) x).codRestrict
    (skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K)).toSubmodule
    (fun y ↦ Matrix.nonisotropicOrbitTangentLift_mem _
      (V.form_symm.map (algebraMap ℚ K)) x y)).comp
        ((V.commutativeScalarExtensionQuadraticForm K).polarBilin x).ker.subtype

theorem orbitPolarTangentLinearMap_lift
    (y : ((V.commutativeScalarExtensionQuadraticForm K).polarBilin x).ker) :
    V.orbitPolarTangentLinearMap K x hx (V.orbitPolarTangentLiftLinearMap K x y) = y := by
  apply Subtype.ext
  apply Matrix.nonisotropicOrbitTangentLift_apply
  · simpa only [V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue,
      gramQuadraticValue] using hx
  · have hy := y.2
    have hF : (V.specialOrthogonalMappedFormMatrix K).IsSymm :=
      V.form_symm.map (algebraMap ℚ K)
    change QuadraticMap.polar (V.commutativeScalarExtensionQuadraticForm K) x y.1 = 0 at hy
    rw [V.commutativeScalarExtensionQuadraticForm_polar_eq_gram,
      dotProduct_comm (mulVec (V.specialOrthogonalMappedFormMatrix K) x) y.1,
      gramBilinearValue_symm _ hF y.1 x] at hy
    exact (mul_eq_zero.mp hy).resolve_left two_ne_zero

/-- Pullback through A -> Ax, with no group-Haar normalization attached. -/
def orbitRelativeCoordinateTopForm :
    (skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K))
      [⋀^Fin n]→ₗ[K] K :=
  ((V.commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm x).compLinearMap
    (V.orbitPolarTangentLinearMap K x hx)

/-- Evaluating at the explicit lifts recovers the relative form exactly. -/
theorem orbitRelativeCoordinateTopForm_lift
    (y : Fin n → ((V.commutativeScalarExtensionQuadraticForm K).polarBilin x).ker) :
    V.orbitRelativeCoordinateTopForm K x hx (fun i ↦ V.orbitPolarTangentLiftLinearMap K x (y i)) =
      (V.commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm x y := by
  simp [orbitRelativeCoordinateTopForm, AlternatingMap.compLinearMap_apply,
    V.orbitPolarTangentLinearMap_lift K x hx]

/-- All supplied matrix lifts with the same images compute the same value.
This is independence from the stabilizer directions, not a quotient section. -/
theorem orbitRelativeCoordinateTopForm_eq_of_same_action
    (A B : Fin n → skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K))
    (hAB : ∀ i, mulVec (A i).1 x = mulVec (B i).1 x) :
    V.orbitRelativeCoordinateTopForm K x hx A = V.orbitRelativeCoordinateTopForm K x hx B := by
  apply congrArg ((V.commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm x)
  funext i
  apply Subtype.ext
  exact hAB i

/-- The tangent pullback loses no information, because its explicit right
inverse is already proved. This is not nonvanishing of a Riesz measure. -/
theorem orbitRelativeCoordinateTopForm_eq_zero_iff :
    V.orbitRelativeCoordinateTopForm K x hx = 0 ↔
      (V.commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm x = 0 := by
  constructor
  · intro h
    ext y
    rw [← V.orbitRelativeCoordinateTopForm_lift K x hx y, h]
    rfl
  · intro h
    simp [orbitRelativeCoordinateTopForm, h]

section Block

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The relative coordinate form evaluated on the orbit lifts of the block
coordinates, keeping orientation and the factor two. -/
theorem orbitRelativeCoordinateTopForm_nonisotropicLastExtension
    (w : Fin n → Fin n → K) :
    (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm K lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (fun i ↦ (W.nonisotropicLastExtension a ha).orbitPolarTangentLiftLinearMap K
        lastCoordinateVector (W.nonisotropicLastPolarTangent a ha (w i))) =
      ((-1 : K)^n / (2 * algebraMap ℚ K a)) * (Pi.basisFun K (Fin n)).det w := by
  rw [orbitRelativeCoordinateTopForm_lift,
    W.relativeCoordinateTopForm_nonisotropicLastExtension]

theorem orbitRelativeCoordinateTopForm_nonisotropicLastExtension_ne_zero :
    (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm K lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) ≠ 0 := by
  intro h
  exact W.relativeCoordinateTopForm_nonisotropicLastExtension_ne_zero a ha
    (((W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm_eq_zero_iff
      K lastCoordinateVector _).mp h)

end Block

end RationalQuadraticSpaceMatrix
