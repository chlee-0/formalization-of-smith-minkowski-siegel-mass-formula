import SMSFormula.SkewAdjointBaseChange
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange
import SMSFormula.QuadraticRegularValueDifferential
import SMSFormula.RationalCliffordSpinBlockIdentityTangent

/-!
# The orbit tangent at a supplied nonisotropic vector

The explicit rank-two skew-adjoint matrix below sends the supplied vector `x`
to any `y` orthogonal to it. This proves the missing surjectivity of the orbit
tangent onto the quadratic-fiber tangent, in the existing matrix model. It is
an algebraic linear lift, not a group section, chart, or choice of complement.
No determinant of top forms, Haar comparison, or local volume is evaluated.
-/

noncomputable section

open Matrix PositiveDefiniteIntegralLattice

namespace Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The rank-two formula `(y (Fx)^T - x (Fy)^T) / Q(x)`. -/
def nonisotropicOrbitTangentLift (F : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  (dotProduct x (mulVec F x))⁻¹ •
    (vecMulVec y (mulVec F x) - vecMulVec x (mulVec F y))

theorem nonisotropicOrbitTangentLift_mem (F : Matrix (Fin n) (Fin n) K)
    (hF : F.IsSymm) (x y : Fin n → K) :
    nonisotropicOrbitTangentLift F x y ∈ skewAdjointMatricesLieSubalgebra F := by
  apply (mem_ker_skewAdjointOperator_iff F _).mp
  rw [LinearMap.mem_ker, nonisotropicOrbitTangentLift, map_smul]
  suffices skewAdjointOperator F
      (vecMulVec y (mulVec F x) - vecMulVec x (mulVec F y)) = 0 by
    rw [this, smul_zero]
  simp only [skewAdjointOperator_apply, transpose_sub, transpose_vecMulVec,
    sub_mul, mul_sub, vecMulVec_mul, mul_vecMulVec,
    ← mulVec_transpose, hF.eq]
  abel

theorem nonisotropicOrbitTangentLift_apply (F : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) (hx : dotProduct x (mulVec F x) ≠ 0)
    (hy : dotProduct x (mulVec F y) = 0) :
    mulVec (nonisotropicOrbitTangentLift F x y) x = y := by
  ext i
  simp only [nonisotropicOrbitTangentLift, smul_mulVec, sub_mulVec,
    vecMulVec_mulVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    op_smul_eq_mul, dotProduct_comm (mulVec F x) x,
    dotProduct_comm (mulVec F y) x, hy]
  field_simp
  ring

/-- The formula is linear in the fiber tangent; the vector and form stay fixed. -/
def nonisotropicOrbitTangentLiftLinearMap (F : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K) : (Fin n → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun := nonisotropicOrbitTangentLift F x
  map_add' y z := by
    simp only [nonisotropicOrbitTangentLift, add_vecMulVec, mulVec_add,
      vecMulVec_add, smul_sub, smul_add]
    abel
  map_smul' c y := by
    simp only [nonisotropicOrbitTangentLift, smul_vecMulVec, mulVec_smul,
      vecMulVec_smul, smul_sub, smul_smul, RingHom.id_apply, mul_comm c]

/-- The old skew-adjoint condition makes the orbit tangent orthogonal to x. -/
theorem dotProduct_form_mulVec_skew_eq_zero [CharZero K]
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm)
    (x : Fin n → K) (A : skewAdjointMatricesLieSubalgebra F) :
    dotProduct x (mulVec F (mulVec A.1 x)) = 0 := by
  have hA := LinearMap.mem_ker.mp ((mem_ker_skewAdjointOperator_iff F A.1).mpr A.2)
  have hh := congrArg (fun M ↦ dotProduct x (mulVec M x)) hA
  have ht : dotProduct x (mulVec (A.1.transpose * F) x) =
      dotProduct x (mulVec F (mulVec A.1 x)) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    exact gramBilinearValue_symm F hF _ _
  simp only [skewAdjointOperator_apply, add_mulVec, dotProduct_add,
    zero_mulVec, dotProduct_zero] at hh
  rw [ht, ← mulVec_mulVec] at hh
  exact (mul_eq_zero.mp (show (2 : K) * dotProduct x (mulVec F (mulVec A.1 x)) = 0
    by simpa only [two_mul] using hh)).resolve_left two_ne_zero

/-- Exact image of the orbit tangent, with the preimage explicitly constructed. -/
theorem exists_skew_mulVec_eq_iff [CharZero K]
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm)
    (x : Fin n → K) (hx : dotProduct x (mulVec F x) ≠ 0) (y : Fin n → K) :
    (∃ A : skewAdjointMatricesLieSubalgebra F, mulVec A.1 x = y) ↔
      dotProduct x (mulVec F y) = 0 := by
  constructor
  · rintro ⟨A, rfl⟩
    exact dotProduct_form_mulVec_skew_eq_zero F hF x A
  · intro hy
    exact ⟨⟨nonisotropicOrbitTangentLift F x y,
      nonisotropicOrbitTangentLift_mem F hF x y⟩,
      nonisotropicOrbitTangentLift_apply F x y hx hy⟩

/-- Rational scalar extension preserves the formula, including its denominator.
No separate real or p-adic lift is chosen. -/
theorem nonisotropicOrbitTangentLift_map
    {K' : Type*} [Field K'] (f : K →+* K')
    (F : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    (nonisotropicOrbitTangentLift F x y).map f =
      nonisotropicOrbitTangentLift (F.map f) (fun i ↦ f (x i)) (fun i ↦ f (y i)) := by
  ext i j
  simp [nonisotropicOrbitTangentLift, Matrix.map_apply, Matrix.smul_apply,
    vecMulVec_apply, mulVec, dotProduct, map_sum]

end Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- In the repository's actual quadratic presentation, the orbit tangent is
exactly the kernel of the polar functional, at a supplied nonisotropic point. -/
theorem exists_skew_mulVec_eq_iff_polar_eq_zero
    (K : Type*) [Field K] [CharZero K] (x : Fin n → K)
    (hx : V.commutativeScalarExtensionQuadraticForm K x ≠ 0) (y : Fin n → K) :
    (∃ A : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K),
      mulVec A.1 x = y) ↔
      QuadraticMap.polar (V.commutativeScalarExtensionQuadraticForm K) x y = 0 := by
  have hF : (V.specialOrthogonalMappedFormMatrix K).IsSymm :=
    V.form_symm.map (algebraMap ℚ K)
  have hx' : dotProduct x (mulVec (V.specialOrthogonalMappedFormMatrix K) x) ≠ 0 := by
    simpa only [V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue,
      gramQuadraticValue] using hx
  rw [Matrix.exists_skew_mulVec_eq_iff _ hF x hx',
    V.commutativeScalarExtensionQuadraticForm_polar_eq_gram]
  rw [dotProduct_comm (mulVec (V.specialOrthogonalMappedFormMatrix K) x) y,
    gramBilinearValue_symm _ hF y x]
  simp [mul_eq_zero]

/-- At real or p-adic places this is the kernel of the strict derivative
of Q, not a separately introduced shell tangent. -/
theorem exists_skew_mulVec_eq_iff_mem_valueDifferential_ker
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    (x : Fin n → K) (hx : V.commutativeScalarExtensionQuadraticForm K x ≠ 0)
    (y : Fin n → K) :
    (∃ A : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix K),
      mulVec A.1 x = y) ↔
      y ∈ ((V.commutativeScalarExtensionQuadraticForm K).valueDifferential x).ker := by
  rw [LinearMap.mem_ker]
  exact V.exists_skew_mulVec_eq_iff_polar_eq_zero K x hx y

/-- The kernel in the existing last-extension presentation is exactly the
stabilizer tangent, whose lower-rank identification was already proved. -/
theorem mem_nonisotropicLastSkewAdjointFiber_iff_orbitTangent_zero
    (a : ℚ) (ha : a ≠ 0) (A : Type*) [CommRing A] [Algebra ℚ A]
    (X : skewAdjointMatricesLieSubalgebra
      ((V.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix A)) :
    X ∈ V.nonisotropicLastSkewAdjointFiber a ha A ↔
      mulVec X.1 lastCoordinateVector = 0 := by
  rw [V.mem_nonisotropicLastSkewAdjointFiber, lastCoordinateVector, mulVec_single_one]
  exact (funext_iff).symm

end RationalQuadraticSpaceMatrix
