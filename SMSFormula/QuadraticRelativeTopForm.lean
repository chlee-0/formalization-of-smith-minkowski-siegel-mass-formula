import SMSFormula.QuadraticOrbitTangentLift
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The relative vector/value top form at a supplied regular point

Contract the coordinate determinant by `x / (2 Q(x))`, then restrict it to
the kernel of the polar functional. Independence of the transverse lift is
proved, not assumed. This is a tangent top form; no fiber measure, chart,
group-Haar comparison or normalization is introduced.
-/

noncomputable section

open Matrix PositiveDefiniteIntegralLattice

namespace QuadraticMap

variable {K : Type*} [Field K] {n : ℕ}

private theorem coordinate_topForm_zero_on_kernel
    (ω : (Fin (n + 1) → K) [⋀^Fin (n + 1)]→ₗ[K] K)
    (ℓ : (Fin (n + 1) → K) →ₗ[K] K) (z : Fin (n + 1) → K) (hz : ℓ z = 1)
    (w : Fin (n + 1) → Fin (n + 1) → K) (hw : ∀ i, ℓ (w i) = 0) :
    ω w = 0 := by
  apply ω.map_linearDependent
  intro hi
  have hs : Submodule.span K (Set.range w) ≤ ℓ.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hw i
  rw [hi.span_eq_top_of_card_eq_finrank' (by simp)] at hs
  have hzero : ℓ z = 0 := hs (Submodule.mem_top)
  exact one_ne_zero (hz.symm.trans hzero)

/-- A top form evaluated on the fiber tangents is independent of which vector
of differential value one is inserted first. No transverse vector is selected. -/
theorem coordinate_topForm_lift_independent
    (ω : (Fin (n + 1) → K) [⋀^Fin (n + 1)]→ₗ[K] K)
    (ℓ : (Fin (n + 1) → K) →ₗ[K] K)
    (z z' : Fin (n + 1) → K) (hz : ℓ z = 1) (hz' : ℓ z' = 1)
    (w : Fin n → Fin (n + 1) → K) (hw : ∀ i, ℓ (w i) = 0) :
    ω (vecCons z w) = ω (vecCons z' w) := by
  have hzero := coordinate_topForm_zero_on_kernel ω ℓ z hz (vecCons (z-z') w) (by
    intro i
    cases i using Fin.cases with
    | zero => simp [hz, hz']
    | succ i => exact hw i)
  have he := congrArg (fun f ↦ f w) (ω.curryLeft.map_sub z z')
  exact sub_eq_zero.mp (he.symm.trans hzero)

/-- The relative coordinate top form on the literal polar kernel. -/
def relativeCoordinateTopForm (Q : QuadraticForm K (Fin (n + 1) → K))
    (x : Fin (n + 1) → K) :
    (Q.polarBilin x).ker [⋀^Fin n]→ₗ[K] K :=
  (((Pi.basisFun K (Fin (n + 1))).det).curryLeft ((2 * Q x)⁻¹ • x)).compLinearMap
    (Q.polarBilin x).ker.subtype

theorem relativeCoordinateTopForm_apply
    (Q : QuadraticForm K (Fin (n + 1) → K)) (x : Fin (n + 1) → K)
    (w : Fin n → (Q.polarBilin x).ker) :
    Q.relativeCoordinateTopForm x w =
      (Pi.basisFun K (Fin (n + 1))).det
        (vecCons ((2 * Q x)⁻¹ • x) (fun i ↦ (w i).1)) := rfl

theorem polarBilin_normalLift [CharZero K]
    (Q : QuadraticForm K (Fin (n + 1) → K))
    (x : Fin (n + 1) → K) (hx : Q x ≠ 0) :
    Q.polarBilin x ((2 * Q x)⁻¹ • x) = 1 := by
  simp only [map_smul, polarBilin_apply_apply, polar_self, nsmul_eq_mul,
    Nat.cast_ofNat, smul_eq_mul]
  exact inv_mul_cancel₀ (mul_ne_zero two_ne_zero hx)

/-- Every supplied differential-one lift computes the same relative form. -/
theorem relativeCoordinateTopForm_eq_of_lift [CharZero K]
    (Q : QuadraticForm K (Fin (n + 1) → K)) (x : Fin (n + 1) → K) (hx : Q x ≠ 0)
    (z : Fin (n + 1) → K) (hz : Q.polarBilin x z = 1)
    (w : Fin n → (Q.polarBilin x).ker) :
    Q.relativeCoordinateTopForm x w =
      (Pi.basisFun K (Fin (n + 1))).det (vecCons z (fun i ↦ (w i).1)) := by
  rw [relativeCoordinateTopForm_apply]
  exact coordinate_topForm_lift_independent (Pi.basisFun K (Fin (n + 1))).det
    (Q.polarBilin x) _ z
    (Q.polarBilin_normalLift x hx) hz _ (fun i ↦ (w i).2)

/-- At real/p-adic places the vector used above is the value at one of the
existing continuous right inverse of dQ. -/
theorem relativeCoordinateTopForm_old_rightInverse
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (Q : QuadraticForm K (Fin (n + 1) → K)) (x : Fin (n + 1) → K) :
    Q.valueDifferentialRightInverse x 1 = (2 * Q x)⁻¹ • x := by
  simp [valueDifferentialRightInverse]

/-- A supplied isometry takes the old polar kernel into the corresponding one. -/
def mapPolarTangent (Q Q' : QuadraticForm K (Fin (n + 1) → K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (he : ∀ z, Q' (e z) = Q z) (x : Fin (n + 1) → K)
    (y : (Q.polarBilin x).ker) : (Q'.polarBilin (e x)).ker :=
  ⟨e y.1, by
    change Q'.polarBilin (e x) (e y.1) = 0
    simp only [polarBilin_apply_apply, polar, ← map_add, he]
    exact y.2⟩

/-- Transport keeps the coordinate determinant of the supplied isometry.
An isometry need not have determinant one between distinct form matrices. -/
theorem relativeCoordinateTopForm_transport
    (Q Q' : QuadraticForm K (Fin (n + 1) → K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (he : ∀ z, Q' (e z) = Q z) (x : Fin (n + 1) → K)
    (w : Fin n → (Q.polarBilin x).ker) :
    Q'.relativeCoordinateTopForm (e x) (fun i ↦ mapPolarTangent Q Q' e he x (w i)) =
      LinearMap.det e.toLinearMap * Q.relativeCoordinateTopForm x w := by
  simp only [relativeCoordinateTopForm_apply, mapPolarTangent, he]
  rw [show vecCons ((2 * Q x)⁻¹ • e x) (fun i ↦ e (w i).1) =
      e.toLinearMap ∘ vecCons ((2 * Q x)⁻¹ • x) (fun i ↦ (w i).1) by
    funext i
    cases i using Fin.cases <;> simp]
  exact (Pi.basisFun K (Fin (n + 1))).det_comp e.toLinearMap _

end QuadraticMap

namespace RationalQuadraticSpaceMatrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The normal-first determinant ignores the last entries of the other rows. -/
theorem coordinateDet_last_normal_snoc (c : K) (w : Fin n → Fin n → K)
    (v : Fin n → K) :
    (Pi.basisFun K (Fin (n + 1))).det
      (vecCons (c • (lastCoordinateVector : Fin (n + 1) → K))
        (fun i ↦ Fin.snoc (w i) (v i))) =
      (-1 : K)^n * c * (Pi.basisFun K (Fin n)).det w := by
  rw [Pi.basisFun_det_apply, Matrix.det_succ_row_zero, Pi.basisFun_det_apply]
  simp [Matrix.of_apply, lastCoordinateVector, Pi.single_apply, Matrix.submatrix]

/-- The sign is from placing the last-coordinate normal first. -/
theorem coordinateDet_last_normal (c : K) (w : Fin n → Fin n → K) :
    (Pi.basisFun K (Fin (n + 1))).det
        (vecCons (c • (lastCoordinateVector : Fin (n + 1) → K))
          (fun i ↦ Fin.snoc (w i) 0)) =
      (-1 : K)^n * c * (Pi.basisFun K (Fin n)).det w := by
  exact coordinateDet_last_normal_snoc c w (fun _ ↦ 0)

theorem nonisotropicLastBlockMatrix_mulVec_last
    (F : Matrix (Fin n) (Fin n) K) (a : K) :
    mulVec (nonisotropicLastBlockMatrix F a) lastCoordinateVector =
      a • (lastCoordinateVector : Fin (n + 1) → K) := by
  rw [lastCoordinateVector, mulVec_single_one]
  ext i
  cases i using Fin.lastCases <;> simp [Matrix.col]

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

theorem nonisotropicLastExtension_quadratic_last [CharZero K] :
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K
      lastCoordinateVector = algebraMap ℚ K a := by
  rw [commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue,
    nonisotropicLastExtension_mappedFormMatrix]
  simp [gramQuadraticValue, lastCoordinateVector]

theorem nonisotropicLastExtension_polar_last [CharZero K]
    (y : Fin (n + 1) → K) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin
      lastCoordinateVector y = 2 * algebraMap ℚ K a * y (Fin.last n) := by
  rw [QuadraticMap.polarBilin_apply_apply,
    commutativeScalarExtensionQuadraticForm_polar_eq_gram,
    nonisotropicLastExtension_mappedFormMatrix, nonisotropicLastBlockMatrix_mulVec_last]
  simp [lastCoordinateVector, mul_assoc]

/-- The old last-coordinate tangent, now typed in the literal polar kernel. -/
def nonisotropicLastPolarTangent [CharZero K] (y : Fin n → K) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin
      lastCoordinateVector).ker :=
  ⟨Fin.snoc y 0, by rw [LinearMap.mem_ker, W.nonisotropicLastExtension_polar_last]; simp⟩

/-- The relative vector/value form on the supplied block: the full scalar is
`(-1)^n / (2a)`, with no group or stabilizer normalization folded into it. -/
theorem relativeCoordinateTopForm_nonisotropicLastExtension [CharZero K]
    (w : Fin n → Fin n → K) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm
      lastCoordinateVector (fun i ↦ W.nonisotropicLastPolarTangent a ha (w i)) =
        ((-1 : K)^n / (2 * algebraMap ℚ K a)) * (Pi.basisFun K (Fin n)).det w := by
  rw [QuadraticMap.relativeCoordinateTopForm_apply,
    W.nonisotropicLastExtension_quadratic_last]
  simpa only [nonisotropicLastPolarTangent, div_eq_mul_inv] using
    coordinateDet_last_normal ((2 * algebraMap ℚ K a)⁻¹) w

/-- The supplied-block relative form is nonzero, witnessed on the existing
standard coordinate vectors. No new basis is chosen. -/
theorem relativeCoordinateTopForm_nonisotropicLastExtension_ne_zero [CharZero K] :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm
      lastCoordinateVector ≠ 0 := by
  intro hzero
  have he := W.relativeCoordinateTopForm_nonisotropicLastExtension a ha (K := K)
    (Pi.basisFun K (Fin n))
  rw [hzero, AlternatingMap.zero_apply, Module.Basis.det_self, mul_one] at he
  exact (div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero two_ne_zero ((map_ne_zero (algebraMap ℚ K)).mpr ha))) he.symm

set_option backward.isDefEq.respectTransparency false in
/-- The local evaluations really are scalar extensions of one rational
evaluation, including its orientation and denominator. This is not an adelic
product formula for the independent raw group-Haar factors. -/
theorem relativeCoordinateTopForm_nonisotropicLastExtension_scalarExtension [CharZero K]
    (w : Fin n → Fin n → ℚ) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm
      lastCoordinateVector
      (fun i ↦ W.nonisotropicLastPolarTangent a ha (fun j ↦ algebraMap ℚ K (w i j))) =
      algebraMap ℚ K
        (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ).relativeCoordinateTopForm
          lastCoordinateVector (fun i ↦ W.nonisotropicLastPolarTangent a ha (w i))) := by
  rw [W.relativeCoordinateTopForm_nonisotropicLastExtension a ha (K := K)
      (fun i j ↦ algebraMap ℚ K (w i j)),
    W.relativeCoordinateTopForm_nonisotropicLastExtension a ha (K := ℚ) w,
    Pi.basisFun_det_apply, Pi.basisFun_det_apply]
  rw [show (Matrix.of (fun i j ↦ algebraMap ℚ K (w i j))).det =
      algebraMap ℚ K (Matrix.of w).det from
    ((algebraMap ℚ K).map_det (Matrix.of w)).symm]
  simp

end RationalQuadraticSpaceMatrix
