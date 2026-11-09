import SMSFormula.QuadraticOrbitRelativeTopForm
import SMSFormula.QuadraticComplement
import SMSFormula.PadicCayleyLeftTrivializedDetNonzero
import SMSFormula.PadicCayleySpecialOrthogonal

/-!
# The orbit differential throughout the p-adic Cayley source

The full derivative is retained at every source point, not replaced by its
value at zero. Its orbit differential is transported by the Cayley matrix;
relative-form invariance then identifies its pullback with the orbit form
composed with the full left-trivialized derivative.
-/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped Matrix.Norms.Operator

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (V : RationalQuadraticSpaceMatrix (n + 1))
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource V.pairingMatrix p)

/-- The Cayley matrix acting on vectors, packaged as its literal linear
equivalence. Its inverse is the matrix inverse, not a chosen orbit lift. -/
def cayleyOrbitVectorEquiv : (Fin (n + 1) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin (n + 1) → ℚ_[p]) :=
  (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.mkOfDetNeZero
    (skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X)
    (by rw [skewAdjointPadicCayleyForwardMatrix_det_one _ _ V.form_det_ne_zero X hX]; exact one_ne_zero))).toLinearEquiv

@[simp] theorem cayleyOrbitVectorEquiv_apply (y : Fin (n + 1) → ℚ_[p]) :
    V.cayleyOrbitVectorEquiv p X hX y =
      Matrix.mulVec (skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X) y := rfl

theorem cayleyOrbitVectorEquiv_det :
    LinearMap.det (V.cayleyOrbitVectorEquiv p X hX).toLinearMap = 1 := by
  change LinearMap.det (Matrix.mulVecLin
    (skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X)) = 1
  exact (LinearMap.det_toLin' _).trans
    (skewAdjointPadicCayleyForwardMatrix_det_one _ _ V.form_det_ne_zero X hX)

/-- Exact value preservation by the same matrix as in the derivative. -/
theorem cayleyOrbitVectorEquiv_value (y : Fin (n + 1) → ℚ_[p]) :
    V.commutativeScalarExtensionQuadraticForm ℚ_[p] (V.cayleyOrbitVectorEquiv p X hX y) =
      V.commutativeScalarExtensionQuadraticForm ℚ_[p] y := by
  simp only [commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue,
    cayleyOrbitVectorEquiv_apply]
  exact gramQuadraticValue_mulVec_of_congr _ _
    (Matrix.GeneralLinearGroup.mkOfDetNeZero
      (skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X)
      (by rw [skewAdjointPadicCayleyForwardMatrix_det_one _ _ V.form_det_ne_zero X hX]; exact one_ne_zero))
    (skewAdjointPadicCayleyForwardMatrix_formPreserving _ _ X hX) y

/-- Undoing the actual left translation recovers the full forward derivative. -/
theorem cayleyOrbit_forwardDerivative
    (H : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    skewAdjointPadicCayleyForwardDerivative V.pairingMatrix p X H =
      skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X *
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism V.pairingMatrix p X hX H).1 := by
  have hg : IsUnit (skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X).det := by
    rw [skewAdjointPadicCayleyForwardMatrix_det_one _ _ V.form_det_ne_zero X hX]
    exact isUnit_one
  change _ = _ * (skewAdjointPadicCayleyLeftTrivializedDerivative V.pairingMatrix p X H)
  change _ = _ * ((_⁻¹ * skewAdjointPadicCayleyForwardDerivative V.pairingMatrix p X H) * 1)
  rw [Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

/-- The actual orbit derivative, as a continuous linear map. -/
def cayleyOrbitDerivative (x : Fin (n + 1) → ℚ_[p]) :
    skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p]) →L[ℚ_[p]]
      (Fin (n + 1) → ℚ_[p]) :=
  (((Matrix.mulVecBilin ℚ_[p] ℚ_[p]).flip x).toContinuousLinearMap).comp
    (skewAdjointPadicCayleyForwardDerivative V.pairingMatrix p X)

include hX in
/-- This is a derivative of the nonlinear orbit map, not merely a
pointwise matrix identity. -/
theorem hasFDerivAt_cayleyOrbit (x : Fin (n + 1) → ℚ_[p]) :
    HasFDerivAt (fun Z ↦ Matrix.mulVec (skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p Z) x)
      (V.cayleyOrbitDerivative p X x) X := by
  exact (((Matrix.mulVecBilin ℚ_[p] ℚ_[p]).flip x).toContinuousLinearMap.hasFDerivAt).comp X
    (hasFDerivAt_skewAdjointPadicCayleyForwardMatrix V.pairingMatrix p X hX)

/-- Literal orbit derivative = Cayley vector action after the full
left-trivialized tangent endomorphism and the orbit tangent. -/
theorem cayleyOrbitDerivative_apply (x : Fin (n + 1) → ℚ_[p])
    (H : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    V.cayleyOrbitDerivative p X x H =
      V.cayleyOrbitVectorEquiv p X hX
        (Matrix.mulVec (skewAdjointPadicCayleyLeftTrivializedEndomorphism V.pairingMatrix p X hX H).1 x) := by
  change Matrix.mulVec (skewAdjointPadicCayleyForwardDerivative V.pairingMatrix p X H) x = _
  rw [V.cayleyOrbit_forwardDerivative p X hX H, ← Matrix.mulVec_mulVec]
  rfl

/-- The inverse differential exposes the actual moving orbit tangent.
It is only a linear inverse at X, not a nonlinear inverse or a section. -/
theorem cayleyOrbitDerivative_inverse (x : Fin (n + 1) → ℚ_[p])
    (A : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    V.cayleyOrbitDerivative p X x
      (skewAdjointPadicCayleyLeftTrivializedInverse V.pairingMatrix p X A) =
        V.cayleyOrbitVectorEquiv p X hX (Matrix.mulVec A.1 x) := by
  rw [V.cayleyOrbitDerivative_apply p X hX,
    skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply_inverse
      V.pairingMatrix p V.form_det_ne_zero X A hX]

variable (x : Fin (n + 1) → ℚ_[p])
    (hx : V.commutativeScalarExtensionQuadraticForm ℚ_[p] x ≠ 0)

/-- The actual derivative has its image in the literal tangent of the moving
fiber point. No tangent projection or choice of complement is used. -/
def cayleyOrbitPolarTangentLinearMap :
    skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p]) →ₗ[ℚ_[p]]
      ((V.commutativeScalarExtensionQuadraticForm ℚ_[p]).polarBilin
        (V.cayleyOrbitVectorEquiv p X hX x)).ker :=
  (V.cayleyOrbitDerivative p X x).toLinearMap.codRestrict _ (fun H ↦ by
    change (V.commutativeScalarExtensionQuadraticForm ℚ_[p]).polarBilin _
      (V.cayleyOrbitDerivative p X x H) = 0
    rw [V.cayleyOrbitDerivative_apply p X hX x H]
    exact (mapPolarTangent _ _ (V.cayleyOrbitVectorEquiv p X hX)
      (V.cayleyOrbitVectorEquiv_value p X hX) x
      (V.orbitPolarTangentLinearMap ℚ_[p] x hx
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism V.pairingMatrix p X hX H))).2)

/-- Relative form pulled through the actual nonlinear orbit derivative. -/
def cayleyOrbitRelativeTopForm :=
  ((V.commutativeScalarExtensionQuadraticForm ℚ_[p]).relativeCoordinateTopForm
    (V.cayleyOrbitVectorEquiv p X hX x)).compLinearMap
      (V.cayleyOrbitPolarTangentLinearMap p X hX x hx)

/-- Pointwise throughout the chart, the relative orbit form consumes the
full varying Cayley differential. Determinant one is the vector action only. -/
theorem cayleyOrbitRelativeTopForm_apply
    (H : Fin n → skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    V.cayleyOrbitRelativeTopForm p X hX x hx H =
      V.orbitRelativeCoordinateTopForm ℚ_[p] x hx
        (fun i ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism V.pairingMatrix p X hX (H i)) := by
  unfold cayleyOrbitRelativeTopForm
  rw [AlternatingMap.compLinearMap_apply]
  have ht : (fun i ↦ V.cayleyOrbitPolarTangentLinearMap p X hX x hx (H i)) =
      (fun i ↦ mapPolarTangent _ _ (V.cayleyOrbitVectorEquiv p X hX)
        (V.cayleyOrbitVectorEquiv_value p X hX) x
        (V.orbitPolarTangentLinearMap ℚ_[p] x hx
          (skewAdjointPadicCayleyLeftTrivializedEndomorphism V.pairingMatrix p X hX (H i)))) := by
    funext i
    apply Subtype.ext
    exact V.cayleyOrbitDerivative_apply p X hX x (H i)
  rw [ht, relativeCoordinateTopForm_transport, V.cayleyOrbitVectorEquiv_det p X hX, one_mul]
  rfl

/-- The already explicit inverse differential recovers the orbit form
at every point, with no new inverse chart or section. -/
theorem cayleyOrbitRelativeTopForm_inverse
    (A : Fin n → skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    V.cayleyOrbitRelativeTopForm p X hX x hx
      (fun i ↦ skewAdjointPadicCayleyLeftTrivializedInverse V.pairingMatrix p X (A i)) =
        V.orbitRelativeCoordinateTopForm ℚ_[p] x hx A := by
  rw [V.cayleyOrbitRelativeTopForm_apply p X hX x hx]
  simp only [skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply_inverse
    V.pairingMatrix p V.form_det_ne_zero X _ hX]

end RationalQuadraticSpaceMatrix
