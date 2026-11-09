import SMSFormula.QuadraticPadicCayleyOrbitFormComparison
import SMSFormula.QuadraticSquareBranchRelativeTopForm
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The moving Cayley orbit differential in the value-branch frame.
The exact overlap is supplied. No branch inverse, chart or section is chosen;
the Jacobian between the two tangent frames is kept explicit. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped ENNReal NNReal Matrix.Norms.Operator

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)

/-- On the existing graph overlap the actual moving orbit form is the full
variable graph coefficient times its lower-coordinate derivative determinant. -/
theorem lastCayley_relative_graph
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (H : Fin n → skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    (W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) H =
      ((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
        ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
          lastCoordinateVector) (Fin.last n))) *
        (Pi.basisFun ℚ_[p] (Fin n)).det
          (fun i j ↦ (W.nonisotropicLastExtension a ha).cayleyOrbitDerivative p X
            lastCoordinateVector (H i) j.castSucc) := by
  let V := W.nonisotropicLastExtension a ha
  let hx : V.commutativeScalarExtensionQuadraticForm ℚ_[p] lastCoordinateVector ≠ 0 := by
    rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha
  let y := V.cayleyOrbitVectorEquiv p X hX lastCoordinateVector
  have hq : V.commutativeScalarExtensionQuadraticForm ℚ_[p] y ≠ 0 := by
    rw [V.cayleyOrbitVectorEquiv_value p X hX]
    exact hx
  change (V.commutativeScalarExtensionQuadraticForm ℚ_[p]).relativeCoordinateTopForm y
    (fun i ↦ V.cayleyOrbitPolarTangentLinearMap p X hX lastCoordinateVector hx (H i)) = _
  have he : (fun i ↦ V.cayleyOrbitPolarTangentLinearMap p X hX lastCoordinateVector hx (H i)) =
      (fun i ↦ W.lastValueTangent a ha y hs (fun j ↦
        V.cayleyOrbitDerivative p X lastCoordinateVector (H i) j.castSucc)) := by
    funext i
    exact (W.lastValueTangent_unique a ha y hs
      (V.cayleyOrbitPolarTangentLinearMap p X hX lastCoordinateVector hx (H i))).symm
  rw [he, W.relativeCoordinateTopForm_lastValueTangent a ha y hs hq]

/-- On a supplied overlap with the square branch, the full moving
relative density equals the branch density times the actual transverse
Jacobian. Neither the inverse square root nor that Jacobian is omitted. -/
theorem lastCayley_relative_eq_branchDensity
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain
      p lastCoordinateVector (algebraMap ℚ ℚ_[p] a))
    (hz : (W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX lastCoordinateVector =
      (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap
        p lastCoordinateVector
        (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (algebraMap ℚ ℚ_[p] a) z).1)
    (H : Fin n → skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) H‖₊ : ℝ≥0∞) =
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberJacobianInverse
        p lastCoordinateVector (algebraMap ℚ ℚ_[p] a) z.1 *
        (‖(Pi.basisFun ℚ_[p] (Fin n)).det
          (fun i j ↦ (W.nonisotropicLastExtension a ha).cayleyOrbitDerivative p X
            lastCoordinateVector (H i) j.castSucc)‖₊ : ℝ≥0∞) := by
  have hs := W.padicSquareBranch_last_coordinate_ne_zero a ha p (algebraMap ℚ ℚ_[p] a) z
  have hvalue : algebraMap ℚ ℚ_[p] a ≠ 0 := (map_ne_zero _).mpr ha
  have hd := W.padicSquareBranch_relativeForm_eq_jacobian a ha p (algebraMap ℚ ℚ_[p] a) z hvalue
  dsimp only at hd hs
  rw [W.relativeCoordinateTopForm_lastValueTangent a ha _ hs
    (by exact (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap
      p lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (algebraMap ℚ ℚ_[p] a) z).property.trans_ne hvalue),
    Module.Basis.det_self, mul_one] at hd
  rw [W.lastCayley_relative_graph a ha p X hX (by rw [hz]; exact hs) H, nnnorm_mul, ENNReal.coe_mul, hz, hd]

end RationalQuadraticSpaceMatrix
