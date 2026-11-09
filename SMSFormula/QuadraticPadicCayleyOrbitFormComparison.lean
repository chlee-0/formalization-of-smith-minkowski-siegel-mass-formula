import SMSFormula.QuadraticPadicCayleyOrbitDifferential
import SMSFormula.QuadraticOrbitDeterminantComparison
import SMSFormula.RationalCliffordSpinBlockIdentityTangent
import SMSFormula.RationalCliffordSpinCandidateCanonicalMapIso
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import SMSFormula.RationalCliffordSpinCandidateFppf
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SMSFormula.RationalCliffordSpinCandidateCoordinateHopf
import SMSFormula.RationalSpecialOrthogonalTamagawa
import Mathlib.Data.Matrix.DualNumber
import SMSFormula.RationalSpecialOrthogonalDifferentialNormalization
import SMSFormula.SpecialOrthogonalRealChartMeasure
import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyCoordinateJacobianDensityENNRealPositive
import SMSFormula.PadicCayleyDomainOpenness
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter
import SMSFormula.PadicCayleyLeftTrivializedInversePowerDeterminant
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.PadicCayleyLeftTrivializedInverseModulus
import SMSFormula.PadicCayleyTangentModulus
import SMSFormula.SkewAdjointCongruenceNormalization
import SMSFormula.PadicCayleyTranslatedChartDifferentialRegularity
import SMSFormula.PadicCayleyLeftTrivializedDeterminantModulus

/-!
# Group/stabilizer/relative forms on the full p-adic Cayley differential

Use the already explicit inverse differential to express the old lower-first
frame in the chart's tangent coordinates. This is a frame at one point,
not a nonlinear product chart or a section. The full old source density times
the coordinate-frame determinant equals the rational ratio times the
stabilizer form and the moving relative-form pullback.
-/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped ENNReal NNReal Matrix.Norms.Operator

namespace RationalQuadraticSpaceMatrix
/-- Recognition of the full chart density, including its variable
Cayley denominator and dyadic factor. This makes no density constant. -/
theorem cayleySourceDensity_eq_det {m : ℕ} (V : RationalQuadraticSpaceMatrix m)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : skewAdjointMatricesLieSubalgebra (V.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource V.pairingMatrix p) :
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p m
      V.pairingMatrix ⟨X,hX⟩ =
        (‖LinearMap.det (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          V.pairingMatrix p X hX).toLinearMap‖₊ : ℝ≥0∞) := by
  rw [skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe]
  congr 1
  unfold skewAdjointPadicCayleySourceDifferentialDensityNNReal
  rw [skewAdjointPadicCayleyCoordinateJacobianDensity_eq_inv_nnnorm
    V.pairingMatrix p
    V.form_symm
    V.form_det_ne_zero X hX, inv_inv]

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)

/-- The lower-first frame expressed using the inverse differential
at X. It varies with X; it is not the derivative of an asserted product chart. -/
def lastCayleyInverseFrame
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (w : Fin n → Fin n → ℚ_[p]) :=
  fun i ↦ skewAdjointPadicCayleyLeftTrivializedInverse
    (W.nonisotropicLastExtension a ha).pairingMatrix p X
      (Sum.elim (fun j ↦ W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] (u j))
        (fun j ↦ W.lastOrbitLift a ha ℚ_[p] (w j)) i)

/-- Exact kernel of the actual nonlinear orbit derivative: the preimage
of the stabilizer tangent under the full left-trivialized derivative. -/
theorem lastCayley_orbitDerivative_eq_zero_iff
    (H : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    (W.nonisotropicLastExtension a ha).cayleyOrbitDerivative p X lastCoordinateVector H = 0 ↔
      skewAdjointPadicCayleyLeftTrivializedEndomorphism
        (W.nonisotropicLastExtension a ha).pairingMatrix p X hX H ∈
          W.nonisotropicLastSkewAdjointFiber a ha ℚ_[p] := by
  rw [cayleyOrbitDerivative_apply _ p X hX]
  rw [LinearEquiv.map_eq_zero_iff]
  exact (W.mem_nonisotropicLastSkewAdjointFiber_iff_orbitTangent_zero a ha ℚ_[p]
    (skewAdjointPadicCayleyLeftTrivializedEndomorphism
      (W.nonisotropicLastExtension a ha).pairingMatrix p X hX H)).symm

include hX in
/-- Stabilizer directions are genuinely vertical for the nonlinear
orbit, after expressing them through the full inverse derivative at X. -/
theorem lastCayley_inverseFrame_vertical
    (u : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :
    (W.nonisotropicLastExtension a ha).cayleyOrbitDerivative p X lastCoordinateVector
      (skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] u)) = 0 := by
  rw [cayleyOrbitDerivative_inverse _ p X hX]
  have hv : Matrix.mulVec (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] u).1
      lastCoordinateVector = 0 := by
    rw [lastCoordinateVector, Matrix.mulVec_single_one]
    funext i
    exact W.nonisotropicLastSkewAdjointEmbed_mem_fiber a ha ℚ_[p] u i
  rw [hv, map_zero]

/-- The transverse lifts yield the actual Cayley images of the
lower-coordinate frame, not the constant basepoint frame. -/
theorem lastCayley_inverseFrame_transverse (w : Fin n → ℚ_[p]) :
    (W.nonisotropicLastExtension a ha).cayleyOrbitDerivative p X lastCoordinateVector
      (skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X (W.lastOrbitLift a ha ℚ_[p] w)) =
      (W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX (Fin.snoc w 0) := by
  rw [cayleyOrbitDerivative_inverse _ p X hX, W.lastOrbitLift_mulVec]

/-- The moving fiber form on the inverse-differential orbit frame recovers
eta on the transverse frame exactly, at every Cayley source point. -/
theorem lastCayley_relative_inverseFrame (w : Fin n → Fin n → ℚ_[p]) :
    (W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
      lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (fun i ↦ skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X (W.lastOrbitLift a ha ℚ_[p] (w i))) =
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).relativeCoordinateTopForm
        lastCoordinateVector (fun i ↦ W.nonisotropicLastPolarTangent a ha (w i)) := by
  rw [cayleyOrbitRelativeTopForm_inverse]
  exact (W.nonisotropicLastExtension a ha).orbitRelativeCoordinateTopForm_lift
    ℚ_[p] lastCoordinateVector _ (fun i ↦ W.nonisotropicLastPolarTangent a ha (w i))

/-- The chart derivative's determinant is retained when evaluating the
ambient form in chart coordinates, in the unchanged rational basis. -/
theorem lastOrbitGroupForm_cayley_apply
    (A : (Fin (Module.finrank ℚ W.skewAdjointTangent) ⊕ Fin n) →
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    W.lastOrbitGroupForm a ha ℚ_[p]
      (fun i ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism
        (W.nonisotropicLastExtension a ha).pairingMatrix p X hX (A i)) =
      LinearMap.det (skewAdjointPadicCayleyLeftTrivializedEndomorphism
        (W.nonisotropicLastExtension a ha).pairingMatrix p X hX).toLinearMap *
          W.lastOrbitGroupForm a ha ℚ_[p] A := by
  rw [(W.lastOrbitGroupForm a ha ℚ_[p]).eq_smul_basis_det (W.lastOrbitFrame a ha ℚ_[p])]
  change (W.lastOrbitGroupForm a ha ℚ_[p] (W.lastOrbitFrame a ha ℚ_[p])) *
      (W.lastOrbitFrame a ha ℚ_[p]).det
        ((skewAdjointPadicCayleyLeftTrivializedEndomorphism
          (W.nonisotropicLastExtension a ha).pairingMatrix p X hX).toLinearMap ∘ A) =
    _ * ((W.lastOrbitGroupForm a ha ℚ_[p] (W.lastOrbitFrame a ha ℚ_[p])) *
      (W.lastOrbitFrame a ha ℚ_[p]).det A)
  erw [Module.Basis.det_comp (W.lastOrbitFrame a ha ℚ_[p])
    (skewAdjointPadicCayleyLeftTrivializedEndomorphism
      (W.nonisotropicLastExtension a ha).pairingMatrix p X hX).toLinearMap A]
  exact mul_left_comm _ _ _

end RationalQuadraticSpaceMatrix
