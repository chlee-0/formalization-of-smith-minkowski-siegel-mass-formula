import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleySourceMeasureTransport

/-!
# P-adic Cayley target measures across anisotropic presentations

The canonical identity-centered Cayley homeomorphism transports the already
normalized source differential measure to the exact units-valued
special-orthogonal target.  The presentation square then carries this target
measure by the same reciprocal local tangent modulus as the source measure.

This is a chart-subtype statement.  It does not compare independently chosen
`GSpin` chart domains, glue a full group measure, or transport a finite-adelic
cylinder.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {m : ℕ}

local instance padicCayleyTargetMeasureModelMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTargetMeasureModelBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTargetMeasureGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTargetMeasureGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The fixed differential measure on the exact identity-centered p-adic
Cayley target, written in the native units-valued special-orthogonal carrier. -/
def padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (padicCayleySpecialOrthogonalSubgroupInverseDomain W.pairingMatrix p) :=
  Measure.map
    (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
      W p)
    (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
      p (m + 1) W.pairingMatrix)

end RationalQuadraticSpaceMatrix
