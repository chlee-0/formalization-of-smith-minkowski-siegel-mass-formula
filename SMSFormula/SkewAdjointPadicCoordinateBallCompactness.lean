import SMSFormula.SkewAdjointPadicCoordinateBallFiltration
import Mathlib.Topology.Compactness.Lindelof

/-!
# Compactness of p-adic coordinate balls

The transported coordinate lattice is already a compact-open set. Its
uniform dilates and additive translates are therefore compact under the
continuous linear and translation homeomorphisms used to define the
coordinate balls.

This module is purely topological and contains no Haar scaling.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology Pointwise

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every zero-centered uniform coordinate ball is compact. -/
theorem isCompact_skewAdjointPadicUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsCompact (skewAdjointPadicUniformCoordinateBall F p k) := by
  rw [skewAdjointPadicUniformCoordinateBall]
  exact (skewAdjointPadicCoordinateLattice F p).isCompact.image
    (skewAdjointPadicUniformCoordinateDilation F p k).continuous

/-- Every translated uniform coordinate ball is compact. -/
theorem isCompact_skewAdjointPadicTranslatedUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    IsCompact (skewAdjointPadicTranslatedUniformCoordinateBall F p k x) := by
  exact (Homeomorph.addLeft (-x)).isCompact_preimage.mpr
    (isCompact_skewAdjointPadicUniformCoordinateBall F p k)

end Matrix
