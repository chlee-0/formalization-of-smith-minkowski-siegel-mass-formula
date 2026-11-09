import SMSFormula.RationalCliffordSpinCandidatePlacewiseHaar
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
import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup

/-!
# Differential-coordinate charts for the Spin candidate

The real and p-adic Spin-to-special-orthogonal maps are already open local
homeomorphisms.  This file composes chosen identity charts for those maps
with the established special-orthogonal differential coordinates.  The
resulting charts have values in the concrete skew-adjoint tangent and, after
one further linear homeomorphism, in the scalar-extended algebraic Spin
tangent.

At the p-adic places the special-orthogonal coordinate is the inverse Cayley
chart.  It is packaged below as an ambient open partial homeomorphism by
composing the two open subtype inclusions with the completed homeomorphism of
the exact source and target subtypes.

The algebraic point-map differential theorem identifies the tangent linear
map used here with the etale tangent comparison.  It does not turn the Spin
point carrier into a normed manifold.  Accordingly this file makes no
Frechet-derivative or change-of-variables assertion, and it does not identify
the placewise Spin Haar measures with top-form measures.
-/

noncomputable section

open MeasureTheory
open Topology
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance differentialCoordinateRealSkewAdjointMeasurableSpace :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

noncomputable local instance differentialCoordinateRealSkewAdjointBorelSpace :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

noncomputable local instance differentialCoordinatePadicSkewAdjointMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

noncomputable local instance differentialCoordinatePadicSkewAdjointBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-! ## Real differential coordinates -/

/-- The identity-centered real Spin chart with values in the concrete
skew-adjoint tangent of `SO`. -/
noncomputable def realCliffordSpinCandidateSkewAdjointIdentityChart :
    OpenPartialHomeomorph V.RealCliffordSpinCandidateGroup
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  V.realCliffordSpinCandidateIdentityChart.trans
    (specialFormPreservingSmoothRealIdentityChart
      V.pairingMatrix V.form_symm V.form_det_ne_zero)

@[simp]
theorem realCliffordSpinCandidateSkewAdjointIdentityChart_apply
    (x : V.RealCliffordSpinCandidateGroup) :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart x =
      specialFormPreservingSmoothRealIdentityChart
        V.pairingMatrix V.form_symm V.form_det_ne_zero
        (V.realCliffordSpinCandidateToSpecialOrthogonalHom x) := by
  rw [realCliffordSpinCandidateSkewAdjointIdentityChart,
    OpenPartialHomeomorph.trans_apply]
  congr 1
  exact congrFun V.realCliffordSpinCandidateIdentityChart_coe.symm x

@[simp]
theorem one_mem_realCliffordSpinCandidateSkewAdjointIdentityChart_source :
    (1 : V.RealCliffordSpinCandidateGroup) ∈
      V.realCliffordSpinCandidateSkewAdjointIdentityChart.source := by
  rw [realCliffordSpinCandidateSkewAdjointIdentityChart,
    OpenPartialHomeomorph.trans_source]
  refine ⟨V.one_mem_realCliffordSpinCandidateIdentityChart_source, ?_⟩
  change V.realCliffordSpinCandidateIdentityChart 1 ∈
    (specialFormPreservingSmoothRealIdentityChart
      V.pairingMatrix V.form_symm V.form_det_ne_zero).source
  rw [← congrFun V.realCliffordSpinCandidateIdentityChart_coe 1]
  simpa using
    (self_mem_specialFormPreservingSmoothRealChart_source
      V.pairingMatrix V.form_symm V.form_det_ne_zero (1 : V.RealSpecialOrthogonalGroup))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem realCliffordSpinCandidateSkewAdjointIdentityChart_one :
    V.realCliffordSpinCandidateSkewAdjointIdentityChart
        (1 : V.RealCliffordSpinCandidateGroup) = 0 := by
  rw [V.realCliffordSpinCandidateSkewAdjointIdentityChart_apply]
  simpa only [map_one] using
    specialFormPreservingSmoothRealChart_center V.pairingMatrix V.form_symm
      V.form_det_ne_zero (1 : V.RealSpecialOrthogonalGroup)

/-! ## The p-adic special-orthogonal inverse Cayley chart -/

/-- The open inclusion of the identity-centered p-adic Cayley target into
the full units-valued special-orthogonal group. -/
noncomputable def padicSpecialOrthogonalCayleyTargetInclusion
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (padicCayleySpecialOrthogonalTranslatedTarget V.pairingMatrix p 1)
      (V.specialOrthogonalMatrixGroup ℚ_[p]) := by
  letI : Nonempty
      (padicCayleySpecialOrthogonalTranslatedTarget V.pairingMatrix p 1) :=
    ⟨⟨1, self_mem_padicCayleySpecialOrthogonalTranslatedTarget
      V.pairingMatrix p 1⟩⟩
  exact
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      V.pairingMatrix p 1).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
        Subtype.val

/-- The open inclusion of the exact p-adic Cayley source into the full
skew-adjoint tangent. -/
noncomputable def padicSkewAdjointCayleySourceInclusion
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (Matrix.skewAdjointPadicCayleySource V.pairingMatrix p)
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : Nonempty (Matrix.skewAdjointPadicCayleySource V.pairingMatrix p) :=
    ⟨⟨0, Matrix.zero_mem_skewAdjointPadicCayleySource V.pairingMatrix p⟩⟩
  exact
    (Matrix.isOpen_skewAdjointPadicCayleySource
      V.pairingMatrix p).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
        Subtype.val

/-- The p-adic inverse Cayley coordinate as an ambient open partial
homeomorphism from `SO(ℚ_p)` to its skew-adjoint tangent. -/
noncomputable def padicSpecialOrthogonalCayleyIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph (V.specialOrthogonalMatrixGroup ℚ_[p])
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (V.padicSpecialOrthogonalCayleyTargetInclusion p).symm.trans
    ((skewAdjointPadicCayleyTranslatedHomeomorph
      V.pairingMatrix p V.form_det_ne_zero 1).symm.toOpenPartialHomeomorph.trans
        (V.padicSkewAdjointCayleySourceInclusion p))

@[simp]
theorem padicSpecialOrthogonalCayleyIdentityChart_source
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicSpecialOrthogonalCayleyIdentityChart p).source =
      padicCayleySpecialOrthogonalTranslatedTarget V.pairingMatrix p 1 := by
  simp [padicSpecialOrthogonalCayleyIdentityChart,
    padicSpecialOrthogonalCayleyTargetInclusion,
    padicSkewAdjointCayleySourceInclusion]
  exact Subtype.range_val

@[simp]
theorem padicSpecialOrthogonalCayleyIdentityChart_target
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicSpecialOrthogonalCayleyIdentityChart p).target =
      Matrix.skewAdjointPadicCayleySource V.pairingMatrix p := by
  simp [padicSpecialOrthogonalCayleyIdentityChart,
    padicSpecialOrthogonalCayleyTargetInclusion,
    padicSkewAdjointCayleySourceInclusion]

@[simp]
theorem one_mem_padicSpecialOrthogonalCayleyIdentityChart_source
    (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : V.specialOrthogonalMatrixGroup ℚ_[p]) ∈
      (V.padicSpecialOrthogonalCayleyIdentityChart p).source := by
  rw [V.padicSpecialOrthogonalCayleyIdentityChart_source]
  exact self_mem_padicCayleySpecialOrthogonalTranslatedTarget
    V.pairingMatrix p 1

/-- On its exact source, the ambient p-adic coordinate chart is the literal
inverse Cayley formula. -/
theorem padicSpecialOrthogonalCayleyIdentityChart_apply_coe
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.specialOrthogonalMatrixGroup ℚ_[p])
    (hg : g ∈ (V.padicSpecialOrthogonalCayleyIdentityChart p).source) :
    ((V.padicSpecialOrthogonalCayleyIdentityChart p g :
        (skewAdjointMatricesLieSubalgebra
          (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[p]) =
      (((g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        ((g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) := by
  let eT := V.padicSpecialOrthogonalCayleyTargetInclusion p
  let H := skewAdjointPadicCayleyTranslatedHomeomorph
    V.pairingMatrix p V.form_det_ne_zero 1
  have hgT : g ∈ eT.target := by
    have h := hg
    rw [padicSpecialOrthogonalCayleyIdentityChart,
      OpenPartialHomeomorph.trans_source] at h
    exact h.1
  have hval : (eT.symm g).1 = g := by
    have h := eT.right_inv hgT
    simpa [eT, padicSpecialOrthogonalCayleyTargetInclusion] using h
  change (((H.symm (eT.symm g)).1 :
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
        Matrix (Fin n) (Fin n) ℚ_[p]) = _
  rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_symm_apply]
  rw [hval]
  simp

@[simp]
theorem padicSpecialOrthogonalCayleyIdentityChart_one
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.padicSpecialOrthogonalCayleyIdentityChart p
        (1 : V.specialOrthogonalMatrixGroup ℚ_[p]) = 0 := by
  apply Subtype.ext
  ext i j
  have h := V.padicSpecialOrthogonalCayleyIdentityChart_apply_coe p 1
    (V.one_mem_padicSpecialOrthogonalCayleyIdentityChart_source p)
  simpa using congrFun (congrFun h i) j

/-! ## P-adic Spin coordinates -/

/-- The identity-centered p-adic Spin chart with values in the concrete
skew-adjoint tangent. -/
noncomputable def padicCliffordSpinCandidateSkewAdjointIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph (V.PadicCliffordSpinCandidateGroup p)
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (V.padicCliffordSpinCandidateIdentityChart p).trans
    (V.padicSpecialOrthogonalCayleyIdentityChart p)

@[simp]
theorem one_mem_padicCliffordSpinCandidateSkewAdjointIdentityChart_source
    (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : V.PadicCliffordSpinCandidateGroup p) ∈
      (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source := by
  rw [padicCliffordSpinCandidateSkewAdjointIdentityChart,
    OpenPartialHomeomorph.trans_source]
  refine ⟨V.one_mem_padicCliffordSpinCandidateIdentityChart_source p, ?_⟩
  change V.padicCliffordSpinCandidateIdentityChart p 1 ∈
    (V.padicSpecialOrthogonalCayleyIdentityChart p).source
  rw [← congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p) 1]
  simpa using V.one_mem_padicSpecialOrthogonalCayleyIdentityChart_source p

@[simp]
theorem padicCliffordSpinCandidateSkewAdjointIdentityChart_one
    (p : ℕ) [Fact (Nat.Prime p)] :
    V.padicCliffordSpinCandidateSkewAdjointIdentityChart p
        (1 : V.PadicCliffordSpinCandidateGroup p) = 0 := by
  rw [padicCliffordSpinCandidateSkewAdjointIdentityChart,
    OpenPartialHomeomorph.trans_apply]
  rw [← congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p) 1]
  simp

/-! ## Coordinates in the algebraic Spin tangent -/

/-! ## Exact coordinate-density measures -/

/-- The real `SO` chart density restricted to the exact target of the
composite Spin-to-skew-adjoint chart. -/
noncomputable def realCliffordSpinCandidateSkewAdjointIdentityChartDensity
    (y : V.realCliffordSpinCandidateSkewAdjointIdentityChart.target) : ℝ≥0∞ :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    V.pairingMatrix V.form_symm V.form_det_ne_zero 1
    ⟨y.1, by
      have hy := y.2
      change y.1 ∈
        (V.realCliffordSpinCandidateIdentityChart.trans
          (specialFormPreservingSmoothRealIdentityChart
            V.pairingMatrix V.form_symm V.form_det_ne_zero)).target at hy
      rw [OpenPartialHomeomorph.trans_target] at hy
      exact hy.1⟩

/-- In real skew-adjoint coordinates, the Spin chart measure is the
established nonlinear `SO` density over the normalized tangent top-form
measure. -/
noncomputable def realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure :
    Measure V.realCliffordSpinCandidateSkewAdjointIdentityChart.target :=
  (Measure.comap Subtype.val
      (Matrix.skewAdjointRealCoordinateDetMeasure V.pairingMatrix 0)).withDensity
    V.realCliffordSpinCandidateSkewAdjointIdentityChartDensity

/-- Pull the exact real coordinate-density measure back to the composite
Spin chart source. -/
noncomputable def realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure :
    Measure V.realCliffordSpinCandidateSkewAdjointIdentityChart.source :=
  Measure.map
    V.realCliffordSpinCandidateSkewAdjointIdentityChart.toHomeomorphSourceTarget.symm
    V.realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure

/-- Forward real Spin coordinates recover the exact density over the
normalized skew-adjoint tangent measure. -/
theorem map_realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure :
    Measure.map
        V.realCliffordSpinCandidateSkewAdjointIdentityChart.toHomeomorphSourceTarget
        V.realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure =
      V.realCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure := by
  rw [realCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (V.realCliffordSpinCandidateSkewAdjointIdentityChart
      |>.toHomeomorphSourceTarget.toMeasurableEquiv)

/-- The p-adic inverse-Cayley density restricted to the exact target of the
composite Spin-to-skew-adjoint chart. -/
noncomputable def padicCliffordSpinCandidateSkewAdjointIdentityChartDensity
    (p : ℕ) [Fact (Nat.Prime p)]
    (y : (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target) :
    ℝ≥0∞ :=
  Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
    p n V.pairingMatrix
    ⟨y.1, by
      have hy := y.2
      change y.1 ∈
        ((V.padicCliffordSpinCandidateIdentityChart p).trans
          (V.padicSpecialOrthogonalCayleyIdentityChart p)).target at hy
      rw [OpenPartialHomeomorph.trans_target] at hy
      simpa using hy.1⟩

/-- In p-adic skew-adjoint coordinates, the Spin chart measure is the exact
inverse-Cayley differential density over the rationally normalized additive
Haar measure. -/
noncomputable def padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target :=
  (Measure.comap Subtype.val
      (Matrix.skewAdjointPadicCoordinateMeasure V.pairingMatrix p)).withDensity
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChartDensity p)

/-- Pull the exact p-adic coordinate-density measure back to the composite
Spin chart source. -/
noncomputable def padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source :=
  Measure.map
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
      p).toHomeomorphSourceTarget.symm
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure p)

/-- Forward p-adic Spin coordinates recover the exact density over the
normalized skew-adjoint tangent measure. -/
theorem map_padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
          p).toHomeomorphSourceTarget
        (V.padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure p) =
      V.padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure p := by
  rw [padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart
      p).toHomeomorphSourceTarget.toMeasurableEquiv

/-! ## Transport of coordinate densities to the Spin tangent -/

end RationalQuadraticSpaceMatrix
