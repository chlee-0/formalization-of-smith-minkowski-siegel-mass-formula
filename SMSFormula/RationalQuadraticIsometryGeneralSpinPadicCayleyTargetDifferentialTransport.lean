import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyTargetMeasureTransport

/-!
# P-adic Cayley target differential transport

The canonical p-adic Cayley presentation square carries the fixed target
differential measure by the reciprocal local tangent modulus.  The target
carrier and commuting function square are imported as opaque named data so
kernel checking does not expand their dependent subtype constructions.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace MeasureTheory.Measure

/-- A pointwise commuting measurable square transports a scalar pushforward.
The pointwise interface avoids materializing a potentially large dependent
function equality. -/
theorem map_map_eq_smul_map_of_forall_commutes
    {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (f : A → B) (g : B → D) (h : A → C) (k : C → D)
    (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hk : Measurable k)
    (mu : Measure A) (nu : Measure C) (c : ℝ≥0)
    (hcomm : ∀ a, g (f a) = k (h a))
    (hmap : Measure.map h mu = c • nu) :
    Measure.map g (Measure.map f mu) = c • Measure.map k nu := by
  calc
    Measure.map g (Measure.map f mu) = Measure.map (g ∘ f) mu :=
      Measure.map_map hg hf
    _ = Measure.map (k ∘ h) mu :=
      Measure.map_congr (Filter.Eventually.of_forall hcomm)
    _ = Measure.map k (Measure.map h mu) :=
      (Measure.map_map hk hh).symm
    _ = Measure.map k (c • nu) := by rw [hmap]
    _ = c • Measure.map k nu := Measure.map_smul c nu k

end MeasureTheory.Measure

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance padicCayleyTargetDifferentialModelMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTargetDifferentialModelBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTargetDifferentialGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTargetDifferentialGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The exact presentation map on identity Cayley targets transports the fixed
differential measure by the reciprocal p-adic norm of the rational tangent
determinant. -/
theorem map_blockToAmbientPadicCayleyIdentityTargetDifferentialMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (P.blockToAmbientPadicCayleyIdentityTargetHomeomorph hx p)
        ((P.blockSpace hx)
          |>.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        V.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p := by
  unfold padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure
  apply Measure.map_map_eq_smul_map_of_forall_commutes
    (padicCayleySpecialOrthogonalIdentityHomeomorph (P.blockSpace hx) p)
    (P.blockToAmbientPadicCayleyIdentityTargetHomeomorph hx p)
    (P.blockToAmbientPadicCayleySourceHomeomorph hx p)
    (padicCayleySpecialOrthogonalIdentityHomeomorph V p)
    (padicCayleySpecialOrthogonalIdentityHomeomorph
      (P.blockSpace hx) p).measurable
    (P.blockToAmbientPadicCayleyIdentityTargetHomeomorph hx p).measurable
    (P.blockToAmbientPadicCayleySourceHomeomorph hx p).measurable
    (padicCayleySpecialOrthogonalIdentityHomeomorph V p).measurable
    (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
      p (m + 1) (P.blockSpace hx).pairingMatrix)
    (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
      p (m + 1) V.pairingMatrix)
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  · intro X
    exact P.blockToAmbientPadicCayleyIdentityHomeomorph_commutes hx p X
  · exact P.map_blockToAmbientPadicCayleySourceDifferentialSubtypeMeasure hx p

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
