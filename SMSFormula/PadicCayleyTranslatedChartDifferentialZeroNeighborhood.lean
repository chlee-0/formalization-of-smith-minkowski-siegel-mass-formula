import SMSFormula.PadicCayleyTranslatedChartDifferentialLocalConstancy
import SMSFormula.SkewAdjointPadicCoordinateBallBasis

/-!
# A zero-centered coordinate ball of constant corrected Cayley density

The correctly oriented p-adic Cayley source density at the zero coordinate is
the nonnegative norm of `2` raised to the symbolic skew-adjoint rank.  Local
constancy on the exact Cayley source and the intrinsic uniform coordinate-ball
basis then select one zero-centered ball lying in the source on which this
value is constant.

No principal-congruence depth or stabilizer measure is used here.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialZeroNeighborhoodMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyDifferentialZeroNeighborhoodBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The corrected `NNReal` Cayley source density at zero is the norm of `2`
raised to the symbolic rational skew-adjoint rank. -/
theorem skewAdjointPadicCayleySourceDifferentialDensityNNReal_zero
    (F : Matrix (Fin n) (Fin n) ℚ) :
    skewAdjointPadicCayleySourceDifferentialDensityNNReal p n F
        ⟨0, zero_mem_skewAdjointPadicCayleySource F p⟩ =
      ‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  simp [skewAdjointPadicCayleySourceDifferentialDensityNNReal,
    skewAdjointPadicCayleyCoordinateJacobianDensity]

/-- The literal corrected `ENNReal` Cayley source density has the same
zero-coordinate value. -/
theorem skewAdjointPadicCayleySourceDifferentialDensityENNReal_zero
    (F : Matrix (Fin n) (Fin n) ℚ) :
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
        ⟨0, zero_mem_skewAdjointPadicCayleySource F p⟩ =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) : ℝ≥0∞) := by
  rw [skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe,
    skewAdjointPadicCayleySourceDifferentialDensityNNReal_zero]
  exact ENNReal.coe_pow _ _

/-- One zero-centered uniform coordinate ball lies in the exact Cayley source
and carries the zero-coordinate corrected density everywhere. -/
theorem
    exists_skewAdjointPadicUniformCoordinateBall_subset_cayleySource_const_differentialDensity
    (F : Matrix (Fin n) (Fin n) ℚ) :
    ∃ level : ℕ,
      ∃ hsubset :
          skewAdjointPadicUniformCoordinateBall F p level ⊆
            skewAdjointPadicCayleySource F p,
        ∀ X,
          ∀ hX : X ∈ skewAdjointPadicUniformCoordinateBall F p level,
            skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
                ⟨X, hsubset hX⟩ =
              (‖(2 : ℚ_[p])‖₊ ^
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra F) : ℝ≥0∞) := by
  let zeroSource : skewAdjointPadicCayleySource F p :=
    ⟨0, zero_mem_skewAdjointPadicCayleySource F p⟩
  obtain ⟨V, hVopen, hzeroV, hconst⟩ :=
    (isLocallyConstant_skewAdjointPadicCayleySourceDifferentialDensityENNReal
      p n F).exists_open zeroSource
  have himageOpen : IsOpen (Subtype.val '' V) :=
    (isOpen_skewAdjointPadicCayleySource F p).isOpenEmbedding_subtypeVal.isOpenMap
      V hVopen
  have hzeroImage : (0 :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈ Subtype.val '' V :=
    ⟨zeroSource, hzeroV, rfl⟩
  obtain ⟨level, hball⟩ :=
    exists_skewAdjointPadicUniformCoordinateBall_subset_of_mem_nhds_zero
      F p (himageOpen.mem_nhds hzeroImage)
  have hsubset :
      skewAdjointPadicUniformCoordinateBall F p level ⊆
        skewAdjointPadicCayleySource F p := by
    intro X hX
    rcases hball hX with ⟨Y, hYV, hYX⟩
    exact hYX ▸ Y.2
  refine ⟨level, hsubset, ?_⟩
  intro X hX
  rcases hball hX with ⟨Y, hYV, hYX⟩
  have hY :
      Y = (⟨X, hsubset hX⟩ : skewAdjointPadicCayleySource F p) := by
    apply Subtype.ext
    exact hYX
  rw [← hY, hconst Y hYV,
    skewAdjointPadicCayleySourceDifferentialDensityENNReal_zero]

end Matrix
