import SMSFormula.RationalCliffordSpinCandidateDifferentialCoordinateHaar
import SMSFormula.PadicCayleyTranslatedChartDifferentialZeroNeighborhood
import SMSFormula.PadicUnitCoordinateHaar

/-!
# p-adic Spin masses of small chart images

Near the identity the composite chart `χ = Cay⁻¹ ∘ π` of the p-adic Spin candidate carries the
restricted Spin Haar measure to the inverse-Cayley differential density over the normalized
skew-adjoint coordinate measure, and the density is the constant `‖2‖^d` on a small uniform ball.
Hence every measurable set `N` of coordinates in a fixed neighbourhood of `0` has

`μ_Spin(χ⁻¹(N)) = ‖2‖^d · unitHaar(N)`.

Nothing is chosen: the neighbourhood is existential and the formula involves only data.
-/

noncomputable section

open MeasureTheory Topology PositiveDefiniteIntegralLattice Set
open scoped ENNReal NNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

local instance cayleyChartMassPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _

local instance cayleyChartMassPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

noncomputable local instance cayleyChartMassSkewAdjointMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

noncomputable local instance cayleyChartMassSkewAdjointBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

theorem padicSkewAdjointIdentityChart_target_subset_cayleySource :
    (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target ⊆
      Matrix.skewAdjointPadicCayleySource V.pairingMatrix p := by
  intro y hy
  change y ∈ ((V.padicCliffordSpinCandidateIdentityChart p).trans
    (V.padicSpecialOrthogonalCayleyIdentityChart p)).target at hy
  rw [OpenPartialHomeomorph.trans_target] at hy
  simpa using hy.1

/-- The chart mass formula: in a fixed neighbourhood of the zero coordinate, the Spin mass of the
chart preimage of a measurable coordinate set is `‖2‖^d` times its normalized Haar mass. -/
theorem exists_nhds_padicSpinChart_mass :
    ∃ W₀ ∈ 𝓝 (0 : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix)) → ℚ_[p]),
      ∀ N ⊆ W₀, MeasurableSet N →
        (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p).symm '' N ⊆
            (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target ∧
          V.padicCliffordSpinCandidateChartGluedMeasure p
              ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).symm ''
                ((Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p).symm '' N)) =
            (‖(2 : ℚ_[p])‖₊ ^ Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix) : ℝ≥0∞) *
              Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) N := by
  set χ := V.padicCliffordSpinCandidateSkewAdjointIdentityChart p with hχ
  set ce := Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p with hce
  obtain ⟨level, hsub, hconst⟩ :=
    Matrix.exists_skewAdjointPadicUniformCoordinateBall_subset_cayleySource_const_differentialDensity p n
      V.pairingMatrix
  set B := Matrix.skewAdjointPadicUniformCoordinateBall V.pairingMatrix p level with hB
  have h0t : (0 : (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
      χ.target := by
    rw [← V.padicCliffordSpinCandidateSkewAdjointIdentityChart_one p]
    exact χ.map_source (V.one_mem_padicCliffordSpinCandidateSkewAdjointIdentityChart_source p)
  have hTB : χ.target ∩ B ∈ 𝓝 (0 : (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
    Filter.inter_mem (χ.open_target.mem_nhds h0t)
      ((Matrix.isClopen_skewAdjointPadicUniformCoordinateBall V.pairingMatrix p level).isOpen.mem_nhds
        (Matrix.zero_mem_skewAdjointPadicUniformCoordinateBall V.pairingMatrix p level))
  refine ⟨ce.symm ⁻¹' (χ.target ∩ B), ce.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hTB),
    fun N hN hNm ↦ ?_⟩
  have hTsub : ce.symm '' N ⊆ χ.target ∩ B := by
    rintro _ ⟨w, hw, rfl⟩
    exact hN hw
  refine ⟨fun y hy ↦ (hTsub hy).1, ?_⟩
  set T := ce.symm '' N with hT
  have hTm : MeasurableSet T := by
    rw [hT, ContinuousLinearEquiv.image_symm_eq_preimage]
    exact ce.continuous.measurable hNm
  have hSsrc : χ.symm '' T ⊆ χ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact χ.map_target (hTsub hy).1
  -- restrict to the chart source
  rw [← Measure.restrict_eq_self _ hSsrc,
    V.restrict_padicCliffordSpinCandidateChartGluedMeasure_skewAdjointIdentityChartSource p,
    (MeasurableEmbedding.subtype_coe χ.open_source.measurableSet).map_apply,
    padicCliffordSpinCandidateSkewAdjointIdentityChartSourceMeasure,
    χ.toHomeomorphSourceTarget.symm.measurableEmbedding.map_apply]
  have hpre : (χ.toHomeomorphSourceTarget.symm) ⁻¹' (Subtype.val ⁻¹' (χ.symm '' T)) =
      Subtype.val ⁻¹' T := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    change (∃ x, x ∈ T ∧ χ.symm x = ((χ.toHomeomorphSourceTarget.symm y : χ.source) : _)) ↔ _
    rw [OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rwa [χ.symm.injOn (by simpa using (hTsub hx).1) (by simpa using y.2) hxy] at hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [hpre, padicCliffordSpinCandidateSkewAdjointIdentityChartTargetMeasure,
    withDensity_apply _ (measurableSet_preimage measurable_subtype_coe hTm)]
  have hdens : ∀ y ∈ Subtype.val ⁻¹' T,
      V.padicCliffordSpinCandidateSkewAdjointIdentityChartDensity p y =
        (‖(2 : ℚ_[p])‖₊ ^ Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix) : ℝ≥0∞) := by
    intro y hy
    exact hconst y.1 (hTsub hy).2
  rw [setLIntegral_congr_fun (measurableSet_preimage measurable_subtype_coe hTm) hdens, setLIntegral_const,
    (MeasurableEmbedding.subtype_coe χ.open_target.measurableSet).comap_apply, Subtype.image_preimage_coe,
    Set.inter_eq_right.2 fun y hy ↦ (hTsub hy).1, ← Matrix.map_skewAdjointPadicCoordinateMeasure,
    Measure.map_apply ce.continuous.measurable hNm, ← ContinuousLinearEquiv.image_symm_eq_preimage]

end RationalQuadraticSpaceMatrix
