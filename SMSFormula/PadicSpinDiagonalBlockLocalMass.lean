import SMSFormula.PadicSpinDiagonalBlockLocal
import SMSFormula.BlockCayleyLinearization
import SMSFormula.PadicUnitHaarLinearImage
import SMSFormula.UltrametricApproximatesLinearImage
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import SMSFormula.HaarMeasureEqOfApplyEq

/-!
# The local block measure identity at a finite place

At every prime `p` the block isomorphism `Φ_p : Spin_T(ℚ_p)² ≃ₜ* Spin_U(ℚ_p)` carries `μ_T ⊗ μ_T` to
`‖κ‖_p μ_U` with the explicit rational constant `κ = 8 e_T² / (e_U f₀f₁f₂)`, `e_V` the rational
basis-comparison determinants.

Both sides are Haar, so it suffices to compare them on one set: the Clifford--Cayley image of a
small ball `B × B`.  Its Cayley coordinates are the linear images `L_U(σ_U(B × B)) = L_U(B × B)`
(the rescaling `σ_U` has strict derivative the identity, so it maps small ultrametric balls onto
themselves), and the chart density `‖2‖^d` together with the explicit elementary coordinate
determinants computes both masses.  Nothing is chosen: the ball radius is existential.
-/

noncomputable section

open MeasureTheory Topology PositiveDefiniteIntegralLattice Set Matrix Metric Filter
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

/-! ## Analytic and ultrametric helpers -/

@[fun_prop] private theorem analyticAt_prod_fst {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : E × F} :
    AnalyticAt 𝕜 (fun w : E × F ↦ w.1) x :=
  analyticAt_fst

@[fun_prop] private theorem analyticAt_prod_snd {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : E × F} :
    AnalyticAt 𝕜 (fun w : E × F ↦ w.2) x :=
  analyticAt_snd

@[fun_prop] private theorem analyticAt_pi_apply {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] (i : ι)
    {x : ι → 𝕜} : AnalyticAt 𝕜 (fun u : ι → 𝕜 ↦ u i) x :=
  (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i).analyticAt x

/-- Products of ultrametric spaces are ultrametric for the sup distance. -/
local instance prodIsUltrametricDist {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] : IsUltrametricDist (X × Y) :=
  ⟨fun a b c ↦ by
    simp only [Prod.dist_eq]
    exact max_le
      ((IsUltrametricDist.dist_triangle_max a.1 b.1 c.1).trans (max_le_max (le_max_left _ _) (le_max_left _ _)))
      ((IsUltrametricDist.dist_triangle_max a.2 b.2 c.2).trans (max_le_max (le_max_right _ _) (le_max_right _ _)))⟩

/-- A map with strict derivative the identity at a fixed zero maps every small closed ball onto
itself (ultrametric domain). -/
theorem exists_image_closedBall_eq_of_hasStrictFDerivAt_id {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] [CompleteSpace E] {g : E → E}
    (hg : HasStrictFDerivAt g (ContinuousLinearMap.id 𝕜 E) 0) (hg0 : g 0 = 0) :
    ∃ δ > 0, ∀ ρ < δ, g '' closedBall 0 ρ = closedBall 0 ρ := by
  have hg' : HasStrictFDerivAt g ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E) 0 := by
    simpa using hg
  have hc : ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖₊ * (1 / 2 : ℝ≥0) < 1 := by
    calc _ ≤ 1 * (1 / 2 : ℝ≥0) :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNNNorm_le_bound _ 1 fun x ↦ by simp) zero_le
      _ < 1 := by norm_num
  obtain ⟨s, hs, happ⟩ := hg'.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, hδ, fun ρ hρ ↦ ?_⟩
  have happ' := happ.mono_set ((closedBall_subset_ball hρ).trans hball)
  rw [happ'.image_closedBall_eq hc, hg0]
  simp

/-! ## The Cayley rescalings near the origin -/

section Rescale

variable {f : Fin 3 → ℚ} (p : ℕ) [Fact (Nat.Prime p)]

theorem hasStrictFDerivAt_blockCayleyRescale :
    HasStrictFDerivAt (blockCayleyRescale f ℚ_[p])
      (ContinuousLinearMap.id ℚ_[p] ((Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]))) 0 := by
  have ha : AnalyticAt ℚ_[p] (fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦
      (1 - blockPureNorm f ℚ_[p] w.1 * blockPureNorm f ℚ_[p] w.2)⁻¹ * (1 + blockPureNorm f ℚ_[p] w.2)) 0 := by
    simp only [blockPureNorm, BlockConjugationCoordinates.pureNorm]
    fun_prop (disch := simp)
  have hb : AnalyticAt ℚ_[p] (fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦
      (1 - blockPureNorm f ℚ_[p] w.1 * blockPureNorm f ℚ_[p] w.2)⁻¹ * (1 + blockPureNorm f ℚ_[p] w.1)) 0 := by
    simp only [blockPureNorm, BlockConjugationCoordinates.pureNorm]
    fun_prop (disch := simp)
  have h1 := ha.hasStrictFDerivAt.smul
    (hasStrictFDerivAt_fst (𝕜 := ℚ_[p]) (p := (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]))))
  have h2 := hb.hasStrictFDerivAt.smul
    (hasStrictFDerivAt_snd (𝕜 := ℚ_[p]) (p := (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]))))
  refine (h1.prodMk h2).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [blockPureNorm_zero]

theorem hasStrictFDerivAt_ternaryCayleyRescale :
    HasStrictFDerivAt (ternaryCayleyRescale f ℚ_[p]) (ContinuousLinearMap.id ℚ_[p] (Fin 3 → ℚ_[p])) 0 := by
  have hs : AnalyticAt ℚ_[p] (fun u : Fin 3 → ℚ_[p] ↦
      (1 - blockPureNorm f ℚ_[p] u * blockPureNorm f ℚ_[p] u)⁻¹ * (1 + blockPureNorm f ℚ_[p] u)) 0 := by
    simp only [blockPureNorm, BlockConjugationCoordinates.pureNorm]
    fun_prop (disch := simp)
  refine (hs.hasStrictFDerivAt.smul (hasStrictFDerivAt_id (0 : Fin 3 → ℚ_[p]))).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u ↦ ?_
  simp [blockPureNorm_zero]

/-- The block rescaling maps every small ball onto itself. -/
theorem exists_blockCayleyRescale_image_closedBall :
    ∃ δ > 0, ∀ ρ < δ, blockCayleyRescale f ℚ_[p] '' closedBall 0 ρ = closedBall 0 ρ :=
  exists_image_closedBall_eq_of_hasStrictFDerivAt_id (hasStrictFDerivAt_blockCayleyRescale p)
    (by simp [blockCayleyRescale])

/-- The ternary rescaling maps every small ball onto itself. -/
theorem exists_ternaryCayleyRescale_image_closedBall :
    ∃ δ > 0, ∀ ρ < δ, ternaryCayleyRescale f ℚ_[p] '' closedBall 0 ρ = closedBall 0 ρ :=
  exists_image_closedBall_eq_of_hasStrictFDerivAt_id (hasStrictFDerivAt_ternaryCayleyRescale p)
    (by simp [ternaryCayleyRescale])

end Rescale

/-! ## Chart values of the Cayley points near the origin -/

section ChartValues

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

theorem eventually_one_sub_blockPureNorm_mul_ne :
    ∀ᶠ w in 𝓝 (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])),
      1 - blockPureNorm f ℚ_[p] w.1 * blockPureNorm f ℚ_[p] w.2 ≠ 0 := by
  have hN := continuous_blockPureNorm (f := f) ℚ_[p]
  have h : ContinuousAt (fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦
      1 - blockPureNorm f ℚ_[p] w.1 * blockPureNorm f ℚ_[p] w.2) 0 :=
    (continuous_const.sub ((hN.comp continuous_fst).mul (hN.comp continuous_snd))).continuousAt
  exact h.eventually_ne (by simp [blockPureNorm_zero])

/-- The ternary chart value: near the origin `κ(u)` lies in the chart source with chart value
`X_T(u)`. -/
theorem eventually_ternaryCayleyPoint_chart :
    ∀ᶠ u in 𝓝 (0 : Fin 3 → ℚ_[p]),
      T.ternaryCayleyPoint hT hδ ℚ_[p] u ∈ (T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source ∧
        ((T.padicCliffordSpinCandidateSkewAdjointIdentityChart p (T.ternaryCayleyPoint hT hδ ℚ_[p] u) :
          (skewAdjointMatricesLieSubalgebra (T.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
            Matrix (Fin 3) (Fin 3) ℚ_[p]) = ternaryCayleyX f ℚ_[p] u := by
  have hsrc : ∀ᶠ u in 𝓝 (0 : Fin 3 → ℚ_[p]),
      T.ternaryCayleyPoint hT hδ ℚ_[p] u ∈ (T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).source := by
    have h1 := T.continuousAt_ternaryCayleyPoint hT hδ ℚ_[p]
    rw [ContinuousAt, T.ternaryCayleyPoint_zero hT hδ ℚ_[p]] at h1
    exact h1 ((T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).open_source.mem_nhds
      (T.one_mem_padicCliffordSpinCandidateSkewAdjointIdentityChart_source p))
  have huu : ∀ᶠ u in 𝓝 (0 : Fin 3 → ℚ_[p]), 1 - blockPureNorm f ℚ_[p] u * blockPureNorm f ℚ_[p] u ≠ 0 := by
    have hN := continuous_blockPureNorm (f := f) ℚ_[p]
    exact (continuous_const.sub (hN.mul hN)).continuousAt.eventually_ne (by simp [blockPureNorm_zero])
  filter_upwards [hsrc, eventually_blockPureNorm_ne (f := f) ℚ_[p], huu] with u hs hu huu
  refine ⟨hs, T.padicSkewAdjointIdentityChart_coe_eq_of_mul p hs ?_⟩
  rw [T.ternaryCayleyPoint_matrix hT hδ ℚ_[p] hu]
  exact T.ternaryConjMatrix_cayley_mul hT hδ ℚ_[p] hu huu

/-- The block chart value: near the origin `Φ(κ(u), κ(v))` lies in the chart source with chart value
`X_U(u, v)`. -/
theorem eventually_blockCayleyPoint_chart :
    ∀ᶠ w in 𝓝 (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])),
      T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2 ∈
          ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).padicCliffordSpinCandidateSkewAdjointIdentityChart
            p).source ∧
        (((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).padicCliffordSpinCandidateSkewAdjointIdentityChart p
            (T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) :
          (skewAdjointMatricesLieSubalgebra ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).pairingMatrix.map
            (algebraMap ℚ ℚ_[p]))).toSubmodule) : Matrix (Fin 4) (Fin 4) ℚ_[p]) =
          blockCayleyX f ℚ_[p] w.1 w.2 := by
  have hsrc : ∀ᶠ w in 𝓝 (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])),
      T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2 ∈ ((UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p).source := by
    have h1 := T.continuousAt_blockCayleyPoint hT hδ ℚ_[p]
    rw [ContinuousAt] at h1
    have h0 : T.blockCayleyPoint hT hδ ℚ_[p] (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])).1
        (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])).2 = 1 :=
      T.blockCayleyPoint_zero hT hδ ℚ_[p]
    rw [h0] at h1
    exact h1 (((UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p).open_source.mem_nhds
      ((UU).one_mem_padicCliffordSpinCandidateSkewAdjointIdentityChart_source p))
  have hu : ∀ᶠ w in 𝓝 (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])), 1 + blockPureNorm f ℚ_[p] w.1 ≠ 0 :=
    (continuous_fst.tendsto (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]))).eventually
      (eventually_blockPureNorm_ne (f := f) ℚ_[p])
  have hv : ∀ᶠ w in 𝓝 (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])), 1 + blockPureNorm f ℚ_[p] w.2 ≠ 0 :=
    (continuous_snd.tendsto (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]))).eventually
      (eventually_blockPureNorm_ne (f := f) ℚ_[p])
  filter_upwards [hsrc, hu, hv, eventually_one_sub_blockPureNorm_mul_ne (f := f) p] with w hs hu hv huv
  refine ⟨hs, (UU).padicSkewAdjointIdentityChart_coe_eq_of_mul p hs ?_⟩
  rw [T.blockCayleyPoint_matrix hT hδ ℚ_[p] hu hv]
  exact diagonalBlockConjMatrix_cayley_mul hδ ℚ_[p] hu hv huv

end ChartValues

/-! ## Chart masses in elementary coordinates -/

section ChartMass

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

local instance localMassPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance localMassPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

noncomputable local instance localMassSkewMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

noncomputable local instance localMassSkewBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

omit [Fact (Nat.Prime p)] in
theorem finrank_skewAdjoint_eq_choose :
    Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix) = n.choose 2 :=
  (card_strictUpperPair_eq_finrank_skewAdjoint V.pairingMatrix V.form_symm V.form_det_ne_zero).symm.trans
    (StrictUpperPair.card n)

/-- The chart mass in elementary coordinates: near the zero skew-adjoint matrix, the Spin mass of the
chart preimage of a compact set is `‖2‖^d ‖e_V‖` times the unit-cube Haar mass of its form-adapted
elementary coordinates. -/
theorem exists_nhds_padicSpinChart_mass_elementary :
    ∃ W ∈ 𝓝 (0 : (skewAdjointMatricesLieSubalgebra (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
      ∀ S ⊆ W, IsCompact S →
        S ⊆ (V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).target ∧
        V.padicCliffordSpinCandidateChartGluedMeasure p
            ((V.padicCliffordSpinCandidateSkewAdjointIdentityChart p).symm '' S) =
          (‖(2 : ℚ_[p])‖₊ ^ Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix) : ℝ≥0∞) *
            ((‖algebraMap ℚ ℚ_[p]
                (skewAdjointFixedFormElementaryDetScalar V.pairingMatrix V.form_symm V.form_det_ne_zero)‖₊ : ℝ≥0∞) *
              Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
                (skewAdjointFormElementaryPadicCoordinateEquiv p V.pairingMatrix V.form_symm V.form_det_ne_zero '' S)) := by
  obtain ⟨W₀, hW₀, hmass⟩ := V.exists_nhds_padicSpinChart_mass p
  have hce := (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p).continuous
  refine ⟨Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p ⁻¹' W₀,
    hce.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hW₀), fun S hS hSc ↦ ?_⟩
  have hN : Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p '' S ⊆ W₀ := image_subset_iff.2 hS
  have hNm : MeasurableSet (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p '' S) :=
    (hSc.image hce).measurableSet
  obtain ⟨hsub, hμ⟩ := hmass _ hN hNm
  have hS' : (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p).symm ''
      (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p '' S) = S := by
    rw [image_image]
    simp
  rw [hS'] at hsub hμ
  refine ⟨hsub, ?_⟩
  rw [hμ]
  congr 1
  have h : (Matrix.skewAdjointPadicCoordinateMeasure V.pairingMatrix p).map
        (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p)
        (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p '' S) =
      Matrix.skewAdjointPadicCoordinateMeasure V.pairingMatrix p
        (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p ⁻¹'
          (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p '' S)) :=
    (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p).toHomeomorph.toMeasurableEquiv.map_apply _
  have h2 : Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p '' S) =
      Matrix.skewAdjointPadicCoordinateMeasure V.pairingMatrix p S := by
    rw [← Matrix.map_skewAdjointPadicCoordinateMeasure V.pairingMatrix p, h,
      preimage_image_eq _ (Matrix.skewAdjointPadicCoordinateEquiv V.pairingMatrix p).injective]
  rw [h2, Matrix.skewAdjointPadicCoordinateMeasure_eq_elementary p V.pairingMatrix V.form_symm V.form_det_ne_zero S]

end ChartMass

/-! ## Masses of the Cayley images of small balls -/

section CayleyMass

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

local instance cayleyMassPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance cayleyMassPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The skew-adjoint ternary linear part `L_T`. -/
def ternaryCayleyLinearSkew : (Fin 3 → ℚ_[p]) →ₗ[ℚ_[p]]
    (skewAdjointMatricesLieSubalgebra (T.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  LinearMap.codRestrict _ (ternaryCayleyLinearMap f ℚ_[p]) fun u ↦ by
    rw [LieSubalgebra.mem_toSubmodule, hT]
    exact ternaryCayleyLinearMap_mem ℚ_[p] u

/-- The skew-adjoint block linear part `L_U`. -/
def blockCayleyLinearSkew : ((Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])) →ₗ[ℚ_[p]]
    (skewAdjointMatricesLieSubalgebra ((UU).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  LinearMap.codRestrict _ (blockCayleyLinearMap f ℚ_[p]) fun w ↦ by
    rw [LieSubalgebra.mem_toSubmodule, T.nonisotropicLastExtension_pairingMatrix_eq_diagonal hT hδ]
    exact blockCayleyLinearMap_mem ℚ_[p] w

theorem ternaryCayleyLinearSkew_elementary (u : Fin 3 → ℚ_[p]) :
    skewAdjointFormElementaryPadicCoordinateEquiv p T.pairingMatrix T.form_symm T.form_det_ne_zero
        (T.ternaryCayleyLinearSkew hT p u) =
      (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p]
        ((skewAdjointFormElementaryIndexEquiv T.pairingMatrix T.form_symm T.form_det_ne_zero).symm.trans
          ternaryPairEquiv.symm)).toContinuousLinearEquiv
        (Matrix.toLin' (ternaryElementaryMatrix f ℚ_[p]) u) := by
  funext j
  rw [skewAdjointFormElementaryPadicCoordinateEquiv_apply]
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Equiv.trans_apply]
  rw [← ternaryElementary_coordinates ℚ_[p] u, Equiv.apply_symm_apply, ← hT]
  rfl

theorem blockCayleyLinearSkew_elementary (w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])) :
    skewAdjointFormElementaryPadicCoordinateEquiv p (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero
        (T.blockCayleyLinearSkew hT hδ p w) =
      (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p]
        ((skewAdjointFormElementaryIndexEquiv (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero).symm.trans
          blockPairEquiv.symm)).toContinuousLinearEquiv
        (Matrix.toLin' (blockElementaryMatrix f ℚ_[p]) (Sum.elim w.1 w.2)) := by
  funext j
  rw [skewAdjointFormElementaryPadicCoordinateEquiv_apply]
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Equiv.trans_apply]
  rw [← blockElementary_coordinates ℚ_[p] w, Equiv.apply_symm_apply,
    ← T.nonisotropicLastExtension_pairingMatrix_eq_diagonal hT hδ]
  rfl

/-- The ternary Cayley mass: the Spin mass of `κ(B)` for a small ball `B`. -/
theorem exists_ternaryCayley_mass :
    ∃ ρ₀ > 0, ∀ ρ, ρ < ρ₀ →
      MeasurableSet (T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 ρ) ∧
      T.padicCliffordSpinCandidateChartGluedMeasure p (T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 ρ) =
        (‖(2 : ℚ_[p])‖₊ ^ 3 : ℝ≥0∞) *
          ((‖algebraMap ℚ ℚ_[p]
              (skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm T.form_det_ne_zero)‖₊ : ℝ≥0∞) *
            ((‖algebraMap ℚ ℚ_[p] (8 * (f 0 * f 1 * f 2) ^ 2)‖₊ : ℝ≥0∞) *
              Padic.unitHaar p (Fin 3) (closedBall 0 ρ))) := by
  obtain ⟨W, hW, hmass⟩ := T.exists_nhds_padicSpinChart_mass_elementary p
  obtain ⟨δσ, hδσ, hσ⟩ := exists_ternaryCayleyRescale_image_closedBall (f := f) p
  obtain ⟨ε, hε, hch⟩ := Metric.eventually_nhds_iff_ball.1 (T.eventually_ternaryCayleyPoint_chart hT hδ p)
  have hL : Continuous (T.ternaryCayleyLinearSkew hT p) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ε', hε', hball'⟩ :=
    Metric.mem_nhds_iff.1 (hL.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hW))
  refine ⟨min (min δσ ε) ε', lt_min (lt_min hδσ hε) hε', fun ρ hρ ↦ ?_⟩
  have hBε : closedBall (0 : Fin 3 → ℚ_[p]) ρ ⊆ ball 0 ε :=
    closedBall_subset_ball (hρ.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hBε' : closedBall (0 : Fin 3 → ℚ_[p]) ρ ⊆ ball 0 ε' :=
    closedBall_subset_ball (hρ.trans_le (min_le_right _ _))
  have hρσ : ρ < δσ := hρ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hSc : IsCompact (T.ternaryCayleyLinearSkew hT p '' closedBall 0 ρ) := (isCompact_closedBall 0 ρ).image hL
  have hSW : T.ternaryCayleyLinearSkew hT p '' closedBall 0 ρ ⊆ W := image_subset_iff.2 (hBε'.trans hball')
  obtain ⟨hStarget, hμ⟩ := hmass _ hSW hSc
  have himg : T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 ρ =
      (T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).symm ''
        (T.ternaryCayleyLinearSkew hT p '' closedBall 0 ρ) := by
    have hpt : ∀ u ∈ closedBall (0 : Fin 3 → ℚ_[p]) ρ, T.ternaryCayleyPoint hT hδ ℚ_[p] u =
        (T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).symm
          (T.ternaryCayleyLinearSkew hT p (ternaryCayleyRescale f ℚ_[p] u)) := by
      intro u hu
      obtain ⟨hs, hv⟩ := hch u (hBε hu)
      have hχ : T.padicCliffordSpinCandidateSkewAdjointIdentityChart p (T.ternaryCayleyPoint hT hδ ℚ_[p] u) =
          T.ternaryCayleyLinearSkew hT p (ternaryCayleyRescale f ℚ_[p] u) :=
        Subtype.ext (hv.trans (ternaryCayleyX_eq_linearMap hδ ℚ_[p] u))
      rw [← hχ, (T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).left_inv hs]
    rw [image_congr hpt]
    conv_rhs => rw [← hσ ρ hρσ, image_image, image_image]
  refine ⟨himg ▸ (hSc.image_of_continuousOn
    ((T.padicCliffordSpinCandidateSkewAdjointIdentityChart p).continuousOn_symm.mono hStarget)).measurableSet, ?_⟩
  have hset : skewAdjointFormElementaryPadicCoordinateEquiv p T.pairingMatrix T.form_symm T.form_det_ne_zero ''
        (T.ternaryCayleyLinearSkew hT p '' closedBall 0 ρ) =
      (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p]
        ((skewAdjointFormElementaryIndexEquiv T.pairingMatrix T.form_symm T.form_det_ne_zero).symm.trans
          ternaryPairEquiv.symm)).toContinuousLinearEquiv ''
        (Matrix.toLin' (ternaryElementaryMatrix f ℚ_[p]) '' closedBall 0 ρ) := by
    rw [image_image, image_image]
    exact image_congr fun u _ ↦ T.ternaryCayleyLinearSkew_elementary hT p u
  have hdet : (ternaryElementaryMatrix f ℚ_[p]).det ≠ 0 := by
    rw [det_ternaryElementaryMatrix]
    exact (map_ne_zero _).2 (mul_ne_zero (by norm_num) (pow_ne_zero _ hδ))
  rw [himg, hμ, hset, Padic.unitHaar_image_funCongrLeft,
    Padic.unitHaar_image_toLin' _ hdet isClosed_closedBall.measurableSet, det_ternaryElementaryMatrix,
    T.finrank_skewAdjoint_eq_choose]
  rfl

/-- The block Cayley mass: the Spin mass of `Φ(κ(B), κ(B))` for a small ball `B`. -/
theorem exists_blockCayley_mass :
    ∃ ρ₀ > 0, ∀ ρ, ρ < ρ₀ →
      MeasurableSet ((fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦ T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) ''
        closedBall 0 ρ) ∧
      (UU).padicCliffordSpinCandidateChartGluedMeasure p
          ((fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦ T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) ''
            closedBall 0 ρ) =
        (‖(2 : ℚ_[p])‖₊ ^ 6 : ℝ≥0∞) *
          ((‖algebraMap ℚ ℚ_[p]
              (skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero)‖₊ :
              ℝ≥0∞) *
            ((‖algebraMap ℚ ℚ_[p] (-(8 * (f 0 * f 1 * f 2) ^ 5))‖₊ : ℝ≥0∞) *
              (Padic.unitHaar p (Fin 3) (closedBall 0 ρ) * Padic.unitHaar p (Fin 3) (closedBall 0 ρ)))) := by
  obtain ⟨W, hW, hmass⟩ := (UU).exists_nhds_padicSpinChart_mass_elementary p
  obtain ⟨δσ, hδσ, hσ⟩ := exists_blockCayleyRescale_image_closedBall (f := f) p
  obtain ⟨ε, hε, hch⟩ := Metric.eventually_nhds_iff_ball.1 (T.eventually_blockCayleyPoint_chart hT hδ p)
  have hL : Continuous (T.blockCayleyLinearSkew hT hδ p) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ε', hε', hball'⟩ :=
    Metric.mem_nhds_iff.1 (hL.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hW))
  refine ⟨min (min δσ ε) ε', lt_min (lt_min hδσ hε) hε', fun ρ hρ ↦ ?_⟩
  have hBε : closedBall (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])) ρ ⊆ ball 0 ε :=
    closedBall_subset_ball (hρ.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hBε' : closedBall (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])) ρ ⊆ ball 0 ε' :=
    closedBall_subset_ball (hρ.trans_le (min_le_right _ _))
  have hρσ : ρ < δσ := hρ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hSc : IsCompact (T.blockCayleyLinearSkew hT hδ p '' closedBall 0 ρ) := (isCompact_closedBall 0 ρ).image hL
  have hSW : T.blockCayleyLinearSkew hT hδ p '' closedBall 0 ρ ⊆ W := image_subset_iff.2 (hBε'.trans hball')
  obtain ⟨hStarget, hμ⟩ := hmass _ hSW hSc
  have himg : (fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦ T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) ''
        closedBall 0 ρ =
      ((UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p).symm ''
        (T.blockCayleyLinearSkew hT hδ p '' closedBall 0 ρ) := by
    have hpt : ∀ w ∈ closedBall (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])) ρ, T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2 =
        ((UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p).symm
          (T.blockCayleyLinearSkew hT hδ p (blockCayleyRescale f ℚ_[p] w)) := by
      intro w hw
      obtain ⟨hs, hv⟩ := hch w (hBε hw)
      have hχ : (UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p (T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) =
          T.blockCayleyLinearSkew hT hδ p (blockCayleyRescale f ℚ_[p] w) :=
        Subtype.ext (hv.trans (blockCayleyX_eq_linearMap hδ ℚ_[p] w))
      rw [← hχ, ((UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p).left_inv hs]
    rw [image_congr hpt]
    conv_rhs => rw [← hσ ρ hρσ, image_image, image_image]
  refine ⟨himg ▸ (hSc.image_of_continuousOn
    (((UU).padicCliffordSpinCandidateSkewAdjointIdentityChart p).continuousOn_symm.mono hStarget)).measurableSet, ?_⟩
  set sumElim : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) → (Fin 3 ⊕ Fin 3 → ℚ_[p]) := fun x ↦ Sum.elim x.1 x.2
    with hsumElim
  have hset : skewAdjointFormElementaryPadicCoordinateEquiv p (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero ''
        (T.blockCayleyLinearSkew hT hδ p '' closedBall 0 ρ) =
      (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p]
        ((skewAdjointFormElementaryIndexEquiv (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero).symm.trans
          blockPairEquiv.symm)).toContinuousLinearEquiv ''
        (Matrix.toLin' (blockElementaryMatrix f ℚ_[p]) '' (sumElim '' closedBall 0 ρ)) := by
    rw [image_image, image_image, image_image]
    exact image_congr fun w _ ↦ T.blockCayleyLinearSkew_elementary hT hδ p w
  have hdet : (blockElementaryMatrix f ℚ_[p]).det ≠ 0 := by
    rw [det_blockElementaryMatrix]
    exact (map_ne_zero _).2 (neg_ne_zero.2 (mul_ne_zero (by norm_num) (pow_ne_zero _ hδ)))
  have hsumc : Continuous sumElim := continuous_pi fun k ↦ by
    rcases k with k | k
    · exact (continuous_apply k).comp continuous_fst
    · exact (continuous_apply k).comp continuous_snd
  have hsuminj : Function.Injective sumElim := fun x y h ↦
    Prod.ext (funext fun i ↦ congrFun h (Sum.inl i)) (funext fun i ↦ congrFun h (Sum.inr i))
  have hYc : IsCompact (sumElim '' closedBall 0 ρ) := (isCompact_closedBall 0 ρ).image hsumc
  have hY : Padic.unitHaar p (Fin 3 ⊕ Fin 3) (sumElim '' closedBall 0 ρ) =
      Padic.unitHaar p (Fin 3) (closedBall 0 ρ) * Padic.unitHaar p (Fin 3) (closedBall 0 ρ) := by
    rw [← Padic.map_sumElim_prod_unitHaar p (Fin 3) (Fin 3), Measure.map_apply hsumc.measurable hYc.measurableSet,
      preimage_image_eq _ hsuminj, ← Prod.mk_zero_zero, ← closedBall_prod_same, Measure.prod_prod]
  rw [himg, hμ, hset, Padic.unitHaar_image_funCongrLeft,
    Padic.unitHaar_image_toLin' _ hdet hYc.measurableSet, det_blockElementaryMatrix, hY,
    (UU).finrank_skewAdjoint_eq_choose]
  rfl

end CayleyMass

/-! ## The local identity -/

section LocalIdentity

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

/-- The local block constant `κ = 8 e_T² / (e_U f₀f₁f₂)`, `e_V` the rational basis-comparison
determinants. -/
def diagonalBlockLocalConstant : ℚ :=
  8 * skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm T.form_det_ne_zero ^ 2 /
    (skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero *
      (f 0 * f 1 * f 2))

theorem diagonalBlockLocalConstant_ne_zero : T.diagonalBlockLocalConstant hδ ≠ 0 := by
  unfold diagonalBlockLocalConstant
  exact div_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _)))
    (mul_ne_zero (skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _) hδ)

theorem diagonalBlockLocalConstant_mul :
    T.diagonalBlockLocalConstant hδ *
        skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero *
          (-(8 * (f 0 * f 1 * f 2) ^ 5)) =
      -((skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm T.form_det_ne_zero) ^ 2 *
        (8 * (f 0 * f 1 * f 2) ^ 2) ^ 2) := by
  have he := skewAdjointFixedFormElementaryDetScalar_ne_zero (UU).pairingMatrix (UU).form_symm (UU).form_det_ne_zero
  unfold diagonalBlockLocalConstant
  field_simp

set_option synthInstance.maxHeartbeats 400000 in
/-- The local block measure identity at a prime `p`:
`Φ_p(μ_T ⊗ μ_T) = ‖κ‖_p μ_U`. -/
theorem map_diagonalBlock_padicChartGluedMeasure :
    Measure.map (T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p])
        ((T.padicCliffordSpinCandidateChartGluedMeasure p).prod (T.padicCliffordSpinCandidateChartGluedMeasure p)) =
      (‖algebraMap ℚ ℚ_[p] (T.diagonalBlockLocalConstant hδ)‖₊ : ℝ≥0∞) •
        (UU).padicCliffordSpinCandidateChartGluedMeasure p := by
  obtain ⟨ρT, hρT, hTm⟩ := T.exists_ternaryCayley_mass hT hδ p
  obtain ⟨ρU, hρU, hUm⟩ := T.exists_blockCayley_mass hT hδ p
  have hρ0 : 0 < min ρT ρU / 2 := by positivity
  have hρT' : min ρT ρU / 2 < ρT := (half_lt_self (lt_min hρT hρU)).trans_le (min_le_left _ _)
  have hρU' : min ρT ρU / 2 < ρU := (half_lt_self (lt_min hρT hρU)).trans_le (min_le_right _ _)
  obtain ⟨hKm, hK⟩ := hTm _ hρT'
  obtain ⟨hEm, hE⟩ := hUm _ hρU'
  -- the evaluation set is the block image of a product
  have hEK : (fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦ T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) ''
        closedBall 0 (min ρT ρU / 2) =
      T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p] ''
        ((T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 (min ρT ρU / 2)) ×ˢ
          (T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 (min ρT ρU / 2))) := by
    rw [show closedBall (0 : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p])) (min ρT ρU / 2) =
        closedBall 0 (min ρT ρU / 2) ×ˢ closedBall 0 (min ρT ρU / 2) from
      (closedBall_prod_same (0 : Fin 3 → ℚ_[p]) (0 : Fin 3 → ℚ_[p]) _).symm, prod_image_image_eq, image_image]
    rfl
  have hpre : T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p] ⁻¹'
        ((fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦ T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) ''
          closedBall 0 (min ρT ρU / 2)) =
      (T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 (min ρT ρU / 2)) ×ˢ
        (T.ternaryCayleyPoint hT hδ ℚ_[p] '' closedBall 0 (min ρT ρU / 2)) := by
    rw [hEK, preimage_image_eq _ (T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p]).injective]
  -- Haar structure
  haveI := T.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  haveI := (UU).padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  haveI hprod : ((T.padicCliffordSpinCandidateChartGluedMeasure p).prod
      (T.padicCliffordSpinCandidateChartGluedMeasure p)).IsHaarMeasure := inferInstance
  haveI : (Measure.map (T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p])
      ((T.padicCliffordSpinCandidateChartGluedMeasure p).prod
        (T.padicCliffordSpinCandidateChartGluedMeasure p))).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ (T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p])
  have hκ0 : (‖algebraMap ℚ ℚ_[p] (T.diagonalBlockLocalConstant hδ)‖₊ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero, nnnorm_ne_zero_iff, map_ne_zero]
    exact T.diagonalBlockLocalConstant_ne_zero hδ
  haveI : ((‖algebraMap ℚ ℚ_[p] (T.diagonalBlockLocalConstant hδ)‖₊ : ℝ≥0∞) •
      (UU).padicCliffordSpinCandidateChartGluedMeasure p).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ hκ0 ENNReal.coe_ne_top
  -- the ball mass
  letI : MeasurableSpace ℚ_[p] := borel _
  haveI : BorelSpace ℚ_[p] := ⟨rfl⟩
  have hm0 : Padic.unitHaar p (Fin 3) (closedBall 0 (min ρT ρU / 2)) ≠ 0 :=
    ((IsUltrametricDist.isOpen_closedBall (0 : Fin 3 → ℚ_[p]) hρ0.ne').measure_ne_zero _
      ⟨0, mem_closedBall_self hρ0.le⟩)
  have hmt : Padic.unitHaar p (Fin 3) (closedBall 0 (min ρT ρU / 2)) ≠ ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  have h2 : (‖(2 : ℚ_[p])‖₊ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero, nnnorm_ne_zero_iff]
    exact two_ne_zero
  have heU : (‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm
      (UU).form_det_ne_zero)‖₊ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero, nnnorm_ne_zero_iff, map_ne_zero]
    exact skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _
  have hd : (‖algebraMap ℚ ℚ_[p] (-(8 * (f 0 * f 1 * f 2) ^ 5))‖₊ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero, nnnorm_ne_zero_iff, map_ne_zero]
    exact neg_ne_zero.2 (mul_ne_zero (by norm_num) (pow_ne_zero _ hδ))
  refine Measure.eq_of_isHaarMeasure_of_apply_eq _ _
    (E := (fun w : (Fin 3 → ℚ_[p]) × (Fin 3 → ℚ_[p]) ↦ T.blockCayleyPoint hT hδ ℚ_[p] w.1 w.2) ''
      closedBall 0 (min ρT ρU / 2)) ?_ ?_ ?_
  · rw [Measure.smul_apply, hE, smul_eq_mul]
    exact mul_ne_zero hκ0 (mul_ne_zero (pow_ne_zero _ h2) (mul_ne_zero heU (mul_ne_zero hd (mul_ne_zero hm0 hm0))))
  · rw [Measure.smul_apply, hE, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hmt hmt))))
  · rw [Measure.map_apply (map_continuous (T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[p])).measurable hEm, hpre,
      Measure.prod_prod, hK, Measure.smul_apply, hE, smul_eq_mul]
    have key : ‖algebraMap ℚ ℚ_[p] (T.diagonalBlockLocalConstant hδ)‖₊ *
          ‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm
            (UU).form_det_ne_zero)‖₊ * ‖algebraMap ℚ ℚ_[p] (-(8 * (f 0 * f 1 * f 2) ^ 5))‖₊ =
        ‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm
            T.form_det_ne_zero)‖₊ ^ 2 * ‖algebraMap ℚ ℚ_[p] (8 * (f 0 * f 1 * f 2) ^ 2)‖₊ ^ 2 := by
      rw [← nnnorm_mul, ← nnnorm_mul, ← map_mul, ← map_mul, T.diagonalBlockLocalConstant_mul hδ, map_neg,
        nnnorm_neg, map_mul, nnnorm_mul, map_pow, map_pow, nnnorm_pow, nnnorm_pow]
    have key' : (‖algebraMap ℚ ℚ_[p] (T.diagonalBlockLocalConstant hδ)‖₊ : ℝ≥0∞) *
          ‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm
            (UU).form_det_ne_zero)‖₊ * ‖algebraMap ℚ ℚ_[p] (-(8 * (f 0 * f 1 * f 2) ^ 5))‖₊ =
        (‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm
            T.form_det_ne_zero)‖₊ : ℝ≥0∞) ^ 2 * (‖algebraMap ℚ ℚ_[p] (8 * (f 0 * f 1 * f 2) ^ 2)‖₊ : ℝ≥0∞) ^ 2 := by
      rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, key, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_pow]
    calc _ = ((‖algebraMap ℚ ℚ_[p] (skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm
            T.form_det_ne_zero)‖₊ : ℝ≥0∞) ^ 2 * (‖algebraMap ℚ ℚ_[p] (8 * (f 0 * f 1 * f 2) ^ 2)‖₊ : ℝ≥0∞) ^ 2) *
          ((‖(2 : ℚ_[p])‖₊ : ℝ≥0∞) ^ 6 * (Padic.unitHaar p (Fin 3) (closedBall 0 (min ρT ρU / 2)) *
            Padic.unitHaar p (Fin 3) (closedBall 0 (min ρT ρU / 2)))) := by ring
      _ = _ := by rw [← key']; ring

end LocalIdentity

end RationalQuadraticSpaceMatrix
