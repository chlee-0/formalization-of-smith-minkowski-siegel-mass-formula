import SMSFormula.UltrametricLocalChangeOfVariables
import SMSFormula.QuadraticPadicCayleyProductBallDensity

/-! Integrated local change of variables for the actual p-adic Cayley product on
an exact clopen coordinate ball around the base point. The modulus is the
group determinant form on the actual frame columns, and after the full
higher density it is the closed density law. Haar measure on the source
coordinates is supplied; the target Haar is its index-concatenation
transport. Gluing on compact domains and Haar-normalization translation remain. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric
open scoped Matrix.Norms.Operator Topology ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hSs : HasStrictFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

section LocalChange

local instance localChangeMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance localChangeBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance localChangePiIsUltrametricDist (ι : Type*) [Fintype ι] :
    IsUltrametricDist (ι → ℚ_[p]) := by
  refine ⟨fun f g h => ?_⟩
  apply (dist_pi_le_iff (le_trans dist_nonneg (le_max_left _ _))).mpr
  intro i
  exact (IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)).trans
    (max_le_max (dist_le_pi_dist f g i) (dist_le_pi_dist g h i))

/-- The Haar modulus of the coordinate derivative against the
index-concatenation transport of any source Haar measure is the group form
on the actual frame columns. -/
theorem lastCayleyProduct_modulus_eq_groupForm
    (μ : Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    Measure.addHaarScalarFactor ((μ.map (W.lastCayleyProductIndexCoordinates a ha p)).map
      (W.lastCayleyProductCoordinateDerivative a ha p S dS z hSs hSO Y hY X hX hproduct v hs hv).symm)
      μ =
      ‖W.lastOrbitGroupForm a ha ℚ_[p]
        (Sum.elim (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
            Y hY X hX hproduct (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
          (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
            Y hY X hX hproduct (0, v j)))‖₊ := by
  rw [Padic.addHaarScalarFactor_map_symm_eq_nnnorm_det]
  congr 1
  refine (W.lastCayleyProduct_coordinate_det_eq_groupForm a ha p
    (W.lastCayleyProductFrameEquiv a ha p S dS z hSs hSO Y hY X hX hproduct v hs hv)).trans ?_
  congr 1
  funext i
  exact W.lastCayleyProductFrameMap_prodBasis a ha p S dS z hSs.hasFDerivAt hSO Y hY X hX hproduct v i

include hs hv in
/-- Integrated local change of variables for the actual product on every
sufficiently small exact clopen coordinate ball around the base point. -/
theorem lastCayleyProduct_exists_forall_lintegral_image_groupForm
    (μ : Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      IsOpen (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      Set.InjOn (W.lastCayleyProductCoordinateValue a ha p S z v)
        (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ContinuousOn (W.lastCayleyProductCoordinateValue a ha p S z v)
        (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ g : (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
          (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p]) → ℝ≥0∞,
        ∫⁻ y in W.lastCayleyProductCoordinateValue a ha p S z v ''
            closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
            g y ∂(μ.map (W.lastCayleyProductIndexCoordinates a ha p)) =
          (‖W.lastOrbitGroupForm a ha ℚ_[p]
            (Sum.elim (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt
                hSO Y hY X hX hproduct (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j)))‖₊ : ℝ≥0∞) *
            ∫⁻ x in closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              g (W.lastCayleyProductCoordinateValue a ha p S z v x) ∂μ := by
  obtain ⟨δ, hδ, h⟩ :=
    (W.hasStrictFDerivAt_lastCayleyProductCoordinateValue a ha p S dS z hSs hSO Y hY X hX hproduct
      v hs hv).exists_forall_lintegral_image_closedBall μ
        (μ.map (W.lastCayleyProductIndexCoordinates a ha p))
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  obtain ⟨hopen, hinj, hcont, hlaw⟩ := h r hr hrδ
  refine ⟨hopen, hinj, hcont, fun g ↦ ?_⟩
  rw [hlaw g, W.lastCayleyProduct_modulus_eq_groupForm a ha p S dS z hSs hSO Y hY X hX hproduct v hs hv]

include hs hv in
/-- Integrated local change of variables for the actual product: on an exact
clopen coordinate ball `U` around the base point the coordinate product is
injective and, for every function `g`, the lintegral over the image equals the
group form modulus on the actual frame columns times the lintegral of `g`
composed with the product over `U`. -/
theorem lastCayleyProduct_exists_lintegral_image_groupForm
    (μ : Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    ∃ r > 0, IsOpen (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      Set.InjOn (W.lastCayleyProductCoordinateValue a ha p S z v)
        (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ g : (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
          (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p]) → ℝ≥0∞,
        ∫⁻ y in W.lastCayleyProductCoordinateValue a ha p S z v ''
            closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
            g y ∂(μ.map (W.lastCayleyProductIndexCoordinates a ha p)) =
          (‖W.lastOrbitGroupForm a ha ℚ_[p]
            (Sum.elim (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt
                hSO Y hY X hX hproduct (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j)))‖₊ : ℝ≥0∞) *
            ∫⁻ x in closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              g (W.lastCayleyProductCoordinateValue a ha p S z v x) ∂μ := by
  obtain ⟨δ, hδ, h⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_groupForm a ha p S dS z
    hSs hSO Y hY X hX hproduct v hs hv μ
  obtain ⟨h1, h2, -, h4⟩ := h _ (half_pos hδ) (half_lt_self hδ)
  exact ⟨δ / 2, half_pos hδ, h1, h2, h4⟩

include hs hv in
/-- The integrated local change of variables combined with the closed full
density law: after the full higher Cayley source density, the image lintegral is
the rational form ratio, full lower source density and actual horizontal
orbit-relative factor times the pulled-back lintegral. Nothing is normalized. -/
theorem lastCayleyProduct_exists_lintegral_image_density
    (μ : Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    ∃ r > 0, IsOpen (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      Set.InjOn (W.lastCayleyProductCoordinateValue a ha p S z v)
        (closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r) ∧
      ∀ g : (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
          (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p]) → ℝ≥0∞,
        skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1)
            (W.nonisotropicLastExtension a ha).pairingMatrix ⟨X,hX⟩ *
          ∫⁻ y in W.lastCayleyProductCoordinateValue a ha p S z v ''
              closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              g y ∂(μ.map (W.lastCayleyProductIndexCoordinates a ha p)) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ⟨Y,hY⟩ *
            (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
              lastCoordinateVector
              (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
            ∫⁻ x in closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r,
              g (W.lastCayleyProductCoordinateValue a ha p S z v x) ∂μ := by
  obtain ⟨r, hr, hopen, hinj, h⟩ := W.lastCayleyProduct_exists_lintegral_image_groupForm a ha p S dS
    z hSs hSO Y hY X hX hproduct v hs hv μ
  refine ⟨r, hr, hopen, hinj, fun g ↦ ?_⟩
  rw [h g, ← mul_assoc,
    W.lastCayleyProduct_density a ha p S dS z hSs.hasFDerivAt hSO Y hY X hX hproduct v]

end LocalChange

end RationalQuadraticSpaceMatrix
