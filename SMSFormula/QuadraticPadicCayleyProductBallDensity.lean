import SMSFormula.QuadraticPadicCayleyProductBallChange
import SMSFormula.PadicCoordinateVectorHaar

/-! The ball-law Haar modulus of the actual product is |det|_p of the coordinate
derivative, and that determinant is the group determinant form on the
actual frame columns, i.e. the quantity in the closed full density law. The
source and target coordinate Haar measures are matched only through the
index concatenation; no Haar normalization, chart or baseline is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric
open scoped Matrix.Norms.Operator Topology ENNReal NNReal

namespace Padic
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance ballDensityMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ballDensityBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- For a coordinate identification `R` and linear equivalence `A`, the Haar
modulus of `A` against the transported source Haar is |det(R⁻¹ ∘ A)|_p. -/
theorem addHaarScalarFactor_map_symm_eq_nnnorm_det
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure (ι → ℚ_[p])) [μ.IsAddHaarMeasure]
    (R A : (ι → ℚ_[p]) ≃L[ℚ_[p]] (κ → ℚ_[p])) :
    Measure.addHaarScalarFactor ((μ.map R).map A.symm) μ =
      ‖LinearMap.det ((A.trans R.symm : (ι → ℚ_[p]) ≃L[ℚ_[p]] (ι → ℚ_[p])) :
        (ι → ℚ_[p]) →ₗ[ℚ_[p]] (ι → ℚ_[p]))‖₊ := by
  let L : (ι → ℚ_[p]) ≃L[ℚ_[p]] (ι → ℚ_[p]) := R.trans A.symm
  have hmm : (μ.map R).map A.symm = μ.map L :=
    Measure.map_map A.symm.continuous.measurable R.continuous.measurable
  have hdetL : (LinearMap.toMatrix' (L : (ι → ℚ_[p]) →ₗ[ℚ_[p]] (ι → ℚ_[p]))).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hmap := Padic.map_vectorHaar_matrix p Measure.addHaar μ
    (LinearMap.toMatrix' (L : (ι → ℚ_[p]) →ₗ[ℚ_[p]] (ι → ℚ_[p]))) hdetL
  rw [Matrix.toLin'_toMatrix', LinearMap.det_toMatrix'] at hmap
  have hL : (L : (ι → ℚ_[p]) → (ι → ℚ_[p])) =
      ((L : (ι → ℚ_[p]) →ₗ[ℚ_[p]] (ι → ℚ_[p])) : (ι → ℚ_[p]) → (ι → ℚ_[p])) := rfl
  have hfac : Measure.addHaarScalarFactor ((μ.map R).map A.symm) μ =
      ‖LinearMap.det (L : (ι → ℚ_[p]) →ₗ[ℚ_[p]] (ι → ℚ_[p]))‖₊⁻¹ := by
    simp only [hmm, hL, hmap, Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self,
      smul_eq_mul, mul_one]
  rw [hfac]
  have hinv : L = (A.trans R.symm).symm := by ext; rfl
  rw [hinv]
  change ‖LinearMap.det ((A.trans R.symm).toLinearEquiv.symm : (ι → ℚ_[p]) →ₗ[ℚ_[p]] _)‖₊⁻¹ = _
  rw [LinearEquiv.det_coe_symm, nnnorm_inv, inv_inv]

end Padic

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]

/-- The index concatenation, read as an identification of the source and
target coordinate spaces. It is a permutation of coordinates, not a Haar choice. -/
def lastCayleyProductIndexCoordinates :
    (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p])
      ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra
        (W.nonisotropicLastExtension a ha).pairingMatrix)) → ℚ_[p]) :=
  (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p] (W.lastOrbitIndexEquiv a ha)).toContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hS : HasFDerivAt S dS z)
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

set_option backward.isDefEq.respectTransparency false in
/-- The frame map on the product basis is exactly the actual frame columns. -/
theorem lastCayleyProductFrameMap_prodBasis
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n) :
    W.lastCayleyProductFrameMap a ha p S dS z hS hSO Y hY X hX hproduct v
      (((skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix).prod
        (Pi.basisFun ℚ_[p] (Fin n))) i) =
      Sum.elim
        (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
          (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
        (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
          (0, v j)) i := by
  classical
  rw [W.lastCayleyProductFrameMap_apply]
  cases i with
  | inl i =>
    rw [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd]
    simp
  | inr j =>
    rw [Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd]
    simp [Pi.basisFun_apply, Pi.single_apply] <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of a linear map read in source/target coordinates,
matched by the index concatenation, is the group determinant form on the
images of the source basis. -/
theorem lastCayleyProduct_coordinate_det_eq_groupForm
    (T : (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) ≃L[ℚ_[p]]
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    LinearMap.det (((W.lastCayleyProductSourceCoordinates p).symm.trans
        (T.trans (W.lastCayleyProductTargetCoordinates a ha p))).trans
        (W.lastCayleyProductIndexCoordinates a ha p).symm).toLinearEquiv.toLinearMap =
      W.lastOrbitGroupForm a ha ℚ_[p]
        (fun i ↦ T (((skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix).prod
          (Pi.basisFun ℚ_[p] (Fin n))) i)) := by
  classical
  set B := (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix).prod
    (Pi.basisFun ℚ_[p] (Fin n)) with hB
  set c := skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
    (W.nonisotropicLastExtension a ha).pairingMatrix with hc
  set L := (((W.lastCayleyProductSourceCoordinates p).symm.trans
        (T.trans (W.lastCayleyProductTargetCoordinates a ha p))).trans
        (W.lastCayleyProductIndexCoordinates a ha p).symm).toLinearEquiv.toLinearMap with hL
  have hcol : ∀ i, L (Pi.basisFun ℚ_[p] _ i) = (c.reindex (W.lastOrbitIndexEquiv a ha)).equivFun
      (T (B i)) := by
    intro i
    have h1 : (W.lastCayleyProductSourceCoordinates p).symm (Pi.basisFun ℚ_[p] _ i) = B i := by
      change B.equivFun.symm (Pi.basisFun ℚ_[p] _ i) = B i
      simp [Pi.basisFun_apply]
    funext j
    change (W.lastCayleyProductIndexCoordinates a ha p).symm
      (W.lastCayleyProductTargetCoordinates a ha p
        (T ((W.lastCayleyProductSourceCoordinates p).symm (Pi.basisFun ℚ_[p] _ i)))) j = _
    rw [h1, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply]
    rfl
  have hdet : LinearMap.det L = (Pi.basisFun ℚ_[p] _).det (fun i ↦ L (Pi.basisFun ℚ_[p] _ i)) := by
    rw [show (fun i ↦ L (Pi.basisFun ℚ_[p] _ i)) = L ∘ (Pi.basisFun ℚ_[p] _) from rfl,
      Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hdet]
  simp_rw [hcol]
  rw [Pi.basisFun_det_apply, ← Matrix.det_transpose]
  have hmat : (Matrix.of fun i j ↦ (c.reindex (W.lastOrbitIndexEquiv a ha)).equivFun (T (B i)) j)ᵀ =
      (c.reindex (W.lastOrbitIndexEquiv a ha)).toMatrix (fun i ↦ T (B i)) := by
    ext i j
    change (c.reindex (W.lastOrbitIndexEquiv a ha)).equivFun (T (B j)) i =
      (c.reindex (W.lastOrbitIndexEquiv a ha)).repr (T (B j)) i
    exact congrFun
      (Module.Basis.equivFun_apply (c.reindex (W.lastOrbitIndexEquiv a ha)) (T (B j))) i
  rw [hmat, ← Module.Basis.det_apply, Module.Basis.det_reindex]
  rfl

section Capstone

local instance capstoneMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance capstoneBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

variable (hSs : HasStrictFDerivAt S dS z)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

include hs hv in
/-- Local p-ADIC change of variables on coordinate balls, with the Haar
modulus evaluated: for any Haar measure `μ` on the source coordinates, the
image of every small coordinate ball under the actual product has measure,
for `μ` transported by the index concatenation, equal to the modulus of the
group determinant form on the actual frame columns times the ball measure. -/
theorem lastCayleyProduct_measure_image_closedBall_groupForm
    (μ : Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    ∃ δ > 0, ∀ (x : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n →
        ℚ_[p]) (ρ : ℝ), closedBall x ρ ⊆ ball (W.lastCayleyProductSourceCoordinates p (Y,0)) δ →
      (μ.map (W.lastCayleyProductIndexCoordinates a ha p))
          (W.lastCayleyProductCoordinateValue a ha p S z v '' closedBall x ρ) =
        (‖W.lastOrbitGroupForm a ha ℚ_[p]
          (Sum.elim (fun i ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
              Y hY X hX hproduct (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
            (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
              Y hY X hX hproduct (0, v j)))‖₊ : ℝ≥0∞) * μ (closedBall x ρ) := by
  obtain ⟨δ, hδ, h⟩ := W.lastCayleyProduct_exists_measure_image_closedBall a ha p S dS z hSs hSO Y
    hY X hX hproduct v hs hv μ (μ.map (W.lastCayleyProductIndexCoordinates a ha p))
  refine ⟨δ, hδ, fun x ρ hsub ↦ ?_⟩
  rw [(h x ρ hsub).2, Padic.addHaarScalarFactor_map_symm_eq_nnnorm_det]
  congr 3
  refine (W.lastCayleyProduct_coordinate_det_eq_groupForm a ha p
    (W.lastCayleyProductFrameEquiv a ha p S dS z hSs hSO Y hY X hX hproduct v hs hv)).trans ?_
  congr 1
  funext i
  exact W.lastCayleyProductFrameMap_prodBasis a ha p S dS z hSs.hasFDerivAt hSO Y hY X hX hproduct v i

include hs hv in
/-- The same ball law combined with the full density law: after the full
higher Cayley source density, the image measure is the rational form ratio,
full lower source density and horizontal orbit-relative factor times the
ball measure. Every factor is kept; none is normalized to one. -/
theorem lastCayleyProduct_measure_image_closedBall_density
    (μ : Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    ∃ δ > 0, ∀ (x : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra W.pairingMatrix)) ⊕ Fin n →
        ℚ_[p]) (ρ : ℝ), closedBall x ρ ⊆ ball (W.lastCayleyProductSourceCoordinates p (Y,0)) δ →
      skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1)
          (W.nonisotropicLastExtension a ha).pairingMatrix ⟨X,hX⟩ *
        (μ.map (W.lastCayleyProductIndexCoordinates a ha p))
          (W.lastCayleyProductCoordinateValue a ha p S z v '' closedBall x ρ) =
        (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
          skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ⟨Y,hY⟩ *
          (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
            lastCoordinateVector
            (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
            (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
              Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) * μ (closedBall x ρ) := by
  obtain ⟨δ, hδ, h⟩ := W.lastCayleyProduct_measure_image_closedBall_groupForm a ha p S dS z hSO Y hY
    X hX hproduct v hSs hs hv μ
  refine ⟨δ, hδ, fun x ρ hsub ↦ ?_⟩
  rw [h x ρ hsub, ← mul_assoc,
    W.lastCayleyProduct_density a ha p S dS z hSs.hasFDerivAt hSO Y hY X hX hproduct v]

end Capstone

end RationalQuadraticSpaceMatrix
