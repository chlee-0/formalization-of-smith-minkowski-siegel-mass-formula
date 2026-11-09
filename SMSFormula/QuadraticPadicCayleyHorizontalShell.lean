import SMSFormula.QuadraticPadicCayleyLowerGroupHaar

/-! Horizontal coefficients versus the shell graph measure. The lower
coordinates of the actual orbit point, c ↦ (S(z + Σ c_i v_i) · x_old)_lower, are
strictly differentiable at 0 with derivative matrix of determinant exactly the
transverse determinant. The ultrametric local law then says the horizontal
unit-cube Haar is pushed forward with modulus |transverse det|_p, and with the
closed graph formula |orbit-relative| = |(-1)^n / (2 a s)| · |transverse det|,
the product |orbit-relative| × horizontal Haar is the graph (Leray) shell
measure |1/(2 a s)| × lower unit-cube Haar, at the base orbit point with last
coordinate s. No chart, section or baseline is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (p : ℕ) [Fact (Nat.Prime p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (v : Fin n → E)

/-- Lower coordinates of the actual orbit point along the supplied
horizontal directions. -/
def lastCayleyHorizontalLower (c : Fin n → ℚ_[p]) : Fin n → ℚ_[p] :=
  fun j ↦ (S (z + ∑ i, c i • v i) *ᵥ lastCoordinateVector) j.castSucc

/-- The derivative of the horizontal lower-coordinate map. -/
def lastCayleyHorizontalLowerDerivative : (Fin n → ℚ_[p]) →L[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (ContinuousLinearMap.pi fun j : Fin n ↦
      ContinuousLinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin (n+1) ↦ ℚ_[p]) j.castSucc).comp
    ((((Matrix.mulVecBilin ℚ_[p] ℚ_[p]).flip
      (lastCoordinateVector : Fin (n+1) → ℚ_[p])).toContinuousLinearMap).comp
      (dS.comp (Fintype.linearCombination ℚ_[p] v).toContinuousLinearMap))

theorem lastCayleyHorizontalLowerDerivative_apply (c : Fin n → ℚ_[p]) (j : Fin n) :
    lastCayleyHorizontalLowerDerivative p dS v c j =
      (dS (∑ i, c i • v i) *ᵥ lastCoordinateVector) j.castSucc := rfl

variable {S dS z}

/-- The horizontal lower-coordinate map is strictly differentiable at the base. -/
theorem hasStrictFDerivAt_lastCayleyHorizontalLower (hSs : HasStrictFDerivAt S dS z) :
    HasStrictFDerivAt (lastCayleyHorizontalLower p S z v)
      (lastCayleyHorizontalLowerDerivative p dS v) 0 := by
  have hσ : HasStrictFDerivAt (fun c : Fin n → ℚ_[p] ↦ z + ∑ i, c i • v i)
      (Fintype.linearCombination ℚ_[p] v).toContinuousLinearMap 0 := by
    have h := ((Fintype.linearCombination ℚ_[p] v).toContinuousLinearMap.hasStrictFDerivAt
      (x := (0 : Fin n → ℚ_[p]))).const_add z
    convert h using 1
  have hz : z + ∑ i, (0 : Fin n → ℚ_[p]) i • v i = z := by simp
  have hS' : HasStrictFDerivAt S dS (z + ∑ i, (0 : Fin n → ℚ_[p]) i • v i) := by rw [hz]; exact hSs
  have h1 := hS'.comp (0 : Fin n → ℚ_[p]) hσ
  have h2 := (((Matrix.mulVecBilin ℚ_[p] ℚ_[p]).flip
    (lastCoordinateVector : Fin (n+1) → ℚ_[p])).toContinuousLinearMap.hasStrictFDerivAt).comp _ h1
  exact ((ContinuousLinearMap.pi fun j : Fin n ↦
      ContinuousLinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin (n+1) ↦ ℚ_[p]) j.castSucc).hasStrictFDerivAt).comp
    _ h2

variable (dS)

/-- The derivative's determinant is the transverse determinant. -/
theorem det_lastCayleyHorizontalLowerDerivative :
    LinearMap.det (lastCayleyHorizontalLowerDerivative p dS v : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] _) =
      (Pi.basisFun ℚ_[p] (Fin n)).det
        (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) := by
  classical
  rw [← LinearMap.det_toMatrix', Pi.basisFun_det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix'_apply, Matrix.of_apply]
  change (dS (∑ k, (Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) k • v k) *ᵥ lastCoordinateVector)
    j.castSucc = _
  rw [show (∑ k, (Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) k • v k) = v i by
    simpa only [Fintype.linearCombination_apply, one_smul] using
      Fintype.linearCombination_apply_single (R := ℚ_[p]) v i 1]

variable {dS}
variable (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

/-- The derivative as a continuous linear equivalence. -/
def lastCayleyHorizontalLowerEquiv : (Fin n → ℚ_[p]) ≃L[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (LinearMap.equivOfIsUnitDet (f := (lastCayleyHorizontalLowerDerivative p dS v :
      (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] _))
    (isUnit_iff_ne_zero.mpr (by rw [det_lastCayleyHorizontalLowerDerivative]; exact hv))).toContinuousLinearEquiv

theorem lastCayleyHorizontalLowerEquiv_coe :
    ((lastCayleyHorizontalLowerEquiv p v hv : (Fin n → ℚ_[p]) ≃L[ℚ_[p]] _) :
      (Fin n → ℚ_[p]) →L[ℚ_[p]] _) = lastCayleyHorizontalLowerDerivative p dS v := by
  ext c j
  simp [lastCayleyHorizontalLowerEquiv]

section Horizontal

local instance horizontalPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance horizontalPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

include hv in
/-- Horizontal local change of variables: on every sufficiently small closed ball
`B` around 0 of horizontal coefficients, the lower-coordinate map of the actual
orbit point is injective and pushes horizontal unit-cube Haar forward with the
constant modulus |transverse det|_p. -/
theorem lastCayleyHorizontalLower_exists_forall_lintegral_image (hSs : HasStrictFDerivAt S dS z) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      Set.InjOn (lastCayleyHorizontalLower p S z v) (closedBall 0 r) ∧
      ContinuousOn (lastCayleyHorizontalLower p S z v) (closedBall 0 r) ∧
      ∀ g : (Fin n → ℚ_[p]) → ℝ≥0∞,
        ∫⁻ y in lastCayleyHorizontalLower p S z v '' closedBall 0 r, g y ∂(Padic.unitHaar p (Fin n)) =
          (‖(Pi.basisFun ℚ_[p] (Fin n)).det
            (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc)‖₊ : ℝ≥0∞) *
            ∫⁻ c in closedBall 0 r, g (lastCayleyHorizontalLower p S z v c)
              ∂(Padic.unitHaar p (Fin n)) := by
  have hstrict : HasStrictFDerivAt (lastCayleyHorizontalLower p S z v)
      ((lastCayleyHorizontalLowerEquiv p v hv : (Fin n → ℚ_[p]) ≃L[ℚ_[p]] _) :
        (Fin n → ℚ_[p]) →L[ℚ_[p]] _) 0 := by
    rw [lastCayleyHorizontalLowerEquiv_coe]
    exact hasStrictFDerivAt_lastCayleyHorizontalLower p v hSs
  obtain ⟨δ, hδ, h⟩ := hstrict.exists_forall_lintegral_image_closedBall (Padic.unitHaar p (Fin n))
    (Padic.unitHaar p (Fin n))
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  obtain ⟨-, hinj, hcont, hlaw⟩ := h r hr hrδ
  refine ⟨hinj, hcont, fun g ↦ ?_⟩
  rw [hlaw g]
  congr 2
  have hmod := Padic.addHaarScalarFactor_map_symm_eq_nnnorm_det p (Padic.unitHaar p (Fin n))
    (ContinuousLinearEquiv.refl ℚ_[p] (Fin n → ℚ_[p])) (lastCayleyHorizontalLowerEquiv p v hv)
  have hμ : (Padic.unitHaar p (Fin n)).map (ContinuousLinearEquiv.refl ℚ_[p] (Fin n → ℚ_[p])) =
      Padic.unitHaar p (Fin n) := by
    rw [ContinuousLinearEquiv.coe_refl', Measure.map_id]
  simp only [hμ] at hmod
  rw [hmod, ← det_lastCayleyHorizontalLowerDerivative p dS v]
  congr 2
  ext c j
  simp [lastCayleyHorizontalLowerEquiv]

end Horizontal

section Leray

local instance lerayPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance lerayPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)

include hv hs in
/-- |orbit-relative| × horizontal Haar = graph (Leray) shell measure: on every
sufficiently small ball `B` of horizontal coefficients around 0, the actual
horizontal orbit-relative factor times the horizontal unit-Haar lintegral of
`g ∘ φ` (φ = lower coordinates of the actual orbit point) equals the
graph factor |(-1)^n / (2 a s)|_p, with s the last coordinate of the base orbit
point, times the lower unit-Haar lintegral of `g` over φ(B). -/
theorem lastCayleyProduct_orbitRelative_horizontal_eq_leray (hSs : HasStrictFDerivAt S dS z) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → ∀ g : (Fin n → ℚ_[p]) → ℝ≥0∞,
      (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
          lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
            Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
        ∫⁻ c in closedBall 0 r, g (lastCayleyHorizontalLower p S z v c) ∂(Padic.unitHaar p (Fin n)) =
      (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
          ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
            lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) *
        ∫⁻ y in lastCayleyHorizontalLower p S z v '' closedBall 0 r, g y ∂(Padic.unitHaar p (Fin n)) := by
  obtain ⟨δ, hδ, h⟩ := lastCayleyHorizontalLower_exists_forall_lintegral_image p v hv hSs
  refine ⟨δ, hδ, fun r hr hrδ g ↦ ?_⟩
  obtain ⟨-, -, hlaw⟩ := h r hr hrδ
  rw [W.lastCayleyProduct_relative_graph a ha p S dS z hSs.hasFDerivAt hSO Y hY X hX hproduct v hs,
    nnnorm_mul, ENNReal.coe_mul, hlaw g, mul_assoc]

end Leray

end RationalQuadraticSpaceMatrix
