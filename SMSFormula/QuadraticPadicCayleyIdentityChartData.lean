import SMSFormula.QuadraticPadicCayleyGoodPlaceMass
import SMSFormula.QuadraticPadicCayleyGoodPlaceAlmostAll

/-! The identity-chart data of the stabilizer identity, discharged. At the identity
(`X = 0`, `Y = 0`, `z = 0`) the horizontal family `S(c) = Cayley(H(c))` built from
the Cayley map and the skew-adjoint horizontal generators
`H(c) = (c,0)·(F e_last)ᵀ − e_last·(F (c,0))ᵀ` is locally special-orthogonal, has
strict derivative `2·H`, and `2·H(c)·e_last = 2a·(c,0)`, so the transverse
determinant is `(2a)^n ≠ 0`. Hence every stabilizer identity proved at the
identity-centred chart holds with no supplied chart data; in particular the
good-place tube identity holds at every prime outside the explicit finite
exceptional set of `W ⊕ ⟨a⟩`. The generators are the canonical rank-two
skew-adjoint maps of the basis vectors; no chart, section or normalization is
chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The rank-two maps `u (F w)ᵀ − w (F u)ᵀ` are `F`-skew-adjoint for symmetric `F`. -/
theorem vecMulVec_sub_vecMulVec_isSkewAdjoint {F : Matrix ι ι R} (hF : F.IsSymm) (u w : ι → R) :
    F.IsSkewAdjoint (vecMulVec u (F *ᵥ w) - vecMulVec w (F *ᵥ u)) := by
  have hsym : ∀ x : ι → R, x ᵥ* F = F *ᵥ x := fun x ↦ by rw [← mulVec_transpose, hF.eq]
  change (vecMulVec u (F *ᵥ w) - vecMulVec w (F *ᵥ u))ᵀ * F =
    F * -(vecMulVec u (F *ᵥ w) - vecMulVec w (F *ᵥ u))
  rw [transpose_sub, transpose_vecMulVec, transpose_vecMulVec, Matrix.sub_mul, vecMulVec_mul,
    vecMulVec_mul, hsym, hsym, Matrix.mul_neg, Matrix.mul_sub, mul_vecMulVec, mul_vecMulVec]
  abel

end Matrix

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

/-- The lower embedding `c ↦ (c, 0)`. -/
def lastLowerEmbedLinear : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (n+1) → ℚ_[p]) where
  toFun c := Fin.snoc c 0
  map_add' c d := by
    ext r; refine Fin.lastCases ?_ (fun j ↦ ?_) r <;> simp
  map_smul' t c := by
    ext r; refine Fin.lastCases ?_ (fun j ↦ ?_) r <;> simp

/-- The skew-adjoint horizontal generators `H(c) = (c,0)(F e)ᵀ − e (F(c,0))ᵀ`. -/
def lastHorizontalGeneratorLinear :
    (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] where
  toFun c := vecMulVec (lastLowerEmbedLinear p c)
      (((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) *ᵥ lastCoordinateVector) -
    vecMulVec lastCoordinateVector
      (((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) *ᵥ lastLowerEmbedLinear p c)
  map_add' c d := by
    rw [map_add, add_vecMulVec, mulVec_add, vecMulVec_add]; abel
  map_smul' t c := by
    rw [map_smul, mulVec_smul, smul_vecMulVec, vecMulVec_smul, RingHom.id_apply, smul_sub]

theorem lastHorizontalGenerator_mem (c : Fin n → ℚ_[p]) :
    W.lastHorizontalGeneratorLinear p a ha c ∈ skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact vecMulVec_sub_vecMulVec_isSkewAdjoint
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionFormMatrix_isSymm ℚ_[p]) _ _

/-- The generator moves `e_last` to `a · (c, 0)`. -/
theorem lastHorizontalGenerator_mulVec_last (c : Fin n → ℚ_[p]) :
    W.lastHorizontalGeneratorLinear p a ha c *ᵥ lastCoordinateVector =
      algebraMap ℚ ℚ_[p] a • lastLowerEmbedLinear p c := by
  set F := (W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]) with hF
  have hFe : F *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p]) =
      algebraMap ℚ ℚ_[p] a • lastCoordinateVector := by
    ext r
    refine Fin.lastCases ?_ (fun j ↦ ?_) r
    · simp [hF, lastCoordinateVector, Matrix.mulVec_single, nonisotropicLastBlockMatrix_last_last]
    · simp [hF, lastCoordinateVector, Matrix.mulVec_single, nonisotropicLastBlockMatrix_castSucc_last]
  change (vecMulVec (lastLowerEmbedLinear p c) (F *ᵥ lastCoordinateVector) -
    vecMulVec lastCoordinateVector (F *ᵥ lastLowerEmbedLinear p c)) *ᵥ lastCoordinateVector = _
  rw [Matrix.sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, hFe]
  have h1 : (algebraMap ℚ ℚ_[p] a • (lastCoordinateVector : Fin (n+1) → ℚ_[p])) ⬝ᵥ
      lastCoordinateVector = algebraMap ℚ ℚ_[p] a := by
    simp [lastCoordinateVector]
  have h2 : (F *ᵥ lastLowerEmbedLinear p c) ⬝ᵥ lastCoordinateVector = 0 := by
    rw [lastCoordinateVector, dotProduct_single, mul_one, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc]
    simp [lastLowerEmbedLinear, hF, nonisotropicLastBlockMatrix_last_castSucc]
  rw [h1, h2]
  ext r
  simp [mul_comm]

/-- The continuous horizontal generator. -/
def lastHorizontalGenerator :
    (Fin n → ℚ_[p]) →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] :=
  LinearMap.toContinuousLinearMap (W.lastHorizontalGeneratorLinear p a ha)

theorem lastHorizontalGenerator_apply (c : Fin n → ℚ_[p]) :
    W.lastHorizontalGenerator p a ha c = W.lastHorizontalGeneratorLinear p a ha c := rfl

/-- The horizontal family `S(c) = Cayley(H(c))` through the Cayley map. -/
def lastHorizontalFamily (c : Fin n → ℚ_[p]) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] :=
  padicCayleyForwardMatrix p (W.lastHorizontalGenerator p a ha c)

theorem padicCayleyForwardMatrix_zero :
    padicCayleyForwardMatrix p (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = 1 := by
  simp [padicCayleyForwardMatrix]

theorem hasStrictFDerivAt_lastHorizontalFamily :
    HasStrictFDerivAt (W.lastHorizontalFamily p a ha)
      ((2 : ℚ_[p]) • W.lastHorizontalGenerator p a ha) 0 := by
  have h0 : W.lastHorizontalGenerator p a ha 0 ∈ padicCayleySource p := by
    rw [map_zero]; exact zero_mem_padicCayleySource p
  have h1 := hasStrictFDerivAt_padicCayleyForwardMatrix p _ h0
  have heq : padicCayleyForwardDerivative p (W.lastHorizontalGenerator p a ha 0) =
      (2 : ℚ_[p]) • ContinuousLinearMap.id ℚ_[p] (Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) := by
    rw [map_zero]
    exact (hasStrictFDerivAt_padicCayleyForwardMatrix p 0
      (zero_mem_padicCayleySource p)).hasFDerivAt.unique (hasFDerivAt_padicCayleyForwardMatrix_zero p)
  have h2 := h1.comp (0 : Fin n → ℚ_[p]) (W.lastHorizontalGenerator p a ha).hasStrictFDerivAt
  rw [heq] at h2
  convert h2 using 1

theorem lastHorizontalFamily_eventually_mem :
    ∀ᶠ c in 𝓝 (0 : Fin n → ℚ_[p]), W.lastHorizontalFamily p a ha c ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) := by
  have hopen := (isOpen_padicCayleySource (ι := Fin (n+1)) p).preimage
    (W.lastHorizontalGenerator p a ha).continuous
  have h0 : (0 : Fin n → ℚ_[p]) ∈ (W.lastHorizontalGenerator p a ha) ⁻¹' padicCayleySource p := by
    rw [Set.mem_preimage, map_zero]; exact zero_mem_padicCayleySource p
  filter_upwards [hopen.mem_nhds h0] with c hc
  let X : (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    ⟨W.lastHorizontalGenerator p a ha c, W.lastHorizontalGenerator_mem p a ha c⟩
  refine ⟨?_, ?_⟩
  · rw [formPreservingConstraint_eq_zero_iff]
    exact skewAdjointPadicCayleyForwardMatrix_formPreserving _ p X hc
  · exact skewAdjointPadicCayleyForwardMatrix_det_one _ p
      (W.nonisotropicLastExtension a ha).form_det_ne_zero X hc

theorem lastHorizontalFamily_zero_mul :
    W.lastHorizontalFamily p a ha 0 *
        fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p
          (0 : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p
        (0 : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) := by
  simp [lastHorizontalFamily, skewAdjointPadicCayleyForwardMatrix, padicCayleyForwardMatrix]

theorem lastHorizontal_transverse_det_ne_zero :
    (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (((2 : ℚ_[p]) • W.lastHorizontalGenerator p a ha) (Pi.single i 1) *ᵥ
        lastCoordinateVector) j.castSucc) ≠ 0 := by
  set c : ℚ_[p] := 2 * algebraMap ℚ ℚ_[p] a with hc
  have hfam : (fun i j ↦ (((2 : ℚ_[p]) • W.lastHorizontalGenerator p a ha) (Pi.single i 1) *ᵥ
      lastCoordinateVector) (Fin.castSucc j)) = fun i ↦ c • (Pi.basisFun ℚ_[p] (Fin n)) i := by
    funext i j
    rw [ContinuousLinearMap.smul_apply, Matrix.smul_mulVec, lastHorizontalGenerator_apply,
      lastHorizontalGenerator_mulVec_last]
    simp [lastLowerEmbedLinear, hc, mul_assoc]
  rw [hfam]
  have h := (Pi.basisFun ℚ_[p] (Fin n)).det.toMultilinearMap.map_smul_univ (fun _ ↦ c)
    (Pi.basisFun ℚ_[p] (Fin n))
  simp only [AlternatingMap.coe_multilinearMap, Module.Basis.det_self, smul_eq_mul, mul_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  exact pow_ne_zero _ (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha))

theorem lastCayley_zero_orbitVector_last_ne_zero :
    ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p
      (0 : skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
      (zero_mem_skewAdjointPadicCayleySource _ p) lastCoordinateVector) (Fin.last n) ≠ 0 := by
  rw [cayleyOrbitVectorEquiv_apply]
  simp [skewAdjointPadicCayleyForwardMatrix, padicCayleyForwardMatrix, lastCoordinateVector]

theorem lastCayley_zero_base :
    (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1
        ⟨0, zero_mem_skewAdjointPadicCayleySource _ p⟩).1 = 1 := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
  simp

section GoodPlace

local instance icPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance icPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance icGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance icGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance icLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance icLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

/-- Unconditional good-place stabilizer identity: at every prime outside the
explicit finite exceptional set of `W ⊕ ⟨a⟩` (`n ≥ 1`), for the integral
subgroup `K` and every atlas covering the nonisotropic vectors,
`vol_G(K) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · λ(X_a(ℤ_p))`. -/
theorem lastCayleyProduct_measure_padicIntegral_eq_integralPoints_of_notMem (hn : 1 ≤ n)
    (hp : p ∉ W.goodPlaceExceptionalPrimes a ha)
    (point : ℕ → Fin (n+1) → ℚ_[p])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point hpoint i) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero
        (padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          ((padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).comap (W.lastFiberEmbedHom p a ha)) *
        (ν (closedBall 0 1) *
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point hpoint tH ν
            (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a) {y | ‖y.1‖ ≤ 1}) := by
  obtain ⟨h2, hint, hdet, ha1⟩ := W.goodPlace_of_notMem_exceptionalPrimes a ha p hp
  exact W.lastCayleyProduct_measure_padicIntegral_eq_integralPoints p a ha
    (W.lastHorizontalFamily p a ha) ((2 : ℚ_[p]) • W.lastHorizontalGenerator p a ha) 0
    (W.hasStrictFDerivAt_lastHorizontalFamily p a ha) (W.lastHorizontalFamily_eventually_mem p a ha)
    0 (zero_mem_skewAdjointPadicCayleySource _ p) 0 (zero_mem_skewAdjointPadicCayleySource _ p)
    (W.lastHorizontalFamily_zero_mul p a ha) (fun i ↦ Pi.single i 1)
    (W.lastCayley_zero_orbitVector_last_ne_zero p a ha) (W.lastHorizontal_transverse_det_ne_zero p a ha)
    ν (W.lastCayley_zero_base p a ha) h2 hn hint hdet ha1 point hpoint tH hcover

/-- Unconditional good-place local density form: at every prime outside the
explicit finite exceptional set (`n ≥ 1`) there is an open neighbourhood `B₀` of
`a` such that for every measurable `B ⊆ B₀`,
`vol_G(K) · ν(B) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · vol(ℤ_p^(n+1) ∩ Q⁻¹B)`. -/
theorem lastCayleyProduct_measure_padicIntegral_mul_eq_tube_of_notMem (hn : 1 ≤ n)
    (hp : p ∉ W.goodPlaceExceptionalPrimes a ha) :
    ∃ B₀ : Set ℚ_[p], IsOpen B₀ ∧ algebraMap ℚ ℚ_[p] a ∈ B₀ ∧ ∀ B ⊆ B₀, MeasurableSet B →
      padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
          (W.nonisotropicLastExtension a ha).pairingMatrix
          (W.nonisotropicLastExtension a ha).form_det_ne_zero
          (padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) * ν B =
        (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
          padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
            ((padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).comap (W.lastFiberEmbedHom p a ha)) *
          (ν (closedBall 0 1) *
            Padic.unitHaar p (Fin (n+1)) ({y : Fin (n+1) → ℚ_[p] | ‖y‖ ≤ 1} ∩
              (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] ⁻¹' B)) := by
  obtain ⟨h2, hint, hdet, ha1⟩ := W.goodPlace_of_notMem_exceptionalPrimes a ha p hp
  exact W.lastCayleyProduct_measure_padicIntegral_mul_eq_tube p a ha
    (W.lastHorizontalFamily p a ha) ((2 : ℚ_[p]) • W.lastHorizontalGenerator p a ha) 0
    (W.hasStrictFDerivAt_lastHorizontalFamily p a ha) (W.lastHorizontalFamily_eventually_mem p a ha)
    0 (zero_mem_skewAdjointPadicCayleySource _ p) 0 (zero_mem_skewAdjointPadicCayleySource _ p)
    (W.lastHorizontalFamily_zero_mul p a ha) (fun i ↦ Pi.single i 1)
    (W.lastCayley_zero_orbitVector_last_ne_zero p a ha) (W.lastHorizontal_transverse_det_ne_zero p a ha)
    ν (W.lastCayley_zero_base p a ha) h2 hn hint hdet ha1

end GoodPlace

end RationalQuadraticSpaceMatrix
