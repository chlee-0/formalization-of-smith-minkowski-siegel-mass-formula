import SMSFormula.QuadraticPadicCayleyStabilizerFiberMass

/-! Orbit pieces on the branch at `x_old`. The branch range at `x_old` for
the value `a` is exactly the set of fiber points whose last coordinate lies in the
unit-square source; on it, lower coordinates determine the point. Hence
the fiber measure at `x_old` gives the lower-coordinate cylinder over any
measurable set of branch points the mass of that set. Elements of sufficiently
small Cayley images move `x_old` onto the branch (when the base last coordinate
is in the source, e.g. at the identity base), so these statements apply to
the orbit pieces `K' · x_old`. No chart, section or square root is chosen: the
branch is the one. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

local instance bpPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance bpPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The decomposition at `x_old` reads the last coordinate as the normal
coefficient. -/
theorem lastDecomposition_symm_snd (y : Fin (n+1) → ℚ_[p]) :
    ((((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalDecompositionContinuousLinearEquiv lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)).symm y).2 = y (Fin.last n) := by
  set D := ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalDecompositionContinuousLinearEquiv lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
    with hD
  have h : (D.symm y).2 • (lastCoordinateVector : Fin (n+1) → ℚ_[p]) + (D.symm y).1.1 = y := by
    rw [← anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply]
    exact D.apply_symm_apply y
  have h' := congrFun h (Fin.last n)
  simp only [Pi.add_apply, Pi.smul_apply, lastCoordinateVector, Pi.single_eq_same, smul_eq_mul,
    mul_one] at h'
  calc (D.symm y).2 = (D.symm y).2 + (D.symm y).1.1 (Fin.last n) := by
        rw [W.lastOrthogonal_coordinate_zero a ha (D.symm y).1, add_zero]
    _ = y (Fin.last n) := h'

/-- The branch range at `x_old`: fiber points whose last coordinate lies in
the unit-square source. -/
theorem mem_range_lastBranch_iff (value : ℚ_[p])
    (y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = value}) :
    y ∈ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) value) ↔
      y.1 (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p := by
  rw [QuadraticMap.range_padicSquareBranchFiberMap]
  simp only [mem_setOf_eq]
  rw [W.lastDecomposition_symm_snd p a ha]

/-- Lower coordinates determine branch points: two points of the fiber `{Q = a}`
with last coordinates in the source and equal lower coordinates coincide. -/
theorem eq_of_lower_eq_of_last_mem_source {y y' : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}}
    (hy : y.1 (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p)
    (hy' : y'.1 (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p)
    (hlow : ∀ i : Fin n, y.1 i.castSucc = y'.1 i.castSucc) : y = y' := by
  have ha' : algebraMap ℚ ℚ_[p] a ≠ 0 := (map_ne_zero _).mpr ha
  have hs := W.nonisotropicLastExtension_quadratic_split a ha p y.1
  have hs' := W.nonisotropicLastExtension_quadratic_split a ha p y'.1
  have hsnoc : (Fin.snoc (fun i ↦ y.1 i.castSucc) 0 : Fin (n+1) → ℚ_[p]) =
      Fin.snoc (fun i ↦ y'.1 i.castSucc) 0 := by
    rw [show (fun i : Fin n ↦ y.1 i.castSucc) = fun i ↦ y'.1 i.castSucc from funext hlow]
  rw [y.2, hsnoc] at hs
  rw [y'.2] at hs'
  have hsq : y.1 (Fin.last n) ^ 2 = y'.1 (Fin.last n) ^ 2 := by
    have h2 : y.1 (Fin.last n) * y.1 (Fin.last n) * algebraMap ℚ ℚ_[p] a =
        y'.1 (Fin.last n) * y'.1 (Fin.last n) * algebraMap ℚ ℚ_[p] a := by
      linear_combination hs' - hs
    have h3 := mul_right_cancel₀ ha' h2
    rw [_root_.sq, _root_.sq]; exact h3
  have hlast : y.1 (Fin.last n) = y'.1 (Fin.last n) := by
    rw [← Rat.padicUnitSquareScalarInverse_sq p hy, hsq, Rat.padicUnitSquareScalarInverse_sq p hy']
  apply Subtype.ext
  funext i
  cases i using Fin.lastCases with
  | last => exact hlast
  | cast i => exact hlow i

/-- The {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} measure of the lower cylinder over branch points: for a measurable
set `A` of branch points whose lower-coordinate image is measurable, the
lower-coordinate fiber measure at `x_old` gives the cylinder over `lower(A)` the
mass of `A`. -/
theorem lastSquareBranchFiberMeasure_lowerCylinder_eq {A : Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}} (hAm : MeasurableSet A)
    (hA : ∀ y ∈ A, y.1 (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p)
    (hlowm : MeasurableSet ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) '' A)) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n)))
        (algebraMap ℚ ℚ_[p] a)
        ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) ⁻¹'
          ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) '' A)) =
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n)))
        (algebraMap ℚ ℚ_[p] a) A := by
  set f := ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)
    with hf
  have hfm := ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).measurable_padicSquareBranchFiberMap p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
    (algebraMap ℚ ℚ_[p] a)
  have hlowc : Measurable (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) :=
    measurable_pi_lambda _ fun i ↦ (measurable_pi_apply _).comp measurable_subtype_coe
  have hpre : f ⁻¹' ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) ⁻¹'
      ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) '' A)) = f ⁻¹' A := by
    ext t
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨y, hyA, hyl⟩
      have hft : (f t).1 (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p :=
        (W.mem_range_lastBranch_iff p a ha _ (f t)).mp ⟨t, rfl⟩
      have hyt := W.eq_of_lower_eq_of_last_mem_source p a ha (hA y hyA) hft
        (fun i ↦ congrFun hyl i)
      rw [← hyt]; exact hyA
    · intro ht
      exact ⟨f t, ht, rfl⟩
  rw [padicSquareBranchFiberMeasure, Measure.map_apply hfm (hlowc hlowm), Measure.map_apply hfm hAm,
    ← hf, hpre]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
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

include hSs hSO hY hX hproduct in
/-- Orbit points of small Cayley images are actual-product orbit points
`S(z + Σ c_i v_i) · x_old` with `c` in the horizontal ball. -/
theorem lastCayleyProduct_exists_forall_orbitPoint_eq :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ k ∈ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))), ∃ c ∈ closedBall (0 : Fin n → ℚ_[p]) r,
        (specialFormPreservingMatrixHom
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k) *ᵥ lastCoordinateVector = S (z + ∑ i, c i • v i) *ᵥ lastCoordinateVector := by
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  have hCM := W.lastCayleyProduct_eventually_chart_matrix a ha p S dS z hSs hSO Y hY X hX hproduct v
  have ht : Tendsto eE.symm (𝓝 (eE (Y,0))) (𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p]))) := by
    have := eE.symm.continuous.continuousAt.tendsto (x := eE (Y,0))
    rwa [ContinuousLinearEquiv.symm_apply_apply] at this
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (ht.eventually hCM)
  refine ⟨ε, hε, fun r hr hrε k hk ↦ ?_⟩
  obtain ⟨_, ⟨⟨y, hy⟩, ⟨q, hqR, hqy⟩, rfl⟩, rfl⟩ := hk
  subst hqy
  have hq := hεP (show dist (eE q) (eE (Y,0)) < ε from
    (mem_closedBall.mp hqR).trans_lt hrε)
  rw [ContinuousLinearEquiv.symm_apply_apply] at hq
  have hmat := hq hy
  have hrect := W.lastCayleyProductSourceCoordinates_preimage_closedBall p Y hr.le
  have hqB : q.2 ∈ closedBall (0 : Fin n → ℚ_[p]) r := by
    rw [hrect] at hqR; exact hqR.2
  refine ⟨q.2, hqB, ?_⟩
  rw [specialFormPreservingMatrixHom_apply, hmat, ← Matrix.mulVec_mulVec,
    show fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1) *ᵥ
      (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = lastCoordinateVector by
      rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_mulVec_last, one_smul]]

include hSs hSO hY hX hproduct in
/-- Orbit points of small images Lie on the branch: when the base last
coordinate lies in the unit-square source, every element of a sufficiently
small Cayley image moves `x_old` to a point whose last coordinate lies there. -/
theorem lastCayleyProduct_exists_forall_orbitPoint_last_mem_source
    (hsrc : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ k ∈ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))), ((specialFormPreservingMatrixHom
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k) *ᵥ lastCoordinateVector) (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p := by
  obtain ⟨δ1, hδ1, hpt⟩ := W.lastCayleyProduct_exists_forall_orbitPoint_eq p a ha S dS z hSs hSO Y hY
    X hX hproduct v
  set yv : (Fin n → ℚ_[p]) → (Fin (n+1) → ℚ_[p]) :=
    fun c ↦ S (z + ∑ i, c i • v i) *ᵥ lastCoordinateVector with hyv
  have hlin : Tendsto (fun c : Fin n → ℚ_[p] ↦ z + ∑ i, c i • v i) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun c : Fin n → ℚ_[p] ↦ z + ∑ i, c i • v i) := by fun_prop
    simpa using hc.tendsto 0
  have hy0 : yv 0 (Fin.last n) = ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) := by
    simp only [hyv, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
      cayleyOrbitVectorEquiv_apply]
    rw [← hproduct, ← Matrix.mulVec_mulVec, show fixLastBlockMatrix
        (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) *ᵥ
        (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = lastCoordinateVector by
      rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_mulVec_last, one_smul]]
  have hylast : Tendsto (fun c ↦ yv c (Fin.last n)) (𝓝 0)
      (𝓝 (((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
        lastCoordinateVector) (Fin.last n))) := by
    rw [← hy0]
    have hS : Tendsto (fun c : Fin n → ℚ_[p] ↦ S (z + ∑ i, c i • v i)) (𝓝 0) (𝓝 (S z)) :=
      hSs.continuousAt.tendsto.comp hlin
    have hmv0 : Continuous (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] ↦
        M *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) :=
      continuous_id.matrix_mulVec continuous_const
    have hmv : Continuous (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p] ↦
        (M *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) (Fin.last n)) :=
      (continuous_apply (Fin.last n)).comp hmv0
    have h0 : S z = S (z + ∑ i, (0 : Fin n → ℚ_[p]) i • v i) := by simp
    rw [h0] at hS
    exact (hmv.tendsto _).comp hS
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp
    (hylast ((Rat.isOpen_padicUnitSquareScalarSource p).mem_nhds hsrc))
  refine ⟨min δ1 ε, lt_min hδ1 hε, fun r hr hrδ k hk ↦ ?_⟩
  obtain ⟨c, hc, hkc⟩ := hpt r hr (hrδ.trans_le (min_le_left _ _)) k hk
  rw [hkc]
  exact hεN (closedBall_subset_ball (hrδ.trans_le (min_le_right _ _)) hc)

end RationalQuadraticSpaceMatrix
