import SMSFormula.QuadraticPadicCayleyStabilizerOrbitIndex
import SMSFormula.QuadraticPadicCayleyFiberCovariance

/-! Fiber-mass form of the stabilizer volume identity. Every element of the Cayley
image of a small exact rectangle moves `x_old` to a point whose lower
coordinates lie in the horizontal image `φ(B)`. Hence, at the identity-centred
chart, the local Leray measure of `lower(K' · x_old)` is the fiber measure of
the lower-coordinate cylinder over it, and by the covariance this equals
`ν(ℤ_p)` times the normalized fiber mass at `g · x_old` of its `g`-translate,
for every group element `g`:

`vol_G(K) = [K : K'(K ∩ H)] · |r| · vol_H(K ∩ H) · ν(ℤ_p) · N_{g x_old}(g · C)`,

with `C` the cylinder `{y | lower y ∈ lower(K' · x_old)}` in the fiber `{Q = a}`
and `ν` a supplied Haar on `ℚ_p`. Identifying the `[K : K'(K ∩ H)]` translates of
`C` with a partition of `K · x_old` is not asserted here. No chart, section,
baseline or Haar normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section StabilizerFiberMass

variable (a : ℚ) (ha : a ≠ 0)

local instance sfPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance sfPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance sfGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance sfGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance sfLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance sfLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance sfLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance sfLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

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
/-- Lower coordinates of the image: on every sufficiently small exact rectangle,
every element of the Cayley image moves `x_old` to a point whose lower
coordinates lie in the horizontal image `φ(B)`. -/
theorem lastCayleyProduct_exists_forall_lower_mem_horizontalImage :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ k ∈ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))), (fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) k ∈ lastCayleyHorizontalLower p S z v '' closedBall 0 r := by
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
  funext j
  change (S (z + ∑ i, q.2 i • v i) *ᵥ lastCoordinateVector) j.castSucc =
    (specialFormPreservingMatrixHom _ _ *ᵥ lastCoordinateVector) j.castSucc
  rw [specialFormPreservingMatrixHom_apply, hmat, ← Matrix.mulVec_mulVec,
    show fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1) *ᵥ
      (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = lastCoordinateVector by
      rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_mulVec_last, one_smul]]

/-- At the identity base point the base orbit point is `x_old`, whose last
coordinate `1` lies in the unit-square source. -/
theorem cayleyOrbitVectorEquiv_last_eq_one_of_base
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1) :
    ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) = 1 := by
  have hm := congrArg (specialFormPreservingMatrixHom
    ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) hbase
  rw [map_one, specialFormPreservingMatrixHom_apply,
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply] at hm
  simp only [OneMemClass.coe_one, Units.val_one, one_mul] at hm
  rw [cayleyOrbitVectorEquiv_apply]
  change (padicCayleyForwardMatrix p (X : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ
    lastCoordinateVector) (Fin.last n) = 1
  rw [show padicCayleyForwardMatrix p (X : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = 1 from hm]
  simp [lastCoordinateVector]

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

set_option maxHeartbeats 1600000 in
include hSs hSO hY hproduct hs hv in
/-- Fiber-mass form: at the identity-centred chart, for every compact open subgroup
`K` and every sufficiently small exact rectangle there is a compact open
`K' ≤ K`, normal in `K`, inside the Cayley image, such that for every element `g`
of the higher group, every transverse Haar at `g · x_old` and every measurable
fiber set `T` pulling back along `g` to the lower cylinder over
`lower(K' · x_old)`,
`vol_G(K) = [K : K'(K ∩ H)] · (|r| · vol_H(K ∩ H) · (ν(ℤ_p) · N_{g x_old}(T)))`. -/
theorem lastCayleyProduct_exists_forall_measure_compactOpen_fiberMass
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1)
    (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))
    (hKc : IsCompact (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))
    (hKo : IsOpen (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∃ K' : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))),
        K' ≤ K ∧ IsCompact (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧ IsOpen (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧
        (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ⊆ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))) ∧ (K'.subgroupOf K).Normal ∧
        ((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index ≠ 0 ∧
        ∀ (g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])
          (targetHaar : Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)))
          [targetHaar.IsAddHaarMeasure]
          (T : Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}),
          MeasurableSet T →
          (((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a)) ⁻¹' T =
            (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦
              fun i : Fin n ↦ y.1 i.castSucc) ⁻¹' ((fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) →
          padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
            (((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index :
                ℝ≥0∞) *
              ((‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
                padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
                  (K.comap (W.lastFiberEmbedHom p a ha)) *
                (ν (closedBall 0 1) *
                  ((((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalProductHaarScalar ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)
                      (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) targetHaar ν (Padic.unitHaar p (Fin (n+1))) : ℝ≥0∞)⁻¹ *
                    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
                      targetHaar (algebraMap ℚ ℚ_[p] a) T))) := by
  obtain ⟨δ1, hδ1, hOI⟩ := W.lastCayleyProduct_exists_forall_measure_compactOpen_orbitIndex p a ha S dS
    z hSs hSO Y hY X hX hproduct v hs hv hbase K hKc hKo
  have hsrc : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p := by
    rw [W.cayleyOrbitVectorEquiv_last_eq_one_of_base p a ha X hX hbase]
    exact Rat.one_mem_padicUnitSquareScalarSource p
  obtain ⟨δ2, hδ2, hLF⟩ := W.lastCayleyProduct_exists_forall_leray_eq_fiberMeasure a ha p S dS z hSs
    hSO Y X hX hproduct v hs hv hsrc
  obtain ⟨δ3, hδ3, hsub⟩ := W.lastCayleyProduct_exists_forall_lower_mem_horizontalImage p a ha S dS z
    hSs hSO Y hY X hX hproduct v
  refine ⟨min (min δ1 δ2) δ3, lt_min (lt_min hδ1 hδ2) hδ3, fun r hr hrδ ↦ ?_⟩
  have hr1 : r < δ1 := hrδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : r < δ2 := hrδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : r < δ3 := hrδ.trans_le (min_le_right _ _)
  obtain ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hm, hvol⟩ := hOI r hr hr1
  refine ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hm, fun g targetHaar _ T hT hTpre ↦ ?_⟩
  set P' := (fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) with hP'
  have hmHc : Continuous (specialFormPreservingMatrixHom
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hP'm : MeasurableSet P' := by
    have hc : Continuous (fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) :=
      continuous_pi fun j ↦ (continuous_apply (Fin.castSucc j)).comp
        (hmHc.matrix_mulVec (continuous_const (y := (lastCoordinateVector : Fin (n+1) → ℚ_[p]))))
    exact (hK'c.image hc).isClosed.measurableSet
  have hP'sub : P' ⊆ lastCayleyHorizontalLower p S z v '' closedBall 0 r := by
    rintro _ ⟨k, hk, rfl⟩
    exact hsub r hr hr3 k (hK'U hk)
  have hL := hLF r hr hr2 (P'.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞)) (measurable_one.indicator hP'm)
  rw [lintegral_indicator_one hP'm, Measure.restrict_apply hP'm, Set.inter_eq_left.mpr hP'sub] at hL
  have hlowm : Measurable (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦
      fun i : Fin n ↦ y.1 i.castSucc) :=
    measurable_pi_lambda _ fun i ↦ (measurable_pi_apply _).comp measurable_subtype_coe
  have hind : (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦
      (lastCayleyHorizontalLower p S z v '' closedBall 0 r).indicator (P'.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞))
        (fun i : Fin n ↦ y.1 i.castSucc)) =
      ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦
        fun i : Fin n ↦ y.1 i.castSucc) ⁻¹' P').indicator (1 : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} → ℝ≥0∞) := by
    funext y
    by_cases hy : (fun i : Fin n ↦ y.1 i.castSucc) ∈ P'
    · simp only [Set.indicator, Set.mem_preimage, hy, hP'sub hy, if_true, Pi.one_apply]
    · simp only [Set.indicator, Set.mem_preimage, hy, if_false, ite_self]
  rw [hind, lintegral_indicator_one (hlowm hP'm)] at hL
  have htr := W.normalized_fiberMeasure_translate_apply a ha p ν g targetHaar (algebraMap ℚ ℚ_[p] a) hT
  rw [hTpre] at htr
  rw [htr, ← mul_assoc (ν (closedBall 0 1)), ENNReal.mul_inv_cancel
      (Metric.measure_closedBall_pos ν 0 one_pos).ne'
      (isCompact_closedBall (0 : ℚ_[p]) 1).measure_lt_top.ne, one_mul, ← hL, hvol]
  ring

end StabilizerFiberMass

end RationalQuadraticSpaceMatrix
