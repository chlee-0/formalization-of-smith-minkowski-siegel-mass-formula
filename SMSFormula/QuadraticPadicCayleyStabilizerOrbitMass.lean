import SMSFormula.QuadraticPadicCayleyOrbitBranchPiece
import SMSFormula.QuadraticPadicCayleyOrbitAction
import SMSFormula.QuadraticPadicSquareBranchFiberGlueIsometry

/-! Orbit-mass form of the stabilizer volume identity. At the identity-centred
chart, for every compact open subgroup `K` of the higher group, every supplied
scalar Haar `ν` and every measure `μ` on the value fiber `{Q = a}` that agrees,
for each `g ∈ K`, with the normalized square-branch measure at `g · x_old` on
measurable subsets of its branch range lying in `K · x_old`,

`vol_G(K) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · μ(K · x_old)`.

The proof partitions `K · x_old` into `[K : K'(K ∩ H)]` translates of `K' · x_old`
(normal `K'` inside a small Cayley image), places each translate in the branch
range at its translated base point, reads its mass through the covariance
and the lower-coordinate cylinder, and combines with the fiber-mass form. The
atlas glue (`padicSquareBranchAtlasGlue`) is the intended `μ`; its
agreement at every `g ∈ K` is not asserted here. No chart, section, baseline or
Haar normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

local instance omPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance omPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance omGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance omGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance omLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance omLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The orbit map of `x_old` in the value fiber is continuous. -/
theorem continuous_smul_lastFiberBasePoint :
    Continuous (fun k : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦ k • W.lastFiberBasePoint p a ha) := by
  have hc : Continuous (fun k : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦ (k.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (hc.matrix_mulVec continuous_const).subtype_mk _

/-- A normal-subgroup translate piece pulls back along its representative to the
`K'`-orbit of `x_old`. -/
theorem preimage_smul_normalOrbitTranslate (K K' : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) (hle : K' ≤ K)
    [(K'.subgroupOf K).Normal]
    (q : K ⧸ (K'.subgroupOf K ⊔ MulAction.stabilizer K (W.lastFiberBasePoint p a ha))) :
    (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ ((q.out : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) • y) ⁻¹'
        MulAction.normalOrbitTranslate (K'.subgroupOf K) (W.lastFiberBasePoint p a ha) q =
      (fun k : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦ k • W.lastFiberBasePoint p a ha) '' (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) := by
  ext y
  simp only [mem_preimage, MulAction.normalOrbitTranslate, mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨g, hg, hgy⟩
    refine ⟨(g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))), (Subgroup.mem_subgroupOf).mp hg, ?_⟩
    have h : ((q.out : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) • ((g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) • W.lastFiberBasePoint p a ha) =
        ((q.out : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) • y := by
      rw [← SemigroupAction.mul_smul]; exact hgy
    exact smul_left_cancel _ h
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, hle hk⟩, (Subgroup.mem_subgroupOf).mpr hk, ?_⟩
    change (((q.out : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) * k) • W.lastFiberBasePoint p a ha = _
    rw [SemigroupAction.mul_smul]

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

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
include hSs hSO hY hproduct hs hv in
/-- Orbit-mass form: at the identity-centred chart, for every compact open subgroup
`K`, every measure `μ` on `{Q = a}` agreeing for each `g ∈ K` with the
normalized branch measure at `g · x_old` on its branch range satisfies
`vol_G(K) = |r| · vol_H(K ∩ H) · (ν(ℤ_p) · μ(K · x_old))`. -/
theorem lastCayleyProduct_measure_compactOpen_eq_orbitMass
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1)
    (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))
    (hKc : IsCompact (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))
    (hKo : IsOpen (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))
    (μ : Measure {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a})
    (hμ : ∀ g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])), g ∈ K →
      ∀ (tH : Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)))
        [tH.IsAddHaarMeasure] (T : Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}), MeasurableSet T →
        T ⊆ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (algebraMap ℚ ℚ_[p] a)) →
        T ⊆ range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) →
        μ T = (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonalProductHaarScalar ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) tH ν
            (Padic.unitHaar p (Fin (n+1))) : ℝ≥0∞)⁻¹ *
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) tH
            (algebraMap ℚ ℚ_[p] a) T) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          (K.comap (W.lastFiberEmbedHom p a ha)) *
        (ν (closedBall 0 1) * μ (range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha))) := by
  classical
  have hsrc : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p := by
    rw [W.cayleyOrbitVectorEquiv_last_eq_one_of_base p a ha X hX hbase]
    exact Rat.one_mem_padicUnitSquareScalarSource p
  obtain ⟨δ1, hδ1, hFM⟩ := W.lastCayleyProduct_exists_forall_measure_compactOpen_fiberMass p a ha S dS
    z hSs hSO Y hY X hX hproduct v hs hv ν hbase K hKc hKo
  obtain ⟨δ2, hδ2, hlast⟩ := W.lastCayleyProduct_exists_forall_orbitPoint_last_mem_source p a ha S dS
    z hSs hSO Y hY X hX hproduct v hsrc
  set r := min δ1 δ2 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < δ1 := by
    rw [hr]; linarith [min_le_left δ1 δ2]
  have hr2 : r < δ2 := by
    rw [hr]; linarith [min_le_right δ1 δ2]
  obtain ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hm, hvol⟩ := hFM r hr0 hr1
  haveI := hnorm
  set xF := W.lastFiberBasePoint p a ha with hxF
  set A := (fun k : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦ k • xF) '' (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) with hA
  have hAc : IsCompact A := hK'c.image (W.continuous_smul_lastFiberBasePoint p a ha)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hAsrc : ∀ y ∈ A, y.1 (Fin.last n) ∈ Rat.padicUnitSquareScalarSource p := by
    rintro _ ⟨k, hk, rfl⟩
    exact hlast r hr0 hr2 k (hK'U hk)
  have hlowA : (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) '' A =
      (fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) := by
    rw [hA, Set.image_image]
    rfl
  have hlowm : MeasurableSet ((fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) '' A) := by
    rw [hlowA]
    have hmHc : Continuous (specialFormPreservingMatrixHom
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hc : Continuous (fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) :=
      continuous_pi fun j ↦ (continuous_apply (Fin.castSucc j)).comp
        (hmHc.matrix_mulVec (continuous_const (y := (lastCoordinateVector : Fin (n+1) → ℚ_[p]))))
    exact (hK'c.image hc).isClosed.measurableSet
  have hcyl := W.lastSquareBranchFiberMeasure_lowerCylinder_eq p a ha hAm hAsrc hlowm
  -- the piece masses
  have hvf : ∀ g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])), (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ g • y) =
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a) :=
    fun g ↦ funext fun y ↦ W.lastFiberMulAction_smul_eq_valueFiberMap p a ha g y
  have hcg : ∀ g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])), Continuous (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ g • y) := fun g ↦ by
    rw [hvf g]; exact ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).continuous_valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a)
  have himg : (fun g' : K ↦ g' • xF) '' ((K'.subgroupOf K : Subgroup K) : Set K) = A := by
    ext y; simp only [mem_image, SetLike.mem_coe, hA]
    constructor
    · rintro ⟨g', hg', rfl⟩; exact ⟨g', (Subgroup.mem_subgroupOf).mp hg', rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hle hk⟩, (Subgroup.mem_subgroupOf).mpr hk, rfl⟩
  have hPm : ∀ q, MeasurableSet (MulAction.normalOrbitTranslate (K'.subgroupOf K) xF q) := by
    intro q
    rw [MulAction.normalOrbitTranslate_eq_image, himg]
    exact (hAc.image (hcg ((q.out : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))).isClosed.measurableSet
  have hpiece : ∀ q, μ (MulAction.normalOrbitTranslate (K'.subgroupOf K) xF q) =
      (ν (closedBall 0 1))⁻¹ * (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) (algebraMap ℚ ℚ_[p] a) A) := by
    intro q
    set g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) := ((q.out : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) with hg
    have hpreV : (((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a))⁻¹'
        (MulAction.normalOrbitTranslate (K'.subgroupOf K) xF q) = A := by
      rw [← hvf g]; exact W.preimage_smul_normalOrbitTranslate p a ha K K' hle q
    have hsub : MulAction.normalOrbitTranslate (K'.subgroupOf K) xF q ⊆
        Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (algebraMap ℚ ℚ_[p] a)) := by
      intro y hy
      have hginv : y = ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a) (g⁻¹ • y) := by
        rw [← W.lastFiberMulAction_smul_eq_valueFiberMap p a ha g, smul_inv_smul]
      have hmem : g⁻¹ • y ∈ A := by
        rw [← hpreV, Set.mem_preimage, ← hginv]; exact hy
      have hrange : g⁻¹ • y ∈ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (algebraMap ℚ ℚ_[p] a)) :=
        (W.mem_range_lastBranch_iff p a ha _ _).mpr (hAsrc _ hmem)
      rw [← QuadraticMap.padicSquareBranchFiberMap_preimage_range_isometry p ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g)
        lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)] at hrange
      rw [hginv]
      exact hrange
    haveI : ProperSpace (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector)) :=
      FiniteDimensional.proper ℚ_[p] _
    have horb : MulAction.normalOrbitTranslate (K'.subgroupOf K) xF q ⊆
        range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) := by
      rw [← MulAction.iUnion_normalOrbitTranslate (K'.subgroupOf K) xF]
      exact Set.subset_iUnion (MulAction.normalOrbitTranslate (K'.subgroupOf K) xF) q
    rw [hμ g q.out.2 Measure.addHaar _ (hPm q) hsub horb,
      W.normalized_fiberMeasure_translate_apply a ha p ν g Measure.addHaar (algebraMap ℚ ℚ_[p] a)
        (hPm q), hpreV]
  have horbit := W.measure_lastFiberOrbit_eq_index_mul p a ha K K' hm μ hPm hpiece
  -- the fiber-mass form at g = 1 with T the lower cylinder
  set C := (fun y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ fun i : Fin n ↦ y.1 i.castSucc) ⁻¹' ((fun k ↦ fun j : Fin n ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K' : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) with hC
  have hCm : MeasurableSet C := by
    rw [hC, ← hlowA]
    exact (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply _).comp measurable_subtype_coe) hlowm
  have hid : (((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] 1).valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a)) ⁻¹' C = C := by
    have h1 : ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] 1).valueFiberMap ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a) = id := by
      funext y
      rw [← W.lastFiberMulAction_smul_eq_valueFiberMap p a ha 1 y, one_smul]
      rfl
    rw [h1, Set.preimage_id]
  haveI : ProperSpace (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] 1 lastCoordinateVector)) :=
    FiniteDimensional.proper ℚ_[p] _
  have hvol1 := hvol 1 Measure.addHaar C hCm hid
  have htr1 := W.normalized_fiberMeasure_translate_apply a ha p ν 1 Measure.addHaar
    (algebraMap ℚ ℚ_[p] a) hCm
  rw [hid] at htr1
  rw [hvol1, htr1, horbit]
  rw [show (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) (algebraMap ℚ ℚ_[p] a) C) = (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMeasure p lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (Measure.map (W.lastOrthogonalLowerEquiv a ha p).symm (Padic.unitHaar p (Fin n))) (algebraMap ℚ ℚ_[p] a) A) by rw [hC, ← hlowA]; exact hcyl]
  ring

end RationalQuadraticSpaceMatrix
