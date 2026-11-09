import SMSFormula.QuadraticPadicCayleyStabilizerOrbitMass
import SMSFormula.QuadraticPadicSquareBranchAtlasGlue

/-! Atlas-glue form of the stabilizer volume identity. For any countable family of
fiber points whose branch ranges cover `K · x_old` (with supplied transverse
Haars), the atlas glue agrees with the normalized branch measure at every
`g · x_old` on the covered part of its range, so at the identity-centred chart

`vol_G(K) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · glue(K · x_old)`.

Such covering families exist and can be taken inside `K · x_old`: every orbit
point lies in the branch range at itself, branch ranges are open, and
`K · x_old` is compact. The glue's value on `K · x_old` is therefore independent
of the covering family. No chart, section, baseline or Haar normalization is
chosen: the family and the transverse Haars are supplied or obtained by
existence. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

local instance ogPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ogPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance ogGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ogGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance ogLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ogLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Every orbit point lies in the branch range at itself. -/
theorem smul_lastFiberBasePoint_mem_range (g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :
    g • W.lastFiberBasePoint p a ha ∈ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)) := by
  have hbase : W.lastFiberBasePoint p a ha ∈ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p
      lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)) := by
    rw [W.mem_range_lastBranch_iff p a ha]
    change (lastCoordinateVector : Fin (n+1) → ℚ_[p]) (Fin.last n) ∈ _
    simpa [lastCoordinateVector] using Rat.one_mem_padicUnitSquareScalarSource p
  rw [← QuadraticMap.padicSquareBranchFiberMap_preimage_range_isometry p ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g)
    lastCoordinateVector (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)] at hbase
  rw [W.lastFiberMulAction_smul_eq_valueFiberMap p a ha g]
  exact hbase

/-- Branch ranges depend only on the base point. -/
theorem range_lastBranch_congr {x y : Fin (n+1) → ℚ_[p]} (h : x = y)
    (hx : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) x ≠ 0) (hy : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) y ≠ 0) :
    Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p x hx (algebraMap ℚ ℚ_[p] a)) =
      Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p y hy (algebraMap ℚ ℚ_[p] a)) := by
  subst h; rfl

set_option maxHeartbeats 800000 in
/-- Covering families exist: for a compact subgroup `K` there is a sequence of
points of `K · x_old` whose branch ranges cover `K · x_old`. -/
theorem exists_lastFiberOrbit_branchCover (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))
    (hKc : IsCompact (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) :
    ∃ pts : ℕ → {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}, (∀ i, pts i ∈ range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha)) ∧
      range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) ⊆
        ⋃ i, Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p (pts i).1 (by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : Continuous (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) :=
    (W.continuous_smul_lastFiberBasePoint p a ha).comp continuous_subtype_val
  have hOc : IsCompact (range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha)) :=
    isCompact_range hcont
  set U : K → Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} := fun γ ↦ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p
    ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] (γ : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)) with hU
  have hUo : ∀ γ, IsOpen (U γ) := fun γ ↦
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).isOpenEmbedding_padicSquareBranchFiberMap p _ _ _).isOpen_range
  have hcov : range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) ⊆ ⋃ γ, U γ := by
    rintro _ ⟨γ, rfl⟩
    exact Set.mem_iUnion.mpr ⟨γ, W.smul_lastFiberBasePoint_mem_range p a ha (γ : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))⟩
  obtain ⟨t, ht⟩ := hOc.elim_finite_subcover U hUo hcov
  set pts : ℕ → {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} := fun i ↦ ((t.toList.getD i 1 : K) : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) • W.lastFiberBasePoint p a ha
    with hpts
  refine ⟨pts, fun i ↦ ⟨t.toList.getD i 1, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨γ, hγt, hyγ⟩ := Set.mem_iUnion₂.mp (ht hy)
  obtain ⟨i, hi, hiγ⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hγt)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hget : t.toList.getD i 1 = γ := by
    rw [List.getD_eq_getElem _ _ hi, hiγ]
  have hpt : (pts i).1 = (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] (γ : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) lastCoordinateVector := by
    rw [hpts]
    simp only [hget]
    rw [lastFiberMulAction_smul_val, specialOrthogonalMatrixGroupIsometryEquiv_padic_apply]
    rfl
  have hrange : Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p (pts i).1 (by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)) =
      U γ := by
    rw [hU]
    exact W.range_lastBranch_congr p a ha hpt _ _
  rw [hrange]
  exact hyγ

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

include hSs hSO hY hproduct hs hv in
/-- Atlas-glue form: at the identity-centred chart, for every compact open subgroup
`K` and every countable family of fiber points whose branch ranges cover
`K · x_old` (supplied transverse Haars),
`vol_G(K) = |r| · vol_H(K ∩ H) · (ν(ℤ_p) · glue(K · x_old))`. -/
theorem lastCayleyProduct_measure_compactOpen_eq_atlasGlue
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1)
    (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))
    (hKc : IsCompact (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))
    (hKo : IsOpen (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))
    (pts : ℕ → {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a})
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (pts i).1)) [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) ⊆
        ⋃ i, Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p (pts i).1 (by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a))) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          (K.comap (W.lastFiberEmbedHom p a ha)) *
        (ν (closedBall 0 1) *
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p (fun i ↦ (pts i).1) (fun i ↦ by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) tH ν
            (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a)
            (range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha))) := by
  refine W.lastCayleyProduct_measure_compactOpen_eq_orbitMass p a ha S dS z hSs hSO Y hY X hX
    hproduct v hs hv ν hbase K hKc hKo _ ?_
  intro g _ tH' _ T hT hTr hTo
  have h := W.nonisotropicLastExtension a ha |>.commutativeScalarExtensionQuadraticForm ℚ_[p] |>.padicSquareBranchAtlasGlue_restrict_of_point p
    (fun i ↦ (pts i).1) (fun i ↦ by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) tH ν (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a)
    ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) tH'
  have hTS : T ⊆ Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g lastCoordinateVector) (by rw [QuadraticMap.IsometryEquiv.map_app, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (algebraMap ℚ ℚ_[p] a)) ∩
        ⋃ i, Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p (pts i).1 (by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)) :=
    fun y hy ↦ ⟨hTr hy, hcover (hTo hy)⟩
  have h' := congrArg (fun m : Measure {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} ↦ m T) h
  simp only [Measure.restrict_apply hT, Set.inter_eq_left.mpr hTS, Measure.smul_apply,
    smul_eq_mul] at h'
  exact h'

end RationalQuadraticSpaceMatrix
