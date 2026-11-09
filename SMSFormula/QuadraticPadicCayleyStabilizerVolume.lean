import SMSFormula.QuadraticPadicCayleyLocalVolume

/-! Local stabilizer volume identity. For a supplied compact subgroup `K` of the
higher group lying inside the Cayley image of a sufficiently small exact
coordinate rectangle, the repository higher group-Haar volume of `K` equals the
rational form ratio × the repository lower group-Haar volume of `K ∩ H` (read
through the block embedding `fixLastBlockMatrix`) × the Leray factor ×
the lower unit-Haar mass of the orbit `K · x_old` in lower coordinates.

The fiber over each horizontal coefficient is a left translate of `K ∩ H` or
empty, so only left invariance of the lower Haar is consumed; the rectangle is
where the fiber product was proved, and `K` inside its image is what makes the
full fiber land in the rectangle. No chart, section, baseline, representative or
Haar normalization is chosen; the existence of such `K` is not asserted here. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

/-- Fibers of a translated subgroup test are left translates: for monoid-valued
readings `m` of `G` and `j` of `H`, the set of `h` with `s · j h ∈ m(K)` is, once
nonempty, a left translate of `j⁻¹(m(K))`, hence has the same left-invariant
measure. -/
theorem MeasureTheory.measure_translatedFiber_eq {G H R : Type*} [Group G] [Group H] [Monoid R]
    (m : G →* R) (j : H →* R) (K : Subgroup G) (s : R) [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [μ.IsMulLeftInvariant] {h₀ : H} (hh₀ : s * j h₀ ∈ m '' (K : Set G)) :
    μ ((fun h ↦ s * j h) ⁻¹' (m '' (K : Set G))) = μ (j ⁻¹' (m '' (K : Set G))) := by
  obtain ⟨k₀, hk₀, hk₀e⟩ := hh₀
  have hset : (fun h ↦ s * j h) ⁻¹' (m '' (K : Set G)) =
      (fun h ↦ h₀⁻¹ * h) ⁻¹' (j ⁻¹' (m '' (K : Set G))) := by
    ext h
    simp only [mem_preimage, mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨k, hk, hke⟩
      refine ⟨k₀⁻¹ * k, K.mul_mem (K.inv_mem hk₀) hk, ?_⟩
      calc m (k₀⁻¹ * k) = m k₀⁻¹ * (s * j h) := by rw [map_mul, hke]
        _ = m k₀⁻¹ * (s * j h₀) * j (h₀⁻¹ * h) := by
          rw [mul_assoc, mul_assoc, ← map_mul j, mul_inv_cancel_left]
        _ = j (h₀⁻¹ * h) := by rw [← hk₀e, ← map_mul, inv_mul_cancel, map_one, one_mul]
    · rintro ⟨k, hk, hke⟩
      refine ⟨k₀ * k, K.mul_mem hk₀ hk, ?_⟩
      rw [map_mul, hk₀e, hke, mul_assoc, ← map_mul, mul_inv_cancel_left]
  rw [hset, measure_preimage_mul]

/-- The block embedding `fixLastBlockMatrix` as a monoid homomorphism. -/
def fixLastBlockMonoidHom (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin (n+1)) (Fin (n+1)) R where
  toFun := RationalQuadraticSpaceMatrix.fixLastBlockMatrix
  map_one' := RationalQuadraticSpaceMatrix.fixLastBlockMatrix_one
  map_mul' := RationalQuadraticSpaceMatrix.fixLastBlockMatrix_mul

/-- The matrix reading of the special form-preserving group. -/
def specialFormPreservingMatrixHom {n : ℕ} {R : Type*} [CommRing R] (F : Matrix (Fin n) (Fin n) R) :
    specialFormPreservingMatrixSubgroup F →* Matrix (Fin n) (Fin n) R :=
  (Units.coeHom _).comp ((formPreservingMatrixSubgroup F).subtype.comp
    (specialFormPreservingMatrixSubgroup F).subtype)

theorem specialFormPreservingMatrixHom_apply {n : ℕ} {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingMatrixHom F g = (g.1.1.1 : Matrix (Fin n) (Fin n) R) := rfl

theorem specialFormPreservingMatrixHom_injective {n : ℕ} {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) : Function.Injective (specialFormPreservingMatrixHom F) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext (Units.ext h))

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section StabilizerVolume

variable (a : ℚ) (ha : a ≠ 0)

local instance svPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance svPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance svSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance svSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance svLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance svLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance svGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance svGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance svLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance svLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance svLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance svLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance svHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance svHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

/-- The identity-translated lower Cayley chart reads, as a matrix, the forward
Cayley formula. -/
theorem lastCayleyLowerChart_matrix (X' : skewAdjointPadicCayleySource W.pairingMatrix p) :
    specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))
        (skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 X').1 =
      skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p X'.1 := by
  rw [specialFormPreservingMatrixHom_apply, coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
  simp only [OneMemClass.coe_one, Units.val_one, one_mul]
  rfl

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

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
include hSs hSO hY hproduct hs hv in
/-- Local stabilizer volume identity: for every sufficiently small exact
coordinate rectangle around `(Y, 0)` and every supplied compact subgroup `K` of
the higher group inside the Cayley image of the actual product on it,
`vol_G(K) = |r| · vol_H(K ∩ H) · |(-1)^n/(2 a s)| · vol(K · x_old)`, with `K ∩ H`
read through the block embedding and `K · x_old` in lower coordinates. -/
theorem lastCayleyProduct_exists_forall_measure_subgroup :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ K : Subgroup (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))),
        IsCompact (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) →
        (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ⊆
          Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))) →
        padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
            (W.nonisotropicLastExtension a ha).pairingMatrix
            (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
              ((fun h ↦ fixLastBlockMatrix
                  (specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) h)) ⁻¹'
                (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ''
                    (K : Set _))) *
            (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
              ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
                lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) *
            Padic.unitHaar p (Fin n)
              ((fun k ↦ fun j ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K : Set _)) := by
  classical
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  set h1 := skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 with hh1
  set mH := specialFormPreservingMatrixHom
    ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) with hmH
  set mL := specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) with hmL
  obtain ⟨δ1, hδ1, hBG⟩ := W.lastCayleyProduct_exists_forall_lintegral_bothGroups p a ha S dS z hSs
    hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ2, hδ2, hGR⟩ := W.lastCayleyProduct_exists_forall_lintegral_groupHaar_repository p a ha S dS
    z hSs hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ3, hδ3, hRep⟩ := W.lastCayleyProduct_exists_forall_lintegral_image_repository a ha p S dS z
    hSs hSO Y hY X hX hproduct v hs hv
  obtain ⟨δ4, hδ4, hH⟩ := lastCayleyHorizontalLower_exists_forall_lintegral_image p v hv hSs
  obtain ⟨δ5, hδ5, hL⟩ := lastCayleyProduct_orbitRelative_horizontal_eq_leray (p := p) (v := v)
    (hv := hv) (W := W) (a := a) (ha := ha) (hSO := hSO) (Y := Y) (hY := hY) (X := X) (hX := hX)
    (hproduct := hproduct) (hs := hs) hSs
  have hCM := W.lastCayleyProduct_eventually_chart_matrix a ha p S dS z hSs hSO Y hY X hX hproduct v
  have hcontE : ContinuousAt eE.symm (eE (Y,0)) := eE.symm.continuous.continuousAt
  have hCMc : {x | ∀ hq : ((W.lastCayleyProductFrameValue a ha p S z v (eE.symm x) : skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
        (skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p,
      ((skewAdjointPadicCayleyTranslatedHomeomorph (W.nonisotropicLastExtension a ha).pairingMatrix p
          (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨_, hq⟩).1.1.1.1 :
          Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) =
        S (z + ∑ i, (eE.symm x).2 i • v i) *
          fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p (eE.symm x).1)} ∈
      𝓝 (eE (Y,0)) := by
    rw [← eE.symm_apply_apply (Y,0)] at hCM
    exact hcontE.preimage_mem_nhds hCM
  have hsrcN : {q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p]) | (q.1 : (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource W.pairingMatrix p} ∈ 𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])) :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_skewAdjointPadicCayleySource _ p).mem_nhds hY)
  have hsrcC : {x | ((eE.symm x).1 : (skewAdjointMatricesLieSubalgebra
      (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource W.pairingMatrix p} ∈ 𝓝 (eE (Y,0)) := by
    rw [← eE.symm_apply_apply (Y,0)] at hsrcN
    exact hcontE.preimage_mem_nhds hsrcN
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hCMc hsrcC)
  refine ⟨min (min (min δ1 δ2) (min δ4 δ5)) (min ε δ3),
    lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ4 hδ5)) (lt_min hε hδ3),
    fun r hr hrδ K hKc hKU ↦ ?_⟩
  have hr1 : r < δ1 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hr2 : r < δ2 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hr4 : r < δ4 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr5 : r < δ5 := hrδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr3 : r < ε := hrδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr6 : r < δ3 := hrδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsubsrc, -, -⟩ := hGR r hr hr2
  obtain ⟨-, hFVc, -⟩ := hRep r hr hr6
  obtain ⟨hinjH, hcontH, -⟩ := hH r hr hr4
  have hKm0 : MeasurableSet (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) :=
    hKc.isClosed.measurableSet
  set hor := lastCayleyHorizontalLower p S z v with hhor
  set R := eE ⁻¹' closedBall (eE (Y,0)) r with hR
  set B := closedBall (0 : Fin n → ℚ_[p]) r with hB
  set U1 : Set (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
    (skewAdjointPadicCoordinateEquiv W.pairingMatrix p) ⁻¹'
      closedBall (skewAdjointPadicCoordinateEquiv W.pairingMatrix p Y) r with hU1
  have hrect : R = U1 ×ˢ B := W.lastCayleyProductSourceCoordinates_preimage_closedBall p Y hr.le
  -- on the rectangle: the chart matrix is the actual product and the lower coordinate is in the source
  have hRpt : ∀ q ∈ R,
      (∀ hq : ((W.lastCayleyProductFrameValue a ha p S z v q : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
          (skewAdjointMatricesLieSubalgebra
            ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
          skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p,
        mH (skewAdjointPadicCayleyTranslatedHomeomorph (W.nonisotropicLastExtension a ha).pairingMatrix p
          (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨_, hq⟩).1 =
          S (z + ∑ i, q.2 i • v i) *
            fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1)) ∧
      (q.1 : (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource W.pairingMatrix p := by
    intro q hq
    have h := hεsub (closedBall_subset_ball hr3 hq)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] at h
    exact ⟨h.1, h.2⟩
  -- every element of the image decomposes as the actual product
  have hdec : ∀ k ∈ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
        (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v '' R))),
      ∃ q ∈ R, ∃ hq1 : (q.1 : (skewAdjointMatricesLieSubalgebra
          (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
          skewAdjointPadicCayleySource W.pairingMatrix p,
        mH k = S (z + ∑ i, q.2 i • v i) * fixLastBlockMatrix (mL (h1 ⟨q.1, hq1⟩).1) := by
    rintro k ⟨_, ⟨⟨y, hy⟩, ⟨q, hqR, hqy⟩, rfl⟩, rfl⟩
    obtain ⟨hmat, hq1⟩ := hRpt q hqR
    refine ⟨q, hqR, hq1, ?_⟩
    rw [W.lastCayleyLowerChart_matrix p]
    subst hqy
    exact hmat hy
  -- the horizontal reading of an actual product
  have hhor_prod : ∀ c : Fin n → ℚ_[p], ∀ M : Matrix (Fin n) (Fin n) ℚ_[p],
      (fun j ↦ ((S (z + ∑ i, c i • v i) * fixLastBlockMatrix M) *ᵥ
        (lastCoordinateVector : Fin (n+1) → ℚ_[p])) j.castSucc) = hor c := by
    intro c M
    rw [← Matrix.mulVec_mulVec, show fixLastBlockMatrix M *ᵥ
        (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = lastCoordinateVector by
      rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_mulVec_last, one_smul]]
    rfl
  -- the recovered coefficient is the given one
  have hcoef : ∀ c ∈ B, ∀ k ∈ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
        (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v '' R))),
      (fun j ↦ (mH k *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) j.castSucc) = hor c →
      ∃ q ∈ R, q.2 = c ∧ ∃ hq1 : (q.1 : (skewAdjointMatricesLieSubalgebra
          (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
          skewAdjointPadicCayleySource W.pairingMatrix p,
        mH k = S (z + ∑ i, c i • v i) * fixLastBlockMatrix (mL (h1 ⟨q.1, hq1⟩).1) := by
    intro c hc k hk hkc
    obtain ⟨q, hqR, hq1, hkq⟩ := hdec k hk
    have hq2B : q.2 ∈ B := by rw [hrect] at hqR; exact hqR.2
    have hq2 : q.2 = c := hinjH hq2B hc (by rw [← hkc, hkq, hhor_prod])
    exact ⟨q, hqR, hq2, hq1, by rw [hkq, hq2]⟩
  -- the higher group-Haar volume of `K` as the fiber-product lintegral of its indicator
  rw [← lintegral_indicator_one hKm0,
    ← setLIntegral_eq_of_support_subset (Set.support_indicator_subset.trans hKU), hBG r hr hr1]
  have hemb : MeasurableEmbedding (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1) :=
    (MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget _ p 1).measurableSet).comp
      h1.measurableEmbedding
  have hU1m : MeasurableSet U1 :=
    (isClosed_closedBall.preimage (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).continuous).measurableSet
  set A := (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1) ''
    (Subtype.val ⁻¹' U1) with hA
  have hAm : MeasurableSet A := hemb.measurableSet_image.mpr (measurable_subtype_coe hU1m)
  have hTW : Prod.map (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1) _root_.id ''
      (Prod.map Subtype.val _root_.id ⁻¹' R) = A ×ˢ B := by
    rw [hrect, preimage_prod_map_prod, prodMap_image_prod, image_id, preimage_id]
  set jL := (fixLastBlockMonoidHom n ℚ_[p]).comp mL with hjL
  have hjL_apply : ∀ h, jL h = fixLastBlockMatrix (mL h) := fun h ↦ rfl
  have hj : ∀ X' : skewAdjointPadicCayleySource W.pairingMatrix p,
      jL (h1 X').1 = fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p X'.1) :=
    fun X' ↦ by rw [hjL_apply, W.lastCayleyLowerChart_matrix p]
  set KM := mH '' (K : Set (specialFormPreservingMatrixSubgroup
    ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) with hKM
  have hmHc : Continuous mH :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKMc : IsClosed KM := (hKc.image hmHc).isClosed
  set P := (fun k ↦ fun j : Fin n ↦ (mH k *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) j.castSucc) ''
    (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) with hP
  have hPm : MeasurableSet P := by
    have hc : Continuous (fun k : specialFormPreservingMatrixSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
        fun j : Fin n ↦ (mH k *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) j.castSucc) :=
      continuous_pi fun j ↦ (continuous_apply (Fin.castSucc j)).comp
        (hmHc.matrix_mulVec (continuous_const (y := (lastCoordinateVector : Fin (n+1) → ℚ_[p]))))
    exact (hKc.image hc).isClosed.measurableSet
  have hPsub : P ⊆ hor '' B := by
    rintro y ⟨k, hk, rfl⟩
    obtain ⟨q, hqR, hq1, hkq⟩ := hdec k (hKU hk)
    have hq2B : q.2 ∈ B := by rw [hrect] at hqR; exact hqR.2
    refine ⟨q.2, hq2B, ?_⟩
    show hor q.2 = fun j ↦ (mH k *ᵥ (lastCoordinateVector : Fin (n+1) → ℚ_[p])) j.castSucc
    rw [hkq, hhor_prod]
  -- each fiber over the rectangle lies in the lower chart image
  have hFcA : ∀ c ∈ B, (fun h ↦ S (z + ∑ i, c i • v i) * jL h) ⁻¹' KM ⊆ A := by
    rintro c hc h ⟨k, hk, hke⟩
    obtain ⟨q, hqR, -, hq1, hkq⟩ := hcoef c hc k (hKU hk) (by rw [hke]; exact hhor_prod c _)
    have hunit : IsUnit (mH k) := Units.isUnit k.1.1
    rw [hke, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hunit
    have hS : IsUnit (S (z + ∑ i, c i • v i)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hunit)
    have heq : fixLastBlockMatrix (mL h) = fixLastBlockMatrix (mL (h1 ⟨q.1, hq1⟩).1) :=
      hS.mul_left_cancel (hke.symm.trans hkq)
    have hmeq : mL h = mL (h1 ⟨q.1, hq1⟩).1 := by
      have := congrArg upperLeftBlock heq
      simpa only [upperLeftBlock_fixLastBlockMatrix] using this
    have hh : h = (h1 ⟨q.1, hq1⟩).1 := specialFormPreservingMatrixHom_injective _ hmeq
    have hqU1 : q.1 ∈ U1 := by rw [hrect] at hqR; exact hqR.1
    rw [hh]
    exact ⟨⟨q.1, hq1⟩, hqU1, rfl⟩
  haveI : Measure.IsMulLeftInvariant (padicCayleySpecialOrthogonalDifferentialMeasure p n
      W.pairingMatrix W.form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isMulLeftInvariant p n W.pairingMatrix W.form_symm
      W.form_det_ne_zero
  haveI : SigmaFinite (padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix
      W.form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite p n W.pairingMatrix W.form_symm
      W.form_det_ne_zero
  set μL := padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
    with hμL
  -- the fiber over a coefficient is a left translate of `K ∩ H` or empty
  have hfib : ∀ c ∈ B, μL ((fun h ↦ S (z + ∑ i, c i • v i) * jL h) ⁻¹' KM) =
      μL (jL ⁻¹' KM) * P.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞) (hor c) := by
    intro c hc
    by_cases hcP : hor c ∈ P
    · obtain ⟨k, hk, hkc⟩ := id hcP
      obtain ⟨q, -, -, hq1, hkq⟩ := hcoef c hc k (hKU hk) hkc
      rw [Set.indicator_of_mem hcP, Pi.one_apply, mul_one]
      exact MeasureTheory.measure_translatedFiber_eq mH jL K _ μL
        (h₀ := (h1 ⟨q.1, hq1⟩).1) ⟨k, hk, hkq⟩
    · rw [Set.indicator_of_notMem hcP, mul_zero]
      have hempty : (fun h ↦ S (z + ∑ i, c i • v i) * jL h) ⁻¹' KM = ∅ := by
        ext h
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨k, hk, hke⟩
        exact hcP ⟨k, hk, by dsimp only; rw [hke]; exact hhor_prod c _⟩
      rw [hempty, measure_empty]
  -- the joint test set on the group rectangle, and its measurability
  set Q : Set (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) ×
      (Fin n → ℚ_[p])) :=
    {x | x ∈ A ×ˢ B ∧ S (z + ∑ i, x.2 i • v i) * jL x.1 ∈ KM} with hQ
  set Mq := fun q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p]) ↦
    S (z + ∑ i, q.2 i • v i) * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p q.1)
    with hMq
  have hMqc : ContinuousOn Mq R := by
    have hc0 : ContinuousOn (fun q ↦ padicCayleyForwardMatrix p
        ((W.lastCayleyProductFrameValue a ha p S z v q : skewAdjointMatricesLieSubalgebra
          ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
          Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])) R :=
      (continuousOn_padicCayleyForwardMatrix p).comp (continuous_subtype_val.comp_continuousOn hFVc)
        (fun q hq ↦ hsubsrc ⟨q, hq, rfl⟩)
    refine hc0.congr fun q hq ↦ ?_
    obtain ⟨hmat, -⟩ := hRpt q hq
    have h := hmat (hsubsrc ⟨q, hq, rfl⟩)
    rw [hmH, specialFormPreservingMatrixHom_apply,
      coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply] at h
    simp only [OneMemClass.coe_one, Units.val_one, one_mul] at h
    exact h.symm
  have hQs0 : IsClosed (R ∩ Mq ⁻¹' KM) :=
    hMqc.preimage_isClosed_of_isClosed (isClosed_closedBall.preimage eE.continuous) hKMc
  have hQeq : Q = Prod.map (fun X' : skewAdjointPadicCayleySource W.pairingMatrix p ↦ (h1 X').1)
      _root_.id '' (Prod.map Subtype.val _root_.id ⁻¹' (R ∩ Mq ⁻¹' KM)) := by
    ext x
    constructor
    · rintro ⟨⟨⟨X', hX'U1, hX'x⟩, hc⟩, hk⟩
      refine ⟨(X', x.2), ⟨?_, ?_⟩, ?_⟩
      · show ((X'.1, x.2) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
          (Fin n → ℚ_[p])) ∈ R
        rw [hrect]; exact ⟨hX'U1, hc⟩
      · show Mq (X'.1, x.2) ∈ KM
        have h' : Mq (X'.1, x.2) = S (z + ∑ i, x.2 i • v i) * jL x.1 := by
          rw [← hX'x, hj]
        rw [h']; exact hk
      · exact Prod.ext hX'x rfl
    · rintro ⟨⟨X', c⟩, ⟨hR', hk⟩, rfl⟩
      have hR'' : X'.1 ∈ U1 ∧ c ∈ B := by rw [hrect] at hR'; exact hR'
      refine ⟨⟨⟨X', hR''.1, rfl⟩, hR''.2⟩, ?_⟩
      show S (z + ∑ i, c i • v i) * jL (h1 X').1 ∈ KM
      rw [hj]; exact hk
  have hQm : MeasurableSet Q := by
    rw [hQeq]
    exact (hemb.prodMap MeasurableEmbedding.id).measurableSet_image.mpr
      ((measurable_subtype_coe.prodMap measurable_id) hQs0.measurableSet)
  -- the higher test read on the group rectangle is the joint indicator
  have hpt : ∀ x ∈ A ×ˢ B, W.lastCayleyProductLowerGroupTest p a ha S z v
      ((K : Set (specialFormPreservingMatrixSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))).indicator
        (1 : specialFormPreservingMatrixSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞)) x =
        Q.indicator (1 : specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) × (Fin n → ℚ_[p]) → ℝ≥0∞) x := by
    rintro ⟨x1, c⟩ ⟨⟨X', hX'U1, hX'eq⟩, hcB⟩
    simp only at hX'eq hcB
    subst hX'eq
    have hq : ((X'.1, c) : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])) ∈ R := by
      rw [hrect]; exact ⟨hX'U1, hcB⟩
    have hfsrc := hsubsrc ⟨_, hq, rfl⟩
    obtain ⟨hmat, -⟩ := hRpt _ hq
    have hmatX := hmat hfsrc
    have key : ∀ e, mH e = S (z + ∑ i, c i • v i) * jL (h1 X').1 →
        (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))).indicator
          (1 : specialFormPreservingMatrixSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞) e =
          Q.indicator (1 : specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) × (Fin n → ℚ_[p]) → ℝ≥0∞) ((h1 X').1, c) := by
      intro e he
      have hiff : e ∈ (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ↔
          ((h1 X').1, c) ∈ Q := by
        constructor
        · intro heK; exact ⟨⟨⟨X', hX'U1, rfl⟩, hcB⟩, ⟨e, heK, he⟩⟩
        · rintro ⟨-, k, hk, hke⟩
          rwa [specialFormPreservingMatrixHom_injective _ (hke.trans he.symm)] at hk
      by_cases he' : e ∈ (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))
      · simp only [Set.indicator_of_mem he', Set.indicator_of_mem (hiff.1 he'), Pi.one_apply]
      · rw [Set.indicator_of_notMem he', Set.indicator_of_notMem (mt hiff.2 he')]
    simp only [lastCayleyProductLowerGroupTest, dif_pos (h1 X').2, Subtype.coe_eta]
    rw [← hh1, Homeomorph.symm_apply_apply]
    simp only [lastCayleyChartPullback]
    rw [dif_pos hfsrc]
    exact key _ (by rw [hmatX, hj])
  -- slices of the joint set
  have hslice : ∀ c, μL ((fun h ↦ (h, c)) ⁻¹' Q) =
      B.indicator (fun c ↦ μL (jL ⁻¹' KM) * P.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞) (hor c)) c := by
    intro c
    by_cases hc : c ∈ B
    · rw [Set.indicator_of_mem hc, ← hfib c hc]
      congr 1
      ext h
      constructor
      · rintro ⟨-, hk⟩; exact hk
      · intro hk; exact ⟨⟨hFcA c hc hk, hc⟩, hk⟩
    · rw [Set.indicator_of_notMem hc]
      have hempty : (fun h ↦ (h, c)) ⁻¹' Q = ∅ := by
        ext h
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, hcB⟩, -⟩
        exact hc hcB
      rw [hempty, measure_empty]
  have hae : AEMeasurable (fun c ↦ P.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞) (hor c))
      ((Padic.unitHaar p (Fin n)).restrict B) :=
    (measurable_one.indicator hPm).comp_aemeasurable
      (hcontH.aemeasurable isClosed_closedBall.measurableSet)
  have hLr := hL r hr hr5 (P.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞))
  have hPvol : ∫⁻ y in lastCayleyHorizontalLower p S z v '' closedBall 0 r,
      P.indicator (1 : (Fin n → ℚ_[p]) → ℝ≥0∞) y ∂(Padic.unitHaar p (Fin n)) = Padic.unitHaar p (Fin n) P := by
    rw [lintegral_indicator_one hPm, Measure.restrict_apply hPm, Set.inter_eq_left.mpr hPsub]
  have final : ∀ g0 b t I L m : ℝ≥0∞, b * I = L * m → g0 * b * (t * I) = g0 * t * L * m := by
    intro g0 b t I L m h
    calc g0 * b * (t * I) = g0 * t * (b * I) := by ring
      _ = g0 * t * L * m := by rw [h]; ring
  rw [hTW, setLIntegral_congr_fun (hAm.prod isClosed_closedBall.measurableSet) hpt,
    lintegral_indicator_one hQm, Measure.restrict_apply hQm,
    Set.inter_eq_left.mpr (fun x hx ↦ hx.1), Measure.prod_apply_symm hQm, lintegral_congr hslice,
    lintegral_indicator isClosed_closedBall.measurableSet, lintegral_const_mul'' _ hae]
  exact final _ _ _ _ _ _ (hLr.trans (by rw [hPvol]))

end StabilizerVolume

end RationalQuadraticSpaceMatrix
