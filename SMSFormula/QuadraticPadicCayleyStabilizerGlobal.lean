import SMSFormula.QuadraticPadicCayleyStabilizerSubgroup

/-! Index form of the stabilizer volume identity for every compact open subgroup.
Left invariance alone splits a compact open subgroup into finitely many left
cosets of a finite-index open subgroup, so `vol(K) = [K : K'] · vol(K')`. At the
identity-centred chart, every compact open subgroup `K` of the higher group has
a finite-index open subgroup `K'`, normal in `K`, inside the small Cayley image;
the local stabilizer identity for `K'` and the counting on both groups give

`[K ∩ H : K' ∩ H] · vol_G(K) = [K : K'] · |r| · vol_H(K ∩ H) · |(-1)^n/(2 a s)| · vol(K' · x_old)`,

with `K ∩ H` the preimage under the fixed-last-coordinate embedding. The
quotient `[K : K'] / [K ∩ H : K' ∩ H] = [K : K'(K ∩ H)]` counts the `K'`-orbits in
`K · x_old`; identifying `[K : K'(K ∩ H)] · vol(K' · x_old)` with a Leray mass of
`K · x_old` needs invariance of the orbit measure and is not asserted. No chart,
section, baseline or Haar normalization is chosen; `K'` is obtained by
existence. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

/-- Coset counting: for a left-invariant measure, a subgroup is the disjoint union
of `[K : K']` left translates of a measurable finite-index subgroup `K' ≤ K`. -/
theorem MeasureTheory.measure_subgroup_eq_relIndex_mul {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {K K' : Subgroup G} (hle : K' ≤ K)
    (hfin : K'.relIndex K ≠ 0) (hK' : MeasurableSet (K' : Set G)) :
    μ K = (K'.relIndex K : ℝ≥0∞) * μ K' := by
  classical
  set L := K'.subgroupOf K with hL
  haveI : L.FiniteIndex := ⟨hfin⟩
  haveI : Finite (K ⧸ L) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (K ⧸ L)
  set S : K ⧸ L → Set G := fun q ↦ (fun g ↦ ((q.out : K) : G)⁻¹ * g) ⁻¹' (K' : Set G) with hS
  have hSK : ∀ q g, g ∈ S q → g ∈ K := by
    intro q g hg
    have : g = (q.out : G) * ((q.out : G)⁻¹ * g) := by group
    rw [this]
    exact K.mul_mem q.out.2 (hle hg)
  have hkey : ∀ (q : K ⧸ L) (g : G) (hg : g ∈ K),
      g ∈ S q ↔ (QuotientGroup.mk ⟨g, hg⟩ : K ⧸ L) = q := by
    intro q g hg
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hU : (K : Set G) = ⋃ q, S q := by
    ext g
    simp only [mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hg
      exact ⟨_, (hkey _ g hg).2 rfl⟩
    · rintro ⟨q, hq⟩
      exact hSK q g hq
  have hD : Pairwise (Function.onFun Disjoint S) := by
    intro q q' hne
    rw [Function.onFun, Set.disjoint_left]
    intro g h1 h2
    have hg := hSK q g h1
    exact hne (((hkey q g hg).1 h1).symm.trans ((hkey q' g hg).1 h2))
  have hSm : ∀ q, MeasurableSet (S q) := fun q ↦ (measurable_const_mul _) hK'
  have hSμ : ∀ q, μ (S q) = μ K' := fun q ↦ measure_preimage_mul μ _ _
  rw [hU, measure_iUnion hD hSm, tsum_fintype]
  simp only [hSμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/-- Normal finite-index open subgroups inside neighbourhoods: a compact open
subgroup `K` (of a topological group with a continuous injection into a totally
disconnected space) contains, inside every neighbourhood of `1`, a compact open
subgroup `K'`, normal in `K`, of finite index. -/
theorem IsTopologicalGroup.exists_normal_relIndex_subgroup_subset {G T : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace T] [TotallyDisconnectedSpace T]
    (f : G → T) (hf : Continuous f) (hfi : Function.Injective f) (K : Subgroup G)
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K' : Subgroup G, K' ≤ K ∧ IsCompact (K' : Set G) ∧ IsOpen (K' : Set G) ∧
      (K' : Set G) ⊆ U ∧ (K'.subgroupOf K).Normal ∧ K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : TotallyDisconnectedSpace K := by
    rw [totallyDisconnectedSpace_iff]
    exact isTotallyDisconnected_of_image (hf.comp continuous_subtype_val).continuousOn
      (hfi.comp Subtype.val_injective) (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨U', hU'U, hU'o, h1⟩ := mem_nhds_iff.mp hU
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hU'o.preimage continuous_subtype_val) (show ((1 : K) : G) ∈ U' from h1)
  have hsub : ((H.toOpenSubgroup : Subgroup K).map K.subtype).subgroupOf K =
      (H.toOpenSubgroup : Subgroup K) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨(H.toOpenSubgroup : Subgroup K).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [Subgroup.coe_map]
    exact (H.toOpenSubgroup.isClosed.isCompact).image continuous_subtype_val
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ H.toOpenSubgroup.isOpen
  · rw [Subgroup.coe_map]
    rintro _ ⟨h, hh, rfl⟩
    exact hU'U (hH hh)
  · rw [hsub]
    exact H.isNormal'
  · rw [Subgroup.relIndex, hsub]
    exact Subgroup.index_ne_zero_of_finite

/-- The block embedding is continuous on matrices. -/
theorem RationalQuadraticSpaceMatrix.continuous_fixLastBlockMatrix {n : ℕ} {R : Type*} [CommRing R]
    [TopologicalSpace R] :
    Continuous (RationalQuadraticSpaceMatrix.fixLastBlockMatrix :
      Matrix (Fin n) (Fin n) R → Matrix (Fin (n+1)) (Fin (n+1)) R) :=
  (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex
    _ _

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section StabilizerGlobal

variable (a : ℚ) (ha : a ≠ 0)

local instance sgPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance sgPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance sgGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance sgGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance sgLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance sgLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The fixed-last-coordinate group embedding, typed on the special
form-preserving carriers used by the repository group Haars. -/
def lastFiberEmbedHom :
    specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) →*
      specialFormPreservingMatrixSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) :=
  W.nonisotropicLastCoordinateFiberEmbedHom a ha ℚ_[p]

theorem specialFormPreservingMatrixHom_lastFiberEmbedHom
    (h : specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :
    specialFormPreservingMatrixHom
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))
        (W.lastFiberEmbedHom p a ha h) =
      fixLastBlockMatrix (specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) h) :=
  rfl

/-- `K ∩ H` read through the block matrix is the preimage of `K` under the
fixed-last-coordinate group embedding. -/
theorem fixLast_preimage_eq_comap_fiberEmbedHom
    (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) :
    (fun h ↦ fixLastBlockMatrix
        (specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) h)) ⁻¹'
      (specialFormPreservingMatrixHom
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ''
          (K : Set (specialFormPreservingMatrixSubgroup
            ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) =
      (K.comap (W.lastFiberEmbedHom p a ha) :
        Set (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])))) := by
  ext h
  simp only [mem_preimage, mem_image, SetLike.mem_coe, Subgroup.mem_comap]
  constructor
  · rintro ⟨k, hk, hke⟩
    have hk' : k = W.nonisotropicLastCoordinateFiberEmbedHom a ha ℚ_[p] h :=
      specialFormPreservingMatrixHom_injective _ hke
    rwa [hk'] at hk
  · intro hh
    exact ⟨_, hh, rfl⟩

/-- The preimage of a compact subgroup under the embedding is measurable. -/
theorem measurableSet_comap_fiberEmbedHom
    (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))
    (hKc : IsCompact (K : Set (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) :
    MeasurableSet (K.comap (W.lastFiberEmbedHom p a ha) :
      Set (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])))) := by
  rw [← W.fixLast_preimage_eq_comap_fiberEmbedHom p a ha K]
  have hmH : Continuous (specialFormPreservingMatrixHom
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hmL : Continuous (specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact ((hKc.image hmH).isClosed.preimage (continuous_fixLastBlockMatrix.comp hmL)).measurableSet

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

include hSs hSO hY hproduct hs hv in
/-- Index form of the stabilizer volume identity: at the identity-centred chart,
for every compact open subgroup `K` of the higher group and every sufficiently
small exact rectangle there is a compact open subgroup `K' ≤ K`, normal in
`K`, of finite index, inside the Cayley image, with finite-index trace on `H`, and
`[K ∩ H : K' ∩ H] · vol_G(K) = [K : K'] · |r| · vol_H(K ∩ H) · |(-1)^n/(2 a s)| · vol(K' · x_old)`. -/
theorem lastCayleyProduct_exists_forall_measure_compactOpen_index
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
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧
        IsOpen (K' : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧
        (K' : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ⊆
          Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))) ∧
        (K'.subgroupOf K).Normal ∧ K'.relIndex K ≠ 0 ∧
        (K'.comap (W.lastFiberEmbedHom p a ha)).relIndex
          (K.comap (W.lastFiberEmbedHom p a ha)) ≠ 0 ∧
        ((K'.comap (W.lastFiberEmbedHom p a ha)).relIndex
            (K.comap (W.lastFiberEmbedHom p a ha)) : ℝ≥0∞) *
            padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
          (K'.relIndex K : ℝ≥0∞) * ((‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
              (K.comap (W.lastFiberEmbedHom p a ha)) *
            (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
              ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
                lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) *
            Padic.unitHaar p (Fin n)
              ((fun k ↦ fun j ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K' : Set (specialFormPreservingMatrixSubgroup
                    ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))) := by
  obtain ⟨δ, hδ, hvol⟩ := W.lastCayleyProduct_exists_forall_measure_subgroup p a ha S dS z hSs hSO
    Y hY X hX hproduct v hs hv
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  have hU := W.lastCayleyProduct_image_mem_nhds p a ha S dS z hSs hSO Y hY X hX hproduct v hs hv hr
  rw [hbase] at hU
  have hc : Continuous (fun g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
        (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hc' : Continuous (fun (g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) (i j : Fin (n+1)) ↦
        (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) i j) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ hc.matrix_elem i j
  obtain ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hfin⟩ :=
    IsTopologicalGroup.exists_normal_relIndex_subgroup_subset _ hc'
      (fun g h e ↦ specialFormPreservingMatrixHom_injective _
        (Matrix.ext fun i j ↦ congrFun (congrFun e i) j)) K hKc hKo hU
  have hfinL := Subgroup.relIndex_comap_ne_zero (W.lastFiberEmbedHom p a ha) hfin
  refine ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hfin, hfinL, ?_⟩
  haveI : Measure.IsMulLeftInvariant (padicCayleySpecialOrthogonalDifferentialMeasure p n
      W.pairingMatrix W.form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isMulLeftInvariant p n W.pairingMatrix W.form_symm
      W.form_det_ne_zero
  haveI : Measure.IsMulLeftInvariant (padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix
      (W.nonisotropicLastExtension a ha).form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isMulLeftInvariant p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix (W.nonisotropicLastExtension a ha).form_symm
      (W.nonisotropicLastExtension a ha).form_det_ne_zero
  have hG := MeasureTheory.measure_subgroup_eq_relIndex_mul
    (padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix
      (W.nonisotropicLastExtension a ha).form_det_ne_zero) hle hfin hK'c.isClosed.measurableSet
  have hH := MeasureTheory.measure_subgroup_eq_relIndex_mul
    (padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero)
    (Subgroup.comap_mono hle) hfinL (W.measurableSet_comap_fiberEmbedHom p a ha K' hK'c)
  have hK' := hvol r hr hrδ K' hK'c hK'U
  rw [W.fixLast_preimage_eq_comap_fiberEmbedHom p a ha K'] at hK'
  rw [hG, hH, hK']
  ring

end StabilizerGlobal

end RationalQuadraticSpaceMatrix
