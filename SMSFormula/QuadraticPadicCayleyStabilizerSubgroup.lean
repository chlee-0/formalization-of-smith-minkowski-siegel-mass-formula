import SMSFormula.QuadraticPadicCayleyStabilizerVolume
import SMSFormula.RationalCliffordGeneralSpinPadicIntegralCoordinates
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! Compact open subgroups inside small Cayley images. The Cayley image of the
actual product on every exact coordinate rectangle around `(Y, 0)` is a
neighbourhood of the base point `Cayley(X)` (the frame map has an invertible
strict derivative, so it is open at `(Y, 0)` by mathlib's inverse function
theorem over `ℚ_p`). Inside the compact open integral subgroup, a
profinite group, every neighbourhood of `1` contains an open subgroup (mathlib's
profinite van Dantzig lemma), so when the base point is `1` every such image
contains a compact open subgroup, and the local stabilizer volume identity has
non-vacuous instances. No chart, section, baseline or Haar normalization is
chosen; the subgroup is obtained by existence, not selected. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

/-- Van Dantzig inside a supplied compact open subgroup: in a topological group
with a compact open subgroup `C` and a continuous injective map into a totally
disconnected space, every neighbourhood of `1` contains a compact open
subgroup. -/
theorem IsTopologicalGroup.exists_isCompact_isOpen_subgroup_subset {G T : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace T] [TotallyDisconnectedSpace T]
    (f : G → T) (hf : Continuous f) (hfi : Function.Injective f) (C : Subgroup G)
    (hCc : IsCompact (C : Set G)) (hCo : IsOpen (C : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (K : Set G) ⊆ U := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  haveI : TotallyDisconnectedSpace C := by
    rw [totallyDisconnectedSpace_iff]
    exact isTotallyDisconnected_of_image (hf.comp continuous_subtype_val).continuousOn
      (hfi.comp Subtype.val_injective) (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨U', hU'U, hU'o, h1⟩ := mem_nhds_iff.mp hU
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hU'o.preimage continuous_subtype_val) (show ((1 : C) : G) ∈ U' from h1)
  refine ⟨(H.toOpenSubgroup : Subgroup C).map C.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact (H.toOpenSubgroup.isClosed.isCompact).image continuous_subtype_val
  · rw [Subgroup.coe_map]
    exact hCo.isOpenMap_subtype_val _ H.toOpenSubgroup.isOpen
  · rw [Subgroup.coe_map]
    rintro _ ⟨h, hh, rfl⟩
    exact hU'U (hH hh)

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section StabilizerSubgroup

variable (a : ℚ) (ha : a ≠ 0)

local instance stabilizerLowerSkewIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

local instance stabilizerHigherSkewIsTopologicalAddGroup :
    IsTopologicalAddGroup
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  Submodule.topologicalAddGroup _

local instance stabilizerLowerSkewIsUniformAddGroup :
    IsUniformAddGroup
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  IsUniformAddGroup.comap
    (skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule.subtype.toAddMonoidHom

local instance stabilizerHigherSkewIsUniformAddGroup :
    IsUniformAddGroup
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  IsUniformAddGroup.comap
    (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule.subtype.toAddMonoidHom

local instance stabilizerLowerSkewContinuousSMul :
    ContinuousSMul ℚ_[p]
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  continuousSMul_induced
    (skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule.subtype

local instance stabilizerHigherSkewContinuousSMul :
    ContinuousSMul ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  continuousSMul_induced
    (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])).toSubmodule.subtype

/-- The compact open integral subgroup, read on the higher special
form-preserving group, makes every neighbourhood of `1` contain a compact open
subgroup. -/
theorem exists_isCompact_isOpen_subgroup_subset_of_mem_nhds_one
    (V : RationalQuadraticSpaceMatrix n)
    {U : Set (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])))}
    (hU : U ∈ 𝓝 (1 : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])))) :
    ∃ K : Subgroup (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))),
      IsCompact (K : Set (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧ IsOpen (K : Set (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧
        (K : Set (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ⊆ U := by
  haveI : IsTopologicalGroup
      (formPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    Topology.IsInducing.subtypeVal.topologicalGroup
      (formPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).subtype
  have hgroup : IsTopologicalGroup
      (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    Topology.IsInducing.subtypeVal.topologicalGroup
      (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).subtype
  have hc : Continuous (fun g : specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦ (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hc' : Continuous (fun (g : specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) (i j : Fin n) ↦
        (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ hc.matrix_elem i j
  exact @IsTopologicalGroup.exists_isCompact_isOpen_subgroup_subset
    (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℚ_[p])))
    (Fin n → Fin n → ℚ_[p]) _ _ hgroup _ _ _ hc'
    (fun g h e ↦ specialFormPreservingMatrixHom_injective _
      (Matrix.ext fun i j ↦ congrFun (congrFun e i) j))
    (V.padicSpecialOrthogonalIntegralSubgroup p)
    (V.isCompact_padicSpecialOrthogonalIntegralSubgroup p)
    (V.isOpen_padicSpecialOrthogonalIntegralSubgroup p) U hU

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

/-- At the Lie origin the identity-translated higher Cayley chart is the
identity of the group. -/
theorem lastCayleyHigherChart_eq_one_of_eq_zero
    (hX0 : ((X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
        Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) = 0) :
    (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1 := by
  apply specialFormPreservingMatrixHom_injective
  rw [map_one, specialFormPreservingMatrixHom_apply,
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
  change (1 : specialFormPreservingMatrixSubgroup _).1.1.1 *
    ((1 + (X : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])) *
      (1 - (X : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]))⁻¹) = 1
  rw [hX0]
  simp

set_option backward.isDefEq.respectTransparency false in
include hSs hSO hY hproduct hs hv in
/-- The Cayley image of every exact rectangle is a neighbourhood of the
base point `Cayley(X)` in the higher group. -/
theorem lastCayleyProduct_image_mem_nhds {r : ℝ} (hr : 0 < r) :
    Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
      (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
        ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
          closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))) ∈
      𝓝 ((skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1) := by
  haveI : CompleteSpace
      (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
        (Fin n → ℚ_[p])) := FiniteDimensional.complete ℚ_[p] _
  haveI : CompleteSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
    FiniteDimensional.complete ℚ_[p] _
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  obtain ⟨e, -, he, heX, -, -⟩ := W.lastCayleyProduct_exists_localInverse a ha p S dS z hSs hSO Y hY
    X hX hproduct v hs hv
  have hbase : W.lastCayleyProductFrameValue a ha p S z v (Y,0) = X := by rw [← he]; exact heX
  have hf := W.hasStrictFDerivAt_lastCayleyProductFrameValue_equiv a ha p S dS z hSs hSO Y hY X hX
    hproduct v hs hv
  have hR : eE ⁻¹' closedBall (eE (Y,0)) r ∈ 𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])) :=
    eE.continuous.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hr)
  have hFV : W.lastCayleyProductFrameValue a ha p S z v '' (eE ⁻¹' closedBall (eE (Y,0)) r) ∈ 𝓝 X := by
    rw [← hbase, ← hf.map_nhds_eq_of_equiv]
    exact image_mem_map hR
  have hsrc : Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
      (eE ⁻¹' closedBall (eE (Y,0)) r)) ∈
      𝓝 (⟨X, hX⟩ : skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hFV
  have htgt := (skewAdjointPadicCayleyTranslatedHomeomorph
    (W.nonisotropicLastExtension a ha).pairingMatrix p
    (W.nonisotropicLastExtension a ha).form_det_ne_zero 1).isOpenMap.image_mem_nhds hsrc
  exact (isOpen_padicCayleySpecialOrthogonalTranslatedTarget _ p 1).isOpenMap_subtype_val.image_mem_nhds
    htgt

include hSs hSO hY hproduct hs hv in
/-- Non-vacuity of the local stabilizer volume identity: when the base point
`Cayley(X)` is the identity, every sufficiently small exact rectangle has a
compact open subgroup `K` inside its Cayley image, and for it
`vol_G(K) = |r| · vol_H(K ∩ H) · |(-1)^n/(2 a s)| · vol(K · x_old)`. -/
theorem lastCayleyProduct_exists_forall_exists_measure_subgroup
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∃ K : Subgroup (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))),
        IsCompact (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧ IsOpen (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ∧
        (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ⊆ Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))) ∧
        padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
            (W.nonisotropicLastExtension a ha).pairingMatrix
            (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
              ((fun h ↦ fixLastBlockMatrix
                  (specialFormPreservingMatrixHom (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) h)) ⁻¹'
                (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ''
                    (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))))) *
            (‖((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
              ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
                lastCoordinateVector) (Fin.last n)))‖₊ : ℝ≥0∞) *
            Padic.unitHaar p (Fin n)
              ((fun k ↦ fun j ↦ (specialFormPreservingMatrixHom
                  ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) k *ᵥ
                  lastCoordinateVector) j.castSucc) '' (K : Set (specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))))) := by
  obtain ⟨δ, hδ, hvol⟩ := W.lastCayleyProduct_exists_forall_measure_subgroup p a ha S dS z hSs hSO
    Y hY X hX hproduct v hs hv
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  have hU := W.lastCayleyProduct_image_mem_nhds p a ha S dS z hSs hSO Y hY X hX hproduct v hs hv hr
  rw [hbase] at hU
  obtain ⟨K, hKc, hKo, hKU⟩ := exists_isCompact_isOpen_subgroup_subset_of_mem_nhds_one p
    (W.nonisotropicLastExtension a ha) hU
  exact ⟨K, hKc, hKo, hKU, hvol r hr hrδ K hKc hKU⟩

end StabilizerSubgroup

end RationalQuadraticSpaceMatrix
