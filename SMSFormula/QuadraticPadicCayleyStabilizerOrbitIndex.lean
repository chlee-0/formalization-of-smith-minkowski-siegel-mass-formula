import SMSFormula.QuadraticPadicCayleyStabilizerGlobal

/-! Orbit-index form of the stabilizer volume identity. For `K'` normal in `K`,
`[K : K'] = [K ∩ H : K' ∩ H] · [K : K'(K ∩ H)]`, the last index read inside `K`.
Cancelling the finite nonzero `[K ∩ H : K' ∩ H]` in the index form gives, at the
identity-centred chart and for every compact open subgroup `K`,

`vol_G(K) = [K : K'(K ∩ H)] · |r| · vol_H(K ∩ H) · |(-1)^n/(2 a s)| · vol(K' · x_old)`,

where `[K : K'(K ∩ H)]` is the number of `K'`-orbits in `K · x_old`. Reading that
count times `vol(K' · x_old)` as the fiber mass of `K · x_old` uses the
fiber-measure covariance and is not asserted here. No chart, section, baseline
or Haar normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

/-- Index splitting through a trace: for `K' ≤ K` normal in `K` and any subgroup
`L`, `[K : K'] = [K ∩ L : K'] · [K : K'(K ∩ L)]`, the last index taken in `K`
(only normality of `K'` inside `K` is used). -/
theorem Subgroup.relIndex_eq_relIndex_inf_mul_index_sup {G : Type*} [Group G]
    {K K' L : Subgroup G} (hN : (K'.subgroupOf K).Normal) :
    K'.relIndex K =
      K'.relIndex (K ⊓ L) * ((K ⊓ L).subgroupOf K ⊔ K'.subgroupOf K).index := by
  have h1 := Subgroup.relIndex_mul_index (H := K'.subgroupOf K)
    (K := (K ⊓ L).subgroupOf K ⊔ K'.subgroupOf K) le_sup_right
  rw [Subgroup.relIndex, ← h1, Subgroup.relIndex_sup_right,
    Subgroup.relIndex_subgroupOf inf_le_left]

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section StabilizerOrbitIndex

variable (a : ℚ) (ha : a ≠ 0)

local instance soPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance soPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance soGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance soGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance soLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance soLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The trace index `[K ∩ H : K' ∩ H]`, read through the embedding, is the
relative index of `K'` in `K ∩ range ι`. -/
theorem relIndex_comap_lastFiberEmbedHom
    (K K' : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) :
    (K'.comap (W.lastFiberEmbedHom p a ha)).relIndex (K.comap (W.lastFiberEmbedHom p a ha)) =
      K'.relIndex (K ⊓ (W.lastFiberEmbedHom p a ha).range) := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_comm]

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
/-- Orbit-index form: at the identity-centred chart, for every compact open
subgroup `K` of the higher group and every sufficiently small exact rectangle
there is a compact open subgroup `K' ≤ K`, normal in `K`, inside the Cayley image,
with `vol_G(K) = [K : K'(K ∩ H)] · |r| · vol_H(K ∩ H) · |(-1)^n/(2 a s)| · vol(K' · x_old)`
and `[K : K'(K ∩ H)]` finite and nonzero. -/
theorem lastCayleyProduct_exists_forall_measure_compactOpen_orbitIndex
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
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) ⊆
          Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))) ∧
        (K'.subgroupOf K).Normal ∧
        ((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index ≠ 0 ∧
        padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
            (W.nonisotropicLastExtension a ha).pairingMatrix
            (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
          (((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index :
              ℝ≥0∞) *
            ((‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
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
  obtain ⟨δ, hδ, h⟩ := W.lastCayleyProduct_exists_forall_measure_compactOpen_index p a ha S dS z hSs
    hSO Y hY X hX hproduct v hs hv hbase K hKc hKo
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  obtain ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hfin, hfinL, heq⟩ := h r hr hrδ
  have hsplit := Subgroup.relIndex_eq_relIndex_inf_mul_index_sup
    (L := (W.lastFiberEmbedHom p a ha).range) hnorm
  rw [← W.relIndex_comap_lastFiberEmbedHom p a ha K K'] at hsplit
  have hm : ((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hsplit; exact hfin hsplit
  refine ⟨K', hle, hK'c, hK'o, hK'U, hnorm, hm, ?_⟩
  rw [hsplit, Nat.cast_mul, mul_assoc] at heq
  exact (ENNReal.mul_right_inj (Nat.cast_ne_zero.mpr hfinL) (ENNReal.natCast_ne_top _)).mp heq

end StabilizerOrbitIndex

end RationalQuadraticSpaceMatrix
