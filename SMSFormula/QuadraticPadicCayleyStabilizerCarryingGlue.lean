import SMSFormula.QuadraticPadicCayleyStabilizerAtlasGlueMass
import SMSFormula.RationalAdeleFiniteLocalReplacementOrbitBridge

/-!
# The stabilizer volume identity through a carrying set

The atlas-glue stabilizer identity expresses `vol_G(K)` through the glue of the orbit `K · x_old` in
a supplied atlas covering the orbit.  If a measurable ambient set `T` carries the orbit on the
shell, `T ∩ {Q = a} = K · x_old` (e.g. the restricted integral set of residue data,
`PadicQuadraticOrbitCarrierResidueData`), and a second supplied atlas covers all nonisotropic
vectors (the atlas of the replacement lemma), the two-atlas carrying identity rewrites the orbit
glue as the glue of `T` in the second atlas:

`vol_G(K) = |r| · vol_H(K ∩ H) · (ν(ℤ_p) · glue_a(T))`.

This is the local comparison `δ_{p,U_p} = κ_p⁻¹ · vol_G(t_p)/vol_H(t_p ∩ H)` in
the Cayley normalization, with the glue read in the replacement lemma's own atlas.  All chart,
atlas and Haar data are supplied; nothing is chosen.
-/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

local instance cgPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance cgPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance cgGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance cgGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance cgLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance cgLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
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

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

include hSs hSO hY hproduct hs hv in
/-- The stabilizer identity through a carrying set: with a supplied measurable `T` carrying the
orbit on the shell and a supplied atlas covering all nonisotropic vectors,
`vol_G(K) = |r| · vol_H(K ∩ H) · (ν(ℤ_p) · glue_a(T))` in that atlas. -/
theorem lastCayleyProduct_measure_compactOpen_eq_carryingGlue
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
        ⋃ i, Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p (pts i).1 (by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) (algebraMap ℚ ℚ_[p] a)))
    (point' : ℕ → Fin (n+1) → ℚ_[p])
    (hpoint' : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
      (point' i) ≠ 0)
    (tH' : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[p]).anisotropicOrthogonal (point' i))) [∀ i, (tH' i).IsAddHaarMeasure]
    (hcover' : {w | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
        w ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[p]).padicSquareBranchAtlasRegion p point' hpoint' i)
    {T : Set (Fin (n+1) → ℚ_[p])} (hT : MeasurableSet T)
    (hTO : T ∩ {w | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
        w = algebraMap ℚ ℚ_[p] a} =
      Subtype.val '' range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha)) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero K =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          (K.comap (W.lastFiberEmbedHom p a ha)) *
        (ν (closedBall 0 1) *
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
            ℚ_[p]).padicSquareBranchAtlasGlue p point' hpoint' tH' ν
            (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a) (Subtype.val ⁻¹' T)) := by
  have hvalue : algebraMap ℚ ℚ_[p] a ≠ 0 := (map_ne_zero _).mpr ha
  set orb := range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) with horb
  have hpre : (Subtype.val ⁻¹' (Subtype.val '' orb) :
      Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}) = orb :=
    Subtype.val_injective.preimage_image orb
  have hsliceT : (Subtype.val ⁻¹' T :
      Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}) = orb := by
    rw [← hpre]
    ext x
    simp only [mem_preimage]
    constructor
    · intro h
      rw [← hTO]
      exact ⟨h, x.2⟩
    · intro h
      rw [← hTO] at h
      exact h.1
  have hO : MeasurableSet (Subtype.val ⁻¹' (Subtype.val '' orb) :
      Set {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}) := by
    rw [hpre, ← hsliceT]
    exact hT.preimage measurable_subtype_coe
  have hg := QuadraticMap.padicSquareBranchAtlasGlue_carrying_eq p
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p])
    point' hpoint' tH' hcover' (fun i ↦ (pts i).1)
    (fun i ↦ by rw [(pts i).2]; exact hvalue) tH ν (Padic.unitHaar p (Fin (n+1))) hvalue hTO hO
    (by rw [hpre]; exact hcover)
  rw [hpre] at hg
  rw [hg]
  exact W.lastCayleyProduct_measure_compactOpen_eq_atlasGlue p a ha S dS z hSs hSO Y hY X hX
    hproduct v hs hv ν hbase K hKc hKo pts tH hcover

end RationalQuadraticSpaceMatrix
