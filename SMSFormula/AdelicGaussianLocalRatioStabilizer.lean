import SMSFormula.AdelicGaussianLocalRatioBlockGlue

/-!
# The local count ratio against the local density

Take the block carrying set to be the presentation preimage `T_blk = E_v⁻¹ T_R` of the lattice
residue set.  It is compact open, its presentation image is `T_R`, and it carries on the block
shell exactly the block set whose image `T_R` carries on the lattice shell.  Combining the block
glue identity of the local masses with the stabilizer identity through a carrying set (taken
in the form it is produced, `vol_V(K) = |r| · vol_W(e⁻¹K) · (ν(ℤ_p) · glue_block(T_blk))`) and the
local density identity `vol_V(K) = vol_W(e⁻¹K) · c_v` gives

`gR · (|r| · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))) = gF · c_v`,

i.e. `gR/gF = c_v / (|r| ν(ℤ_p) glue_block(E_v⁻¹ ℤ_p^n))`.  The chart
data of the stabilizer identity remain supplied; nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Metric PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance lrsPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance lrsPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The presentation preimage carries the block orbit: if `T ∩ {Q_lat = a} = E_v '' O` with `O` in
the block shell, then `E_v⁻¹ T ∩ {Q_block = a} = O`. -/
theorem preimage_blockToAmbient_inter_shell (p : ℕ) [Fact p.Prime] (value : ℚ_[p])
    {T : Set (Fin n → ℚ_[p])} {O : Set (Fin (m + 1) → ℚ_[p])}
    (hO : O ⊆ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z = value})
    (hT : T ∩ {w | (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = value} = (P.blockToAmbientPadicContinuousLinearEquiv hx p) '' O) :
    (P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' T ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z = value} = O := by
  ext z
  constructor
  · rintro ⟨hz, hzv⟩
    have hmem : (P.blockToAmbientPadicContinuousLinearEquiv hx p) z ∈ T ∩ {w | (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = value} :=
      ⟨hz, by change (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') ((P.blockToAmbientPadicContinuousLinearEquiv hx p) z) = value; rw [latticeGram_blockToAmbient L P hx p]; exact hzv⟩
    rw [hT] at hmem
    obtain ⟨z', hz', hzz⟩ := hmem
    rwa [← (P.blockToAmbientPadicContinuousLinearEquiv hx p).injective hzz]
  · intro hz
    have hmem : (P.blockToAmbientPadicContinuousLinearEquiv hx p) z ∈ (P.blockToAmbientPadicContinuousLinearEquiv hx p) '' O := ⟨z, hz, rfl⟩
    rw [← hT] at hmem
    exact ⟨hmem.1, hO hz⟩

/-- The local count ratio against the local density at a bad place: with `T_blk = E_v⁻¹ T_R`,
the stabilizer identity `vol_V(K) = r · vol_W(e⁻¹K) · (ν(ℤ_p) · glue_block(T_blk))` and the
local density identity `vol_V(K) = vol_W(e⁻¹K) · c` (with `vol_W(e⁻¹K) ∈ (0,∞)`),
`gR · (r · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))) = gF · c`. -/
theorem localMass_mul_stabilizerScale_eq (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ Pr) {gF gR : ℝ≥0∞}
    (hloc : ∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF =
      (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR)
    (hFne : ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0)
    (hM : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0)
    (point₂ : ℕ → Fin n → ℚ_[p])
    (hpoint₂ : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point₂ i) ≠ 0)
    (tH₂ : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point₂ i)))
    [∀ i, (tH₂ i).IsAddHaarMeasure]
    (hcover₂ : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point₂ hpoint₂ i)
    (point₁ : ℕ → Fin (m + 1) → ℚ_[p])
    (hpoint₁ : ∀ i, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] (point₁ i) ≠ 0)
    (tH₁ : ∀ i, Measure (((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[p]).anisotropicOrthogonal (point₁ i))) [∀ i, (tH₁ i).IsAddHaarMeasure]
    (hcover₁ : {w | (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] w ≠ 0} ⊆
      ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion
        p point₁ hpoint₁ i)
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure]
    (μ₁ : Measure (Fin (m + 1) → ℚ_[p])) (μ₂ : Measure (Fin n → ℚ_[p]))
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]
    (hG0 : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
          p point₂ hpoint₂ tH₂ νs μ₂ (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} ≠ 0)
    (hGt : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
          p point₂ hpoint₂ tH₂ νs μ₂ (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} ≠ ⊤)
    {volV volW c r : ℝ≥0∞} (hdens : volV = volW * c)
    (hstab : volV = r * volW * (νs (closedBall 0 1) *
      ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p])
        (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)))))
    (hvolW0 : volW ≠ 0) (hvolWt : volW ≠ ⊤) :
    gR * (r * (νs (closedBall 0 1) *
      ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p])
        (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall 0 1)))) = gF * c := by
  have hTc : IsCompact ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) :=
    ((P.blockToAmbientPadicContinuousLinearEquiv hx p).toHomeomorph.isCompact_preimage (s := PadicInt.restrictedIntegralVectors (e p) (R p))).mpr (PadicInt.isCompact_restrictedIntegralVectors _ _)
  have hTo : IsOpen ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) :=
    (PadicInt.isOpen_restrictedIntegralVectors _ _).preimage (P.blockToAmbientPadicContinuousLinearEquiv hx p).continuous
  have hslice : (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) '' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p))) :
      Set {w : Fin n → ℚ_[p] // (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) = Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p) := by
    rw [Set.image_preimage_eq _ (P.blockToAmbientPadicContinuousLinearEquiv hx p).surjective]
  have hblk := localMass_mul_blockGlue_eq L P hx M Pr e R hPr hp hloc hFne hM point₂ hpoint₂ tH₂
    hcover₂ point₁ hpoint₁ tH₁ hcover₁ νs μ₁ μ₂ hG0 hGt hTc hTo hslice
  exact ENNReal.localRatio_mul_eq_of_blockGlue hblk
    (ENNReal.eq_mul_of_mul_eq_mul_mul hdens hstab hvolW0 hvolWt)

/-- At a place where the residue set carries the whole integral shell the local masses agree:
if `T_R` and `ℤ_p^n` have the same trace on the lattice shell and `glue_lat(ℤ_p^n) ∈ (0,∞)`,
then `gR = gF`. -/
theorem localMass_eq_of_slice_eq_integral (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ Pr) {gF gR : ℝ≥0∞}
    (hloc : ∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF =
      (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR)
    (hFne : ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0)
    (hM : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0)
    (point : ℕ → Fin n → ℚ_[p])
    (hpoint : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin n → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point hpoint i)
    (hG0 : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
          p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} ≠ 0)
    (hGt : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
          p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} ≠ ⊤)
    (hslice : (Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p) :
        Set {w : Fin n → ℚ_[p] // (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) = {x | ‖x.1‖ ≤ 1}) :
    gR = gF := by
  have h := localMass_mul_latticeGlue_eq L M Pr e R hPr hp hloc hFne hM point hpoint tH νs νv hcover
  rw [hslice, mul_comm _ gF] at h
  exact (ENNReal.mul_left_inj hG0 hGt).mp h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
