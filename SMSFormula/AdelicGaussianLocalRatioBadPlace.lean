import SMSFormula.AdelicGaussianLocalRatioStabilizer

/-!
# The bad-place local identity from the carrying property

Three local inputs of `localMass_mul_stabilizerScale_eq` are discharged:

* in every covering lattice atlas `glue_lat(ℤ_p^n) ∈ (0,∞)` once `M` has an integral `p`-adic
  representation (the tube law on a small open value set; the argument of
  `exists_localGlueRatio`, now atlas-free);
* the carrying property `E_v z ∈ T_R ⟺ z ∈ O'` of block shell points gives the lattice-shell trace
  `T_R ∩ {Q_lat = a} = E_v(O')`, hence `E_v⁻¹ T_R` carries `O'` on the block shell;
* the local scale `D_v = r · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))` is positive and finite (isometric
  transport of glue masses).

With the stabilizer identity through any carrying set in a fixed block atlas (its chart data
supplied), the bad-place identity `gR · D_v = gF · c_v` follows.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Metric Set PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance lrbpPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance lrbpPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- In every covering atlas the glue mass of `ℤ_p^N` at an integrally represented nonzero value is
positive and finite. -/
theorem padicSquareBranchAtlasGlue_integral_ne_zero_ne_top {N : ℕ} {p : ℕ} [Fact p.Prime]
    (G : Matrix (Fin N) (Fin N) ℚ_[p]) (point : ℕ → Fin N → ℚ_[p])
    (hpoint : ∀ i, G.toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((G.toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {w | G.toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (G.toQuadraticMap').padicSquareBranchAtlasRegion p point hpoint i)
    {value : ℚ_[p]} (hv0 : value ≠ 0) {u : Fin N → ℚ_[p]} (hu1 : ‖u‖ ≤ 1)
    (hu : G.toQuadraticMap' u = value) :
    (G.toQuadraticMap').padicSquareBranchAtlasGlue p point hpoint tH νs νv value
        {x | ‖x.val‖ ≤ 1} ≠ 0 ∧
      (G.toQuadraticMap').padicSquareBranchAtlasGlue p point hpoint tH νs νv value
        {x | ‖x.val‖ ≤ 1} ≠ ⊤ := by
  obtain ⟨B₀, hB₀o, hMB₀, hB₀⟩ :=
    (G.toQuadraticMap').exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul p
      point hpoint tH νs νv hcover value hv0
  set B := B₀ ∩ ball value 1
  have hBo : IsOpen B := hB₀o.inter isOpen_ball
  have hB := hB₀ B inter_subset_left hBo.measurableSet
  have hνB0 : νs B ≠ 0 := hBo.measure_ne_zero νs ⟨value, hMB₀, mem_ball_self one_pos⟩
  have hball : {vector : Fin N → ℚ_[p] | ‖vector‖ ≤ 1} = closedBall 0 1 := by
    ext w; simp [mem_closedBall, dist_zero_right]
  have hopen : IsOpen ({vector : Fin N → ℚ_[p] | ‖vector‖ ≤ 1} ∩ G.toQuadraticMap' ⁻¹' B) := by
    rw [hball]
    exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).inter
      (hBo.preimage (continuous_toQuadraticMap'_padic G))
  have hL0 : νv ({vector : Fin N → ℚ_[p] | ‖vector‖ ≤ 1} ∩ G.toQuadraticMap' ⁻¹' B) ≠ 0 :=
    hopen.measure_ne_zero νv ⟨u, hu1, show G.toQuadraticMap' u ∈ B from by
      rw [hu]; exact ⟨hMB₀, mem_ball_self one_pos⟩⟩
  have hLt : νv ({vector : Fin N → ℚ_[p] | ‖vector‖ ≤ 1} ∩ G.toQuadraticMap' ⁻¹' B) ≠ ⊤ := by
    refine ((measure_mono inter_subset_left).trans_lt ?_).ne
    rw [hball]
    exact (isCompact_closedBall 0 1).measure_lt_top
  refine ⟨fun h0 ↦ hL0 (by rw [hB, h0, zero_mul]), fun ht ↦ hLt (by rw [hB, ht,
    ENNReal.top_mul hνB0])⟩

/-- The carrying property gives the lattice-shell trace: if `E_v z ∈ T ⟺ z ∈ O'` for block shell
points, then `T ∩ {Q_lat = a} = E_v(O')`. -/
theorem inter_latticeShell_eq_image_of_carry (p : ℕ) [Fact p.Prime]
    {T : Set (Fin n → ℚ_[p])}
    {O' : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p])}
    (hcarry : ∀ z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p],
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 ∈ T ↔ z ∈ O') :
    T ∩ {w | (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = algebraMap ℚ ℚ_[p]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)} =
      (P.blockToAmbientPadicContinuousLinearEquiv hx p) '' (Subtype.val '' O') := by
  ext w
  constructor
  · rintro ⟨hwT, hwQ⟩
    set z₀ := (P.blockToAmbientPadicContinuousLinearEquiv hx p).symm w
    have hz₀ : ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z₀ = algebraMap ℚ ℚ_[p]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) := by
      rw [← latticeGram_blockToAmbient L P hx p, show (P.blockToAmbientPadicContinuousLinearEquiv hx p) z₀ = w from (P.blockToAmbientPadicContinuousLinearEquiv hx p).apply_symm_apply w]
      exact hwQ
    refine ⟨z₀, ⟨⟨z₀, hz₀⟩, (hcarry ⟨z₀, hz₀⟩).mp ?_, rfl⟩, (P.blockToAmbientPadicContinuousLinearEquiv hx p).apply_symm_apply w⟩
    change (P.blockToAmbientPadicContinuousLinearEquiv hx p) z₀ ∈ T
    rw [(P.blockToAmbientPadicContinuousLinearEquiv hx p).apply_symm_apply w]
    exact hwT
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(hcarry z).mpr hz, ?_⟩
    change (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') ((P.blockToAmbientPadicContinuousLinearEquiv hx p) z.1) = _
    rw [latticeGram_blockToAmbient L P hx p]
    exact z.2

/-- The local scale `D_v = r · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))` is positive and finite. -/
theorem localScale_ne_zero_ne_top (p : ℕ) [Fact p.Prime]
    (point₁ : ℕ → Fin (m + 1) → ℚ_[p]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) (point₁ i) ≠ 0)
    (tH₁ : ∀ i, Measure (((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (point₁ i))) [∀ i, (tH₁ i).IsAddHaarMeasure]
    (hcover₁ : {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point₁ hpoint₁ i)
    (point₂ : ℕ → Fin n → ℚ_[p]) (hpoint₂ : ∀ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') (point₂ i) ≠ 0)
    (tH₂ : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point₂ i))) [∀ i, (tH₂ i).IsAddHaarMeasure]
    (hcover₂ : {w | (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w ≠ 0} ⊆ ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion p point₂ hpoint₂ i)
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure]
    (μ₁ : Measure (Fin (m + 1) → ℚ_[p])) (μ₂ : Measure (Fin n → ℚ_[p]))
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] {value : ℚ_[p]} (hvalue : value ≠ 0)
    (hG0 : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue p point₂ hpoint₂ tH₂ νs μ₂ value {x | ‖x.1‖ ≤ 1} ≠ 0)
    (hGt : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue p point₂ hpoint₂ tH₂ νs μ₂ value {x | ‖x.1‖ ≤ 1} ≠ ⊤)
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    r * (νs (closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ tH₁ νs μ₁ value
        (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall 0 1))) ≠ 0 ∧
      r * (νs (closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ tH₁ νs μ₁ value
        (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall 0 1))) ≠ ⊤ := by
  obtain ⟨c, hc0, hct, hmap⟩ := QuadraticMap.exists_map_continuousLinearEquiv_eq_smul p (P.blockToAmbientPadicContinuousLinearEquiv hx p) μ₁ μ₂
  have hZc : IsCompact ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1) :=
    ((P.blockToAmbientPadicContinuousLinearEquiv hx p).toHomeomorph.isCompact_preimage (s := closedBall (0 : Fin n → ℚ_[p]) 1)).mpr
      (isCompact_closedBall _ _)
  have hZo : IsOpen ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1) :=
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage (P.blockToAmbientPadicContinuousLinearEquiv hx p).continuous
  have htr := QuadraticMap.padicSquareBranchAtlasGlue_linearIsometry p _ _ (P.blockToAmbientPadicContinuousLinearEquiv hx p)
    (latticeGram_blockToAmbient L P hx p) point₁ hpoint₁ tH₁ hcover₁ point₂ hpoint₂ tH₂ hcover₂
    νs μ₁ μ₂ hmap hvalue hZc hZo
  rw [Set.image_preimage_eq _ (P.blockToAmbientPadicContinuousLinearEquiv hx p).surjective] at htr
  have hball : (Subtype.val ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1 :
      Set {w : Fin n → ℚ_[p] // (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = value}) = {x | ‖x.1‖ ≤ 1} := by
    ext w; simp [mem_closedBall, dist_zero_right]
  rw [hball] at htr
  have hν0 : νs (closedBall (0 : ℚ_[p]) 1) ≠ 0 :=
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).measure_ne_zero νs
      ⟨0, mem_closedBall_self zero_le_one⟩
  have hνt : νs (closedBall (0 : ℚ_[p]) 1) ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  rw [htr]
  exact ⟨mul_ne_zero hr0 (mul_ne_zero hν0 (mul_ne_zero hc0 hG0)),
    ENNReal.mul_ne_top hrt (ENNReal.mul_ne_top hνt (ENNReal.mul_ne_top hct hGt))⟩

/-- The bad-place local identity from the carrying property: with the carrying property of `T_R`,
an integral representation of `M`, the local density identity and the stabilizer identity
through any carrying set in the block atlas, `gR · D_v = gF · c`. -/
theorem localMass_mul_stabilizerScale_eq_of_carry (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
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
    {O' : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p])}
    (hcarry : ∀ z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p],
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 ∈ PadicInt.restrictedIntegralVectors (e p) (R p) ↔ z ∈ O')
    (hMx : algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) = (((M : ℤ) : ℤ_[p]) : ℚ_[p]))
    {u : Fin n → ℚ_[p]} (hu1 : ‖u‖ ≤ 1) (hu : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') u = (((M : ℤ) : ℤ_[p]) : ℚ_[p]))
    {volV volW c r : ℝ≥0∞} (hdens : volV = volW * c)
    (hstab : ∀ T : Set (Fin (m + 1) → ℚ_[p]), MeasurableSet T →
      T ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z = (((M : ℤ) : ℤ_[p]) : ℚ_[p])} = Subtype.val '' O' →
      volV = r * volW * (νs (closedBall 0 1) *
        ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' T)))
    (hvolW0 : volW ≠ 0) (hvolWt : volW ≠ ⊤) :
    gR * (r * (νs (closedBall 0 1) *
      ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p])
        (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall 0 1)))) = gF * c := by
  have hG := padicSquareBranchAtlasGlue_integral_ne_zero_ne_top _ point₂ hpoint₂ tH₂ νs μ₂ hcover₂
    hM hu1 hu
  have htrace := inter_latticeShell_eq_image_of_carry L P hx p hcarry
  rw [hMx] at htrace
  have hsub : Subtype.val '' O' ⊆ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z = (((M : ℤ) : ℤ_[p]) : ℚ_[p])} := by
    rintro _ ⟨z, -, rfl⟩
    change ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z.1 = (((M : ℤ) : ℤ_[p]) : ℚ_[p])
    rw [← hMx]; exact z.2
  have hTblk := preimage_blockToAmbient_inter_shell L P hx p (((M : ℤ) : ℤ_[p]) : ℚ_[p]) hsub htrace
  have hmeas : MeasurableSet ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) :=
    ((PadicInt.isOpen_restrictedIntegralVectors _ _).preimage (P.blockToAmbientPadicContinuousLinearEquiv hx p).continuous).measurableSet
  exact localMass_mul_stabilizerScale_eq L P hx M Pr e R hPr hp hloc hFne hM point₂ hpoint₂ tH₂
    hcover₂ point₁ hpoint₁ tH₁ hcover₁ νs μ₁ μ₂ hG.1 hG.2 hdens (hstab _ hmeas hTblk) hvolW0 hvolWt

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
