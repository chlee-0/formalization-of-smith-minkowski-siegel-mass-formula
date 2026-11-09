import SMSFormula.AdelicGaussianPresentationGlueTransport

/-!
# The local count ratio as a block glue ratio

The local masses `(gF_p, gR_p)` of the replacement lemma are only characterized by the eventual
count identity `f(p^v) gF = F(p^v) gR`.  That identity determines the ratio: any two solutions
satisfy `gR · gF' = gR' · gF` (cancel a nonzero finite count).  The glue count identity makes
`(glue_lat(ℤ_p^n), glue_lat(T_R))` a solution for every covering lattice atlas, so

`gR · glue_lat(ℤ_p^n) = gF · glue_lat(T_R)`.

If a compact open block set `T_blk` is carried by the presentation onto `T_R` on the lattice shell,
the isometric transport of glue masses turns this into a purely block statement,

`gR · glue_block(E_v⁻¹ ℤ_p^n) = gF · glue_block(T_blk)`,

in which the Jacobian of `E_v` has cancelled.  Finally the stabilizer identity through a
carrying set, `vol_V(K) = |r| vol_W(e⁻¹K) (ν(ℤ_p) glue_block(T_blk))`, together with the local
density identity `vol_V(K) = vol_W(e⁻¹K) c_v` gives `c_v = |r| (ν(ℤ_p) glue_block(T_blk))`.
Nothing is chosen; all atlases and Haars are arbitrary.
-/

noncomputable section

open MeasureTheory Filter Metric PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

/-- The count identity determines the ratio: two eventual solutions of `f · a = F · b` with
eventually nonzero `F` satisfy `b · a' = b' · a`. -/
theorem ENNReal.mul_eq_mul_of_eventually_count_mul_eq {f F : ℕ → ℕ} {a b a' b' : ℝ≥0∞}
    (h : ∀ᶠ v : ℕ in atTop, (f v : ℝ≥0∞) * a = (F v : ℝ≥0∞) * b)
    (h' : ∀ᶠ v : ℕ in atTop, (f v : ℝ≥0∞) * a' = (F v : ℝ≥0∞) * b')
    (hF : ∀ᶠ v : ℕ in atTop, F v ≠ 0) : b * a' = b' * a := by
  obtain ⟨v, hv, hv', hFv⟩ := (h.and (h'.and hF)).exists
  have hF0 : (F v : ℝ≥0∞) ≠ 0 := by exact_mod_cast hFv
  have hFt : (F v : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine (ENNReal.mul_right_inj hF0 hFt).mp ?_
  calc (F v : ℝ≥0∞) * (b * a') = ((F v : ℝ≥0∞) * b) * a' := by ring
    _ = ((f v : ℝ≥0∞) * a) * a' := by rw [hv]
    _ = ((f v : ℝ≥0∞) * a') * a := by ring
    _ = ((F v : ℝ≥0∞) * b') * a := by rw [hv']
    _ = (F v : ℝ≥0∞) * (b' * a) := by ring

/-- The stabilizer identity determines the local density: from `vol_V = vol_W · c` and
`vol_V = r · vol_W · g` with `vol_W ∈ (0,∞)`, `c = r · g`. -/
theorem ENNReal.eq_mul_of_mul_eq_mul_mul {volV volW c r g : ℝ≥0∞} (hloc : volV = volW * c)
    (hcarry : volV = r * volW * g) (h0 : volW ≠ 0) (ht : volW ≠ ⊤) : c = r * g := by
  refine (ENNReal.mul_right_inj h0 ht).mp ?_
  rw [← hloc, hcarry]
  ring

/-- The local ratio against the local density: from `gR · bZ = gF · bT` and `c = r · (ν · bT)`,
`gR · (r · (ν · bZ)) = gF · c`. -/
theorem ENNReal.localRatio_mul_eq_of_blockGlue {gF gR bZ bT c r ν : ℝ≥0∞}
    (h : gR * bZ = gF * bT) (hc : c = r * (ν * bT)) : gR * (r * (ν * bZ)) = gF * c := by
  rw [hc]
  calc gR * (r * (ν * bZ)) = r * ν * (gR * bZ) := by ring
    _ = r * ν * (gF * bT) := by rw [h]
    _ = gF * (r * (ν * bT)) := by ring

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance lrbgPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance lrbgPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The local masses are lattice glue masses up to the common scalar: for every covering lattice
atlas, `gR · glue_lat(ℤ_p^n) = gF · glue_lat(T_R)`. -/
theorem localMass_mul_latticeGlue_eq (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
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
          p point hpoint i) :
    gR * (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
          p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} =
      (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
          p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p])
          (Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) * gF :=
  ENNReal.mul_eq_mul_of_eventually_count_mul_eq hloc
    (L.eventually_restrictedResidueCount_primePow_mul_glue_eq_of_eq M Pr e R hPr hp _ rfl _ rfl hM
      point hpoint tH νs νv hcover) hFne

/-- The local count ratio is a block glue ratio: if a compact open block set `T_blk` is carried by
`E_v` onto `T_R` on the lattice shell, then `gR · glue_block(E_v⁻¹ ℤ_p^n) = gF · glue_block(T_blk)`
for every block atlas, provided `glue_lat(ℤ_p^n) ∈ (0,∞)` in some lattice atlas. -/
theorem localMass_mul_blockGlue_eq (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
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
    {Tblk : Set (Fin (m + 1) → ℚ_[p])} (hTc : IsCompact Tblk) (hTo : IsOpen Tblk)
    (hslice : (Subtype.val ⁻¹' (P.blockToAmbientPadicContinuousLinearEquiv hx p '' Tblk) :
        Set {w : Fin n → ℚ_[p] // ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
          (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w =
            (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) =
      Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) :
    gR * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
        p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p])
        (Subtype.val ⁻¹' (P.blockToAmbientPadicContinuousLinearEquiv hx p ⁻¹' closedBall 0 1)) =
      gF * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
        p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' Tblk) := by
  set E := P.blockToAmbientPadicContinuousLinearEquiv hx p with hE
  set Zb := E ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1 with hZb
  have hZbc : IsCompact Zb :=
    (E.toHomeomorph.isCompact_preimage (s := closedBall (0 : Fin n → ℚ_[p]) 1)).mpr
      (isCompact_closedBall _ _)
  have hZbo : IsOpen Zb := (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage E.continuous
  have hEZ : E '' Zb = closedBall (0 : Fin n → ℚ_[p]) 1 := Set.image_preimage_eq _ E.surjective
  have hball : (Subtype.val ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1 :
      Set {w : Fin n → ℚ_[p] // ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w =
        (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) = {x | ‖x.1‖ ≤ 1} := by
    ext w
    change dist (w : Fin n → ℚ_[p]) (0 : Fin n → ℚ_[p]) ≤ 1 ↔
      ‖(w : Fin n → ℚ_[p])‖ ≤ 1
    rw [dist_zero_right]
  -- lattice identification
  have hlat := localMass_mul_latticeGlue_eq L M Pr e R hPr hp hloc hFne hM point₂ hpoint₂ tH₂ νs μ₂
    hcover₂
  -- isometric transport between T_blk and E⁻¹ℤ_p^n
  have hcross := blockGlue_mul_latticeGlue_eq L P hx p point₁ hpoint₁ tH₁ hcover₁ point₂ hpoint₂ tH₂
    hcover₂ νs μ₁ μ₂ hM hTc hTo hZbc hZbo
  rw [hEZ, hball, hslice] at hcross
  -- cancel glue_lat(ℤ_p^n)
  set GF := (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue p point₂ hpoint₂ tH₂ νs μ₂
    (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1}
  set GR := (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue p point₂ hpoint₂ tH₂ νs μ₂
    (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p))
  set bT := ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
    p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' Tblk)
  set bZ := ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue
    p point₁ hpoint₁ tH₁ νs μ₁ (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' Zb)
  -- hlat : gR * GF = gr * gF ; hcross : bT * GF = bZ * gr
  refine (ENNReal.mul_left_inj hG0 hGt).mp ?_
  calc gR * bZ * GF = bZ * (gR * GF) := by ring
    _ = bZ * (GR * gF) := by rw [hlat]
    _ = (bZ * GR) * gF := by ring
    _ = (bT * GF) * gF := by rw [hcross]
    _ = gF * bT * GF := by ring

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
