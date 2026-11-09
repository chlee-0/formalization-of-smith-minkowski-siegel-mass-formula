import SMSFormula.RationalAdeleFiniteLocalReplacementOrbitBridge
import SMSFormula.QuadraticPadicSquareBranchAtlasGlueScalar

/-!
# The local count ratios of the replacement lemma exist

The replacement lemma consumed supplied masses `gF_p, gR_p` with
`f(p^v) · gF_p = F(p^v) · gR_p` eventually, `gF_p ∈ (0, ∞)` and `F(p^v) ≠ 0` eventually.  Here
they are produced.  At a prime `p` where the value `M ≠ 0` has an integral `p`-adic
representation `Q(u) = M`, `‖u‖ ≤ 1`:

* a covering atlas of the nonisotropic vectors exists (countable atlas existence), with the
  auxiliary Haars;
* the tube law `vol(ℤ_p^n ∩ Q⁻¹B) = glue_M(X_M(ℤ_p)) · ν(B)` on a small open `B ∋ M` shows
  `gF_p = glue_M(ℤ_p^n)` is positive (the left side contains the open neighbourhood of `u`) and
  finite (the left side is bounded by the mass of `ℤ_p^n`);
* the glue count ratio gives the eventual identity with `gR_p = glue_M(T_{R_p})`, and the
  nonvanishing gives `F(p^v) ≠ 0` eventually.

The ratio `gR_p/gF_p` is intrinsic (it is the eventual ratio of restricted to full counts), so the
existential form loses nothing; the atlas enters only inside the proof.  Consequently the
replacement lemma holds with no supplied masses:
`d_fin(1_{U_R})(M) = κ · d_fin(1_Ẑ)(M)` with `κ = ∏ gR_p / ∏ gF_p`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Matrix Set RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance grPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance grPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- A matrix quadratic map over `ℚ_p` is continuous. -/
theorem continuous_toQuadraticMap'_padic {p : ℕ} [Fact p.Prime] (G : Matrix (Fin n) (Fin n) ℚ_[p]) :
    Continuous (G.toQuadraticMap') := by
  have h : ∀ v, G.toQuadraticMap' v = v ⬝ᵥ (G *ᵥ v) := fun v ↦ by
    simp [Matrix.toQuadraticMap', Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  rw [show ⇑(G.toQuadraticMap') = fun v ↦ v ⬝ᵥ (G *ᵥ v) from funext h]
  unfold dotProduct Matrix.mulVec dotProduct
  fun_prop

/-- The local masses exist at a prime where `M` is integrally represented. -/
theorem exists_localGlueRatio (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (hM : M ≠ 0) (P : Finset ℕ)
    (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    {p : ℕ} [Fact p.Prime] (hpP : p ∈ P)
    (hrep : ∃ u : Fin n → ℚ_[p], ‖u‖ ≤ 1 ∧
      ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u = (((M : ℤ) : ℤ_[p]) : ℚ_[p])) :
    ∃ gF gR : ℝ≥0∞, gF ≠ 0 ∧ gF ≠ ⊤ ∧
      (∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR) ∧
      ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0 := by
  set G := (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) with hG
  set Q := G.toQuadraticMap' with hQ
  set value : ℚ_[p] := (((M : ℤ) : ℤ_[p]) : ℚ_[p]) with hvalue
  have hv0 : value ≠ 0 := by rw [hvalue, PadicInt.coe_intCast]; exact_mod_cast hM
  obtain ⟨u, hu1, hu⟩ := hrep
  obtain ⟨point, hpoint, hcover⟩ := Q.exists_padicSquareBranchAtlas_cover p
    ⟨u, by rw [hu]; exact hv0⟩
  let tH : ∀ i, Measure (Q.anisotropicOrthogonal (point i)) := fun _ ↦ Measure.addHaar
  haveI : ∀ i, (tH i).IsAddHaarMeasure := fun _ ↦ by simp only [tH]; infer_instance
  let νs : Measure ℚ_[p] := Measure.addHaar
  let νv : Measure (Fin n → ℚ_[p]) := Measure.addHaar
  obtain ⟨B₀, hB₀o, hMB₀, hB₀⟩ := Q.exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul p
    point hpoint tH νs νv hcover value hv0
  set gF := Q.padicSquareBranchAtlasGlue p point hpoint tH νs νv value {x | ‖x.val‖ ≤ 1} with hgF
  let B := B₀ ∩ ball value 1
  have hBo : IsOpen B := hB₀o.inter isOpen_ball
  have hBm : MeasurableSet B := hBo.measurableSet
  have hB := hB₀ B inter_subset_left hBm
  have hνB0 : νs B ≠ 0 := hBo.measure_ne_zero νs ⟨value, hMB₀, mem_ball_self one_pos⟩
  have hνBt : νs B ≠ ⊤ :=
    ((measure_mono (inter_subset_right.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall value 1).measure_lt_top).ne
  have hopen : IsOpen ({vector : Fin n → ℚ_[p] | ‖vector‖ ≤ 1} ∩ Q ⁻¹' B) := by
    refine IsOpen.inter ?_ (hBo.preimage (continuous_toQuadraticMap'_padic G))
    have : {vector : Fin n → ℚ_[p] | ‖vector‖ ≤ 1} = closedBall 0 1 := by
      ext w; simp [mem_closedBall, dist_zero_right]
    rw [this]
    exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hL0 : νv ({vector : Fin n → ℚ_[p] | ‖vector‖ ≤ 1} ∩ Q ⁻¹' B) ≠ 0 :=
    hopen.measure_ne_zero νv ⟨u, hu1, show Q u ∈ B from by
      rw [show Q u = value from hu]; exact ⟨hMB₀, mem_ball_self one_pos⟩⟩
  have hLt : νv ({vector : Fin n → ℚ_[p] | ‖vector‖ ≤ 1} ∩ Q ⁻¹' B) ≠ ⊤ := by
    refine ((measure_mono inter_subset_left).trans_lt ?_).ne
    have : {vector : Fin n → ℚ_[p] | ‖vector‖ ≤ 1} = closedBall 0 1 := by
      ext w; simp [mem_closedBall, dist_zero_right]
    rw [this]
    exact (isCompact_closedBall 0 1).measure_lt_top
  have hgF0 : gF ≠ 0 := by
    intro h0
    apply hL0
    rw [hB, h0, zero_mul]
  have hgFt : gF ≠ ⊤ := by
    intro ht
    apply hLt
    rw [hB, ht, ENNReal.top_mul hνB0]
  refine ⟨gF, Q.padicSquareBranchAtlasGlue p point hpoint tH νs νv value
      (Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)), hgF0, hgFt, ?_, ?_⟩
  · exact L.eventually_restrictedResidueCount_primePow_mul_glue_eq_of_eq M P e R hP hpP G hG.symm
      value hvalue.symm hv0 point hpoint tH νs νv hcover
  · exact L.eventually_fullResidueCount_primePow_ne_zero_of_eq M G hG.symm value hvalue.symm hv0
      point hpoint tH νs νv hcover hgF0

/-- The local masses exist as a prime-indexed family when `M` is integrally represented at every
prime of `P`. -/
theorem exists_localGlueRatio_family (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (hM : M ≠ 0) (P : Finset ℕ)
    (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (hrep : ∀ p (hp : p ∈ P), haveI : Fact p.Prime := ⟨(hP p hp).1⟩;
      ∃ u : Fin n → ℚ_[p], ‖u‖ ≤ 1 ∧
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
          (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u =
            (((M : ℤ) : ℤ_[p]) : ℚ_[p])) :
    ∃ gF gR : ℕ → ℝ≥0∞, (∀ p ∈ P, gF p ≠ 0) ∧ (∀ p ∈ P, gF p ≠ ⊤) ∧
      (∀ p ∈ P, ∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0 := by
  have h : ∀ p : ℕ, ∃ gF gR : ℝ≥0∞, p ∈ P → gF ≠ 0 ∧ gF ≠ ⊤ ∧
      (∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR) ∧
      ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0 := by
    intro p
    by_cases hp : p ∈ P
    · haveI : Fact p.Prime := ⟨(hP p hp).1⟩
      obtain ⟨gF, gR, h1, h2, h3, h4⟩ := L.exists_localGlueRatio M hM P e R hP hp (hrep p hp)
      exact ⟨gF, gR, fun _ ↦ ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, 1, fun h ↦ (hp h).elim⟩
  choose gF gR hg using h
  exact ⟨gF, gR, fun p hp ↦ (hg p hp).1, fun p hp ↦ (hg p hp).2.1, fun p hp ↦ (hg p hp).2.2.1,
    fun p hp ↦ (hg p hp).2.2.2⟩

/-- The replacement lemma with no supplied masses: above rank four, if `M ≠ 0` is integrally
represented at every prime of `P`, then there exist local masses (intrinsically, eventual count
ratios) with `d_fin(1_{U_R})(M) = (∏ gR/∏ gF) · d_fin(1_Ẑ)(M)` and `gF_p ∈ (0, ∞)`. -/
theorem exists_finiteLocalValueDensity_localRestriction_eq_mul (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) (M : ℤ) (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (hrep : ∀ p (hp : p ∈ P), haveI : Fact p.Prime := ⟨(hP p hp).1⟩;
      ∃ u : Fin n → ℚ_[p], ‖u‖ ≤ 1 ∧
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
          (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u =
            (((M : ℤ) : ℤ_[p]) : ℚ_[p])) :
    ∃ gF gR : ℕ → ℝ≥0∞, (∀ p ∈ P, gF p ≠ 0) ∧ (∀ p ∈ P, gF p ≠ ⊤) ∧
      (∀ p ∈ P, ∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) ∧
      haveI : NeZero (localRestrictionLevel P e) :=
        ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
      L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          (residueRestrictedIndicator n (localRestrictionLevel P e)
            (localRestrictionSet P e R))
          (algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) =
        (((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal : ℂ) *
          L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
            rationalFiniteAdeleVectorIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) := by
  obtain ⟨gF, gR, h0, ht, hloc, hFne⟩ := L.exists_localGlueRatio_family M hM P e R hP hrep
  exact ⟨gF, gR, h0, ht, hloc, hFne,
    L.finiteLocalValueDensity_localRestriction_eq_mul hn M P e R hP gF gR h0 ht hloc hFne⟩

end PositiveDefiniteIntegralLattice
