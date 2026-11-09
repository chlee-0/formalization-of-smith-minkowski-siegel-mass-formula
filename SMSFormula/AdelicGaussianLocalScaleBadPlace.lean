import SMSFormula.AdelicGaussianLocalRatioBadPlace

/-!
# The intrinsic local scale at a bad place

At a prime `p` of a bad place the local masses satisfy `gR · D_p = gF · c_p` with

`D_p = r_p · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))`,

where the block glue is taken in any covering block atlas (with the auxiliary Haars `addHaar`
on the transverse slices and the scalar line, and the unit-cube Haar on the block space):
glue masses of measurable sets agree across covering atlases.  So `D_p` is an intrinsic local
quantity, independent of the local density `c_p`.  All other inputs of the bad-place identity
(lattice atlas, positivity of the lattice glue of `ℤ_p^n`, eventual nonvanishing of full counts,
integral representation) are produced here from the carrying property and one integral orbit
point.  The stabilizer identity through carrying sets (chart data) remains supplied.
-/

noncomputable section

open MeasureTheory Filter Metric Set PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime] {N : ℕ}

local instance lsPadicMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance lsPadicBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

/-- Glue masses do not depend on the covering atlas. -/
theorem padicSquareBranchAtlasGlue_eq_of_covers (form : QuadraticForm ℚ_[prime] (Fin N → ℚ_[prime]))
    (point : ℕ → Fin N → ℚ_[prime]) (hpoint : ∀ i, form (point i) ≠ 0)
    (tH : ∀ i, Measure (form.anisotropicOrthogonal (point i))) [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {w | form w ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (point' : ℕ → Fin N → ℚ_[prime]) (hpoint' : ∀ i, form (point' i) ≠ 0)
    (tH' : ∀ i, Measure (form.anisotropicOrthogonal (point' i))) [∀ i, (tH' i).IsAddHaarMeasure]
    (hcover' : {w | form w ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point' hpoint' i)
    (νs : Measure ℚ_[prime]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[prime]))
    [νv.IsAddHaarMeasure] {value : ℚ_[prime]} (hvalue : value ≠ 0)
    {S : Set {w : Fin N → ℚ_[prime] // form w = value}} (hS : MeasurableSet S) :
    form.padicSquareBranchAtlasGlue prime point hpoint tH νs νv value S =
      form.padicSquareBranchAtlasGlue prime point' hpoint' tH' νs νv value S := by
  have hcov : ∀ (pt : ℕ → Fin N → ℚ_[prime]) (hpt : ∀ i, form (pt i) ≠ 0),
      {w | form w ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime pt hpt i →
      S ⊆ ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (pt i) (hpt i) value) := by
    intro pt hpt hc y _
    have hy : y.1 ∈ {w | form w ≠ 0} := by
      change form y.1 ≠ 0
      rw [y.2]
      exact hvalue
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hy)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [form.range_padicSquareBranchFiberMap prime (pt i) (hpt i) value]
    exact hi
  exact form.padicSquareBranchAtlasGlue_apply_eq_of_cover prime point hpoint tH point' hpoint' tH'
    νs νv value hS (hcov point hpoint hcover) (hcov point' hpoint' hcover')

end QuadraticMap

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance lsPadicMeasurableSpace' (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance lsPadicBorelSpace' (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

set_option maxHeartbeats 1000000 in
/-- The intrinsic local scale at a bad place: there is `D` with `gR · D = gF · c`, `D ∈ (0,∞)`, and
`D = r · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))` in every covering block atlas. -/
theorem exists_localScale_of_carry (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ Pr) {gF gR : ℝ≥0∞}
    (hloc : ∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF =
      (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR)
    (hM : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0)
    (hMx : algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) = (((M : ℤ) : ℤ_[p]) : ℚ_[p]))
    {O' : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p])}
    (hcarry : ∀ z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p],
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 ∈ PadicInt.restrictedIntegralVectors (e p) (R p) ↔ z ∈ O')
    (hrep : ∃ z ∈ O', ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 i ∈
      PadicInt.subring p)
    {volV volW c r : ℝ≥0∞} (hdens : volV = volW * c) (hvolW0 : volW ≠ 0) (hvolWt : volW ≠ ⊤)
    (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hstab : ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[p]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point₁ hpoint₁ i →
      ∀ Tb : Set (Fin (m + 1) → ℚ_[p]), MeasurableSet Tb →
        Tb ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z = (((M : ℤ) : ℤ_[p]) : ℚ_[p])} = Subtype.val '' O' →
        volV = r * volW * ((Measure.addHaar : Measure ℚ_[p]) (closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar p (Fin (m + 1))) (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' Tb))) :
    ∃ D : ℝ≥0∞, gR * D = gF * c ∧ D ≠ 0 ∧ D ≠ ⊤ ∧
      ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[p]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) (point₁ i) ≠ 0),
        {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point₁ hpoint₁ i →
        D = r * ((Measure.addHaar : Measure ℚ_[p]) (closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar p (Fin (m + 1))) (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall 0 1))) := by
  obtain ⟨z₀, hz₀O, hz₀⟩ := hrep
  set u := P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z₀.1 with hudef
  have hu1 : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ hz₀ i
  have hu : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') u = (((M : ℤ) : ℤ_[p]) : ℚ_[p]) := by
    rw [← hMx, hudef, ← P.blockToAmbientPadicContinuousLinearEquiv_apply,
      latticeGram_blockToAmbient L P hx p]
    exact z₀.2
  obtain ⟨point₂, hpoint₂, hcover₂⟩ := (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').exists_padicSquareBranchAtlas_cover p
    ⟨u, by rw [hu]; exact hM⟩
  have hG := padicSquareBranchAtlasGlue_integral_ne_zero_ne_top _ point₂ hpoint₂
    (fun _ ↦ Measure.addHaar) Measure.addHaar Measure.addHaar hcover₂ hM hu1 hu
  have hFne := L.eventually_fullResidueCount_primePow_ne_zero_of_eq M _ rfl _ rfl hM point₂
    hpoint₂ (fun _ ↦ Measure.addHaar) Measure.addHaar Measure.addHaar hcover₂ hG.1
  have hQz : ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z₀.1 ≠ 0 := by
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] z₀.1 ≠ 0
    rw [show (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] z₀.1 =
      algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) from z₀.2]
    exact (map_ne_zero _).mpr hx
  obtain ⟨point₁, hpoint₁, hcover₁⟩ := ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]).exists_padicSquareBranchAtlas_cover p ⟨z₀.1, hQz⟩
  have hDb := localScale_ne_zero_ne_top L P hx p point₁ hpoint₁ (fun _ ↦ Measure.addHaar) hcover₁
    point₂ hpoint₂ (fun _ ↦ Measure.addHaar) hcover₂ Measure.addHaar
    (Padic.unitHaar p (Fin (m + 1))) Measure.addHaar (value := (((M : ℤ) : ℤ_[p]) : ℚ_[p])) hM
    hG.1 hG.2 hr0 hrt
  have hkey := localMass_mul_stabilizerScale_eq_of_carry L P hx M Pr e R hPr hp hloc hFne hM point₂
      hpoint₂ (fun _ ↦ Measure.addHaar) hcover₂ point₁ hpoint₁ (fun _ ↦ Measure.addHaar) hcover₁
      Measure.addHaar (Padic.unitHaar p (Fin (m + 1))) Measure.addHaar hcarry hMx hu1 hu hdens
      (hstab point₁ hpoint₁ hcover₁) hvolW0 hvolWt
  refine ⟨_, hkey, hDb.1, hDb.2, ?_⟩
  · intro point₁' hpoint₁' hcover₁'
    have hmeas : MeasurableSet (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx p) ⁻¹' closedBall (0 : Fin n → ℚ_[p]) 1) :
        Set {z : Fin (m + 1) → ℚ_[p] // ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p]) z = (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) :=
      (((IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage
        (P.blockToAmbientPadicContinuousLinearEquiv hx p).continuous).preimage continuous_subtype_val).measurableSet
    rw [QuadraticMap.padicSquareBranchAtlasGlue_eq_of_covers p _ point₁ hpoint₁
      (fun _ ↦ Measure.addHaar) hcover₁ point₁' hpoint₁' (fun _ ↦ Measure.addHaar) hcover₁'
      Measure.addHaar (Padic.unitHaar p (Fin (m + 1))) hM hmeas]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
