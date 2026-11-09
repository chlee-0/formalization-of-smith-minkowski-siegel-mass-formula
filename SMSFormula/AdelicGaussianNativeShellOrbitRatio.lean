import SMSFormula.AdelicGaussianNativeShellCalibrationLedger

/-!
# The Riesz ratio at an arbitrary orbit set

The actual Riesz measure is `σ = r · M_native` with `r = σ(U)/M_native(U)` for the compact
open `SO`-orbit `U`.  Hence the same ratio is obtained from every set `U'` of finite positive
native mass.  For the image `e_X(O)` of a set `O` of the block shell with `0 < N(O) < ∞`,
`M_native(e_X(O)) = c_G⁻¹ · N(O)`, so

`σ(U)/M_native(U) = c_G · σ(e_X(O)) / N(O)`.

The set `O` is supplied (for instance an orbit of a central-cutoff subgroup, whose `N`-mass is
the bad-place orbit identity); no section or representative is chosen.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
open scoped ENNReal

local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The block pushforward of the image of a block-shell set is its block mass. -/
theorem blockShellMeasureOnValueFiber_image
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele)) :
    blockShellMeasureOnValueFiber L P hx (P.blockToAmbientShellHomeomorph hx RationalAdele '' O) =
      P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O := by
  letI : MeasurableSpace (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x
    RationalAdele) := borel _
  haveI : BorelSpace (L.rationalQuadraticSpaceMatrix.anisotropicRationalAmbientShell x
    RationalAdele) := ⟨rfl⟩
  unfold blockShellMeasureOnValueFiber
  rw [(P.blockToAmbientShellHomeomorph hx RationalAdele).measurableEmbedding.map_apply,
    Set.preimage_image_eq _ (P.blockToAmbientShellHomeomorph hx RationalAdele).injective]

section Ratio
variable (hn : 4 < n) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

/-- The Riesz ratio is set-independent: every set of finite positive native mass gives the same
ratio as the compact open orbit `U`. -/
theorem div_nativeShellMeasure_eq_of_ne (U' : Set (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))))
    (h0 : nativeShellMeasureOnValueFiber L P hx U' ≠ 0)
    (htop : nativeShellMeasureOnValueFiber L P hx U' ≠ ⊤) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    σ U' / M U' = σ U / M U := by
  intro a σ M U
  have hσ : σ = (σ U / M U) • M :=
    gaussianFiberMeasure_eq_smul_nativeShellMeasure L P hx hn hb x₀ K hc ho
  conv_lhs => rw [hσ]
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_cancel_right h0 htop]

/-- The Riesz ratio at a block-shell set: for `O` in the block shell with `0 < N(O) < ∞`,
`σ(U)/M_native(U) = c_G · σ(e_X(O)) / N(O)`. -/
theorem div_nativeShellMeasure_eq_scalar_mul_div_blockImage
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele))
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ ⊤) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    σ U / M U =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        (σ (P.blockToAmbientShellHomeomorph hx RationalAdele '' O) /
          P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O) := by
  intro a σ M U
  have hc0 : (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx).ne'
  have hct : (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hM : M (P.blockToAmbientShellHomeomorph hx RationalAdele '' O) =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞)⁻¹ *
        P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O := by
    rw [nativeShellMeasureOnValueFiber_eq_inv_mul_block, blockShellMeasureOnValueFiber_image]
  have hM0 : M (P.blockToAmbientShellHomeomorph hx RationalAdele '' O) ≠ 0 := by
    rw [hM]; exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hct) h0
  have hMtop : M (P.blockToAmbientShellHomeomorph hx RationalAdele '' O) ≠ ⊤ := by
    rw [hM]; exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) htop
  rw [← div_nativeShellMeasure_eq_of_ne L P hx hn hb x₀ K hc ho _ hM0 hMtop,
    div_nativeShellMeasure_eq_scalar_mul_div_block, blockShellMeasureOnValueFiber_image]

end Ratio
end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
